{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Haddock.Backends.Hyperlinker.HieAst (validAst, enrichHie, hieFromTypechecked) where

import GHC hiding (exprType, Token)
import Outputable (ppr, showSDocUnsafe)
import Bag (bagToList)
import Var
import ConLike (conLikeName)
import TcHsSyn (hsPatType)
import MonadUtils
import Desugar (deSugarExpr)
import CoreUtils (exprType)
import SrcLoc (containsSpan, srcSpanStartCol, srcSpanStartLine, srcSpanEndCol, srcSpanEndLine, srcSpanFile, mkRealSrcSpan, mkRealSrcLoc)

import Haddock.Backends.Hyperlinker.Types

import Control.Applicative
import Prelude hiding (span)

astSpan :: HieAST a -> Span
astSpan (Leaf x) = htkSpan x
astSpan (Node _ sp _) = sp

validAst :: HieAST a -> Bool
validAst (Leaf _ ) = True
validAst (Node _ span children) = all validAst children
                               && all ((span `containsSpan`) . astSpan) children
                               && astSorted children
  where astSorted [] = True
        astSorted [x] = True
        astSorted (x:y:xs) = astSpan x `leftOf` astSpan y && astSorted (y:xs)

combineNodeInfo :: NodeInfo a -> NodeInfo a -> NodeInfo a
combineNodeInfo (NodeInfo as ta) (NodeInfo bs tb) = NodeInfo (as ++ bs) (ta <|> tb)

-- | One must contain the other. Leaf nodes cannot contain anything
combineAst :: HieAST a -> HieAST a -> HieAST a
combineAst (Leaf (HieToken asp aInf aDet)) (Leaf (HieToken bsp bInf bDet))
  | asp == bsp = Leaf $ HieToken bsp (aInf <|> bInf) (aDet <|> bDet)
  | otherwise = error $ "tried to combine leafs with differing spans" ++ show asp ++ show bsp
-- ^ Since one must contain the other, and leaf nodes cannot contain anything, we assume they are the same token
combineAst a b@(Leaf _) = combineAst b a
combineAst a@(Node aInf aSpn xs) b@(Node bInf bSpn ys)
  | aSpn == bSpn = Node (combineNodeInfo aInf bInf) aSpn (mergeAsts xs ys)
  | aSpn `containsSpan` bSpn = combineAst b a
combineAst a (Node xs span children) = Node xs span (insertAst a children) -- a is a Leaf node or is contained in span

-- | Insert an AST in a sorted list of disjoint Asts
insertAst :: HieAST a -> [HieAST a] -> [HieAST a]
insertAst x xs = mergeAsts [x] xs

-- Merge two sorted, disjoint lists of ASTs, combining when necessary
mergeAsts :: [HieAST a] -> [HieAST a] -> [HieAST a]
mergeAsts xs [] = xs
mergeAsts [] ys = ys
mergeAsts xs@(a:as) ys@(b:bs)
  | astSpan a `containsSpan` astSpan b = mergeAsts (combineAst a b : as) bs
  | astSpan b `containsSpan` astSpan a = mergeAsts as (combineAst a b : bs)
  | astSpan a `rightOf` astSpan b = b : mergeAsts xs bs
  | astSpan a `leftOf`  astSpan b = a : mergeAsts as ys
  | otherwise = error $ "mergeAsts: Spans overlapping "

rightOf :: Span -> Span -> Bool
rightOf s1 s2
  = (srcSpanStartLine s1, srcSpanStartCol s1)
       >= (srcSpanEndLine s2, srcSpanEndCol s2)
    && (srcSpanFile s1 == srcSpanFile s2)

leftOf :: Span -> Span -> Bool
leftOf s1 s2
  = (srcSpanEndLine s1, srcSpanEndCol s1)
       <= (srcSpanStartLine s2, srcSpanStartCol s2)
    && (srcSpanFile s1 == srcSpanFile s2)

-- | combines and sorts ASTs using a merge sort
mergeSortAsts :: [HieAST a] -> [HieAST a]
mergeSortAsts = go . map pure
  where
    go :: [[HieAST a]] -> [HieAST a]
    go [] = []
    go [xs] = xs
    go xss = go (mergePairs xss)
    mergePairs :: [[HieAST a]] -> [[HieAST a]]
    mergePairs [] = []
    mergePairs [xs] = [xs]
    mergePairs (xs:ys:xss) = mergeAsts xs ys : mergePairs xss

simpleNodeInfo :: String -> String -> NodeInfo a
simpleNodeInfo cons typ = NodeInfo [(cons, typ)] Nothing

enrichHie :: GhcMonad m => TypecheckedSource -> RenamedSource -> [Token] -> m (HieAST Type)
enrichHie ts (hsGrp, _, _, _) toks = do
    liftIO $ putStrLn $ showSDocUnsafe $ ppr ts
    tasts <- concatMapM toHie $ bagToList ts
    rasts <- toHie $ hs_valds hsGrp
    return $ Node (NodeInfo [] Nothing) spanFile (mergeSortAsts $ tasts ++ rasts ++ (map toHieToken toks))
  where 
    spanFile = mkRealSrcSpan (mkRealSrcLoc "" 1 1) (mkRealSrcLoc "" 1 1)

    toHieToken (Token inf _ span) = Leaf (HieToken span (Just inf) Nothing)

concatM :: Monad m => [m [a]] -> m [a]
concatM xs = concat <$> sequence xs

makeNode :: String -> String -> Span -> HieAST a
makeNode cons typ spn = Node (simpleNodeInfo cons typ) spn []

makeTypeNode :: String -> String -> Span -> Type -> HieAST Type
makeTypeNode cons typ spn etyp = Node (NodeInfo [(cons,typ)] (Just etyp)) spn []

class ToHie a where
  toHie :: GhcMonad m => a -> m [HieAST Type]

class HasType a where
  getTypeNode :: GhcMonad m => a -> String -> String -> Span -> m [HieAST Type]

class HieVar a where
  varBind :: Located a -> [HieAST Type]
  varUse  :: Located a -> [HieAST Type]

instance HasType (LHsBind GhcRn) where
  getTypeNode _ cons typ spn = pure [makeNode cons typ spn]

instance HasType (LHsBind GhcTc) where
  getTypeNode (L _ bind) cons typ spn = case bind of
      FunBind name _ _ _ _ -> pure [makeTypeNode cons typ spn (varType $ unLoc name)]
      _ -> pure $ [makeNode cons typ spn]

instance HasType (LPat GhcRn) where
  getTypeNode _ cons typ spn = pure [makeNode cons typ spn]

instance HasType (LPat GhcTc) where
  getTypeNode (L _ opat) cons typ spn = 
    pure [makeTypeNode cons typ spn (hsPatType opat)]

instance HasType (LHsExpr GhcRn) where
  getTypeNode _ cons typ spn = pure [makeNode cons typ spn]

instance HasType (LHsExpr GhcTc) where
  getTypeNode e cons typ spn = do
    hs_env <- getSession
    (_,mbe) <- liftIO $ deSugarExpr hs_env e
    pure [Node (NodeInfo [(cons,typ)] (exprType <$> mbe)) spn []]

instance HieVar PlaceHolder where
  varBind _ = []
  varUse _ = []
instance HieVar Var where
  varBind _ = []
  varUse _ = []
  
instance HieVar Name where
  varBind (L (RealSrcSpan span) name)
    | isExternalName name = [Leaf $ HieToken span Nothing (Just $ RtkDecl name)]
    | otherwise       = [Leaf $ HieToken span Nothing (Just $ RtkBind name)]
  varBind _ = []
  varUse (L (RealSrcSpan span) name) = 
    [Leaf $ HieToken span Nothing (Just $ RtkVar name)]
  varUse _ = []

instance ( HieVar (IdP a)
         , ToHie (LPat a)
         , ToHie (LHsExpr a)
         , ToHie (GRHSs a (LHsExpr a))
         , ToHie (MatchGroup a (LHsExpr a))
         , HasType (LHsBind a)
         ) => ToHie (LHsBind a) where
  toHie b@(L (RealSrcSpan span) bind) = concatM $ case bind of 
      FunBind name matches _ _ _ ->
        [ mkTypeNode "FunBind" 
        , pure $ varBind name
        , toHie matches
        ]
      PatBind lhs rhs _ _ _ ->
        [ mkNode "PatBind" 
        , toHie lhs
        , toHie rhs
        ]
      VarBind _ expr _ ->
        [ mkNode "VarBind" 
        , toHie expr
        ]
      AbsBinds _ _ _ _ binds _ ->
        [ mkNode "AbsBinds" 
        , concatMapM toHie $ bagToList binds
        ]
      _ -> []
    where mkNode cons = pure [makeNode cons "HsBindLR" span]
          mkTypeNode cons = getTypeNode b cons "HsBindLR" span
  toHie _ = pure []

instance ( ToHie (LMatch a body)
         , ToHie body
         ) => ToHie (MatchGroup a body) where
  toHie (MG (L (RealSrcSpan span) alts) _ _ _) = concatM
    [ pure [Node (simpleNodeInfo "Alts" "MatchGroup") span []]
    , concatMapM toHie alts
    ]
  toHie _ = pure []

instance ( ToHie body
         , ToHie (LPat a)
         , ToHie (GRHSs a body)
         ) => ToHie (LMatch a body) where
  toHie (L (RealSrcSpan span) (Match _ pats grhss)) = concatM
    [ pure [Node (simpleNodeInfo "Match" "Match") span []] 
    , concatMapM toHie pats
    , toHie grhss
    ]
  toHie _ = pure []

instance ( HieVar (IdP a)
         , ToHie (HsRecFields a (LPat a))
         , ToHie (LHsExpr a)
         , HasType (LPat a)
         ) => ToHie (LPat a) where
  toHie lpat@(L (RealSrcSpan pspan) opat) = concatM $ case opat of
      WildPat _ ->
        [ mkNode "WildPat"
        ]
      VarPat lname ->
        [ mkNode "VarPat" 
        , pure $ varBind lname
        ]
      LazyPat p ->
        [ mkNode "LazyPat" 
        , toHie p
        ]
      AsPat lname pat ->
        [ mkNode "AsPat" 
        , pure $ varBind lname
        , toHie pat
        ]
      ParPat pat ->
        [ mkNode "ParPat" 
        , toHie pat
        ]
      BangPat pat ->
        [ mkNode "BangPat" 
        , toHie pat
        ]
      ListPat pats _ _ ->
        [ mkNode "ListPat" 
        , concatMapM toHie pats
        ]
      TuplePat pats _ _ ->
        [ mkNode "TuplePat" 
        , concatMapM toHie pats
        ]
      SumPat pat _ _ _ ->
        [ mkNode "SumPat" 
        , toHie pat
        ]
      PArrPat pats _ ->
        [ mkNode "PArrPat" 
        , concatMapM toHie pats
        ]
      ConPatIn c dets ->
        [ mkNode "ConPatIn" 
        , pure $ varUse c
        , toHie dets
        ]
      ConPatOut con _ _ _ _ dets _ ->
        [ mkNode "ConPatIn" 
        , pure $ varUse $ fmap conLikeName con
        , toHie dets
        ]
      ViewPat expr pat _ ->
        [ mkNode "ViewPat" 
        , toHie expr 
        , toHie pat
        ]
      LitPat _ ->
        [ mkNode "LitPat" 
        ]
      NPat _ _ _ _ ->
        [ mkNode "NPat"
        ]
      NPlusKPat n _ _ _ _ _ ->
        [ mkNode "NPlusKPat" 
        , pure $ varBind n
        ]
      SigPatIn pat sig ->
        [ mkNode "SigPatIn"
        , toHie pat
        ]
      SigPatOut pat _ ->
        [ mkNode "SigPatOut" 
        , toHie pat
        ]
      CoPat _ _ _ ->
        [ mkNode "CoPat"
        ]
      _ -> []
    where mkNode cons = getTypeNode lpat cons "Pat" pspan
  toHie _ = pure []

instance ( ToHie body
         , ToHie (LGRHS a body)
         , ToHie (LHsLocalBinds a)
         ) => ToHie (GRHSs a body) where
  toHie (GRHSs grhss binds) = concatM
    [ concatMapM toHie grhss 
    , toHie binds
    ]

instance ( ToHie body
         , ToHie (GuardLStmt a)
         ) => ToHie (LGRHS a body) where
  toHie (L (RealSrcSpan span) (GRHS guards body)) = concatM
    [ pure [Node (simpleNodeInfo "GRHS" "GRHS") span []]
    , concatMapM toHie guards 
    , toHie body
    ]
  toHie _ = pure []

instance ( HieVar (IdP a)
         , HasType (LPat a)
         , HasType (LHsExpr a)
         , ToHie (LHsTupArg a)
         , ToHie (HsRecordBinds a)
         , ToHie (Located (AmbiguousFieldOcc a))
         , ToHie (ArithSeqInfo a)
         , ToHie (LHsCmdTop a)
         , ToHie (HsRecFields a (LPat a))
         , ToHie (GuardLStmt a)
         , ToHie (LHsLocalBinds a)
         ) => ToHie (LHsExpr a) where
  toHie e@(L mspan oexpr) = concatM $ case oexpr of
      HsVar v -> 
        [ mkNode "HsVar" 
        , pure $ varUse v
        ]
      HsConLikeOut con ->
        [ mkNode "ConLikeOut"
        , pure $ varUse $ L mspan $ conLikeName con
        ]
      HsRecFld fld ->
        [ mkNode "HsRecFld"
        , toHie (L mspan fld)
        ]
      HsOverLabel _ _ ->
        [ mkNode "HsOverLable"
        ]
      HsOverLit _ ->
        [ mkNode "HsOverLit"
        ]
      HsLit _ ->
        [ mkNode "HsLit"
        ]
      HsLam mg -> 
        [ mkNode "HsLam" 
        , toHie mg
        ]
      HsLamCase mg -> 
        [ mkNode "HsLamCase" 
        , toHie mg
        ]
      HsApp a b -> 
        [ mkNode "HsApp" 
        , toHie a 
        , toHie b
        ]
      HsAppType expr sig ->
        [ mkNode "HsAppType"
        , toHie expr
        ]
      HsAppTypeOut expr _ -> 
        [ mkNode "HsAppTypeOut" 
        , toHie expr
        ]
      OpApp a b _ c -> 
        [ mkNode "OpApp" 
        , toHie a 
        , toHie b 
        , toHie c
        ]
      NegApp a _ -> 
        [ mkNode "NegApp" 
        , toHie a
        ]
      HsPar a -> 
        [ mkNode "HsPar" 
        , toHie a
        ]
      SectionL a b -> 
        [ mkNode "SectionL" 
        , toHie a 
        , toHie b
        ]
      SectionR a b -> 
        [ mkNode "SectionR" 
        , toHie a 
        , toHie b
        ]
      ExplicitTuple args _ -> 
        [ mkNode "ExplicitTyple" 
        , concatMapM toHie args
        ]
      ExplicitSum _ _ expr _ -> 
        [ mkNode "ExplicitSum" 
        , toHie expr
        ]
      HsCase expr matches -> 
        [ mkNode "HsCase" 
        , toHie expr 
        , toHie matches
        ]
      HsIf _ a b c -> 
        [ mkNode "HsIf" 
        , toHie a 
        , toHie b 
        , toHie c
        ]
      HsMultiIf _ grhss -> 
        [ mkNode "HsMultiIf" 
        , concatMapM toHie grhss
        ]
      HsLet binds expr -> 
        [ mkNode "HsLet" 
        , toHie binds 
        , toHie expr
        ]
      HsDo _ (L _ stmts) _ -> 
        [ mkNode "HsDo" 
        , concatMapM toHie stmts
        ]
      ExplicitList _ _ exprs -> 
        [ mkNode "ExplicitList" 
        , concatMapM toHie exprs
        ]
      ExplicitPArr _ exprs -> 
        [ mkNode "ExplicitPArr" 
        , concatMapM toHie exprs
        ]
      RecordCon name _ _ binds -> 
        [ mkNode "RecordCon" 
        , pure $ varUse name
        , toHie binds
        ]
      RecordUpd expr upds _ _ _ _ -> 
        [ mkNode "RecordUpd" 
        , toHie expr 
        , concatMapM toHie upds
        ]
      ExprWithTySig expr sig ->
        [
        ]
      ExprWithTySigOut expr _ -> 
        [ mkNode "ExprWithTySigOut" 
        , toHie expr 
        ]
      ArithSeq _ _ info -> 
        [ mkNode "ArithSeq" 
        , toHie info
        ]
      PArrSeq _ info -> 
        [ mkNode "PArrSeq" 
        , toHie info
        ]
      HsSCC _ _ expr -> 
        [ mkNode "HsSCC" 
        , toHie expr
        ]
      HsCoreAnn _ _ expr -> 
        [ mkNode "HsCoreAnn" 
        , toHie expr
        ]
      HsProc pat cmdtop -> 
        [ mkNode "HsProc" 
        , toHie pat 
        , toHie cmdtop
        ]
      HsStatic _ expr -> 
        [ mkNode "HsStatic" 
        , toHie expr
        ]
      HsArrApp a b _ _ _ ->
        [ mkNode "HsArrApp"
        , toHie a
        , toHie b
        ]
      HsArrForm expr _ cmds ->
        [ mkNode "HsArrForm"
        , toHie expr
        , concatMapM toHie cmds
        ]
      HsTick _ expr -> 
        [ mkNode "HsTick" 
        , toHie expr
        ]
      HsBinTick _ _ expr -> 
        [ mkNode "HsBinTick" 
        , toHie expr
        ]
      HsTickPragma _ _ _ expr -> 
        [ mkNode "HsTickPragma" 
        , toHie expr
        ]
      HsWrap _ _ ->
        [ mkNode "HsWrap"
        ]
      _ -> []
    where 
      mkNode cons = case mspan of
        RealSrcSpan span -> getTypeNode e cons "HsExpr" span
        _ -> return []

instance ( HieVar (IdP a)
         , HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , HasType (LPat a)
         , HasType (LHsExpr a)
         , HasType (LHsBind a)
         ) => ToHie (LHsTupArg a) where
  toHie (L (RealSrcSpan span) arg) = concatM $ case arg of
    Present expr -> 
      [ mkNode "Present" 
      , toHie expr
      ]
    Missing _ -> [ mkNode "Missing" ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsTupArg") span []]
  toHie _ = pure []

instance ( HieVar (IdP a)
         , HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , HasType (LPat a)
         , HasType (LHsExpr a)
         , HasType (LHsBind a)
         , ToHie body
         ) => ToHie (LStmt a body) where
  toHie (L (RealSrcSpan span) stmt) = concatM $ case stmt of
      LastStmt body _ _ -> 
        [ mkNode "LastStmt" 
        , toHie body
        ]
      BindStmt pat body _ _ _ -> 
        [ mkNode "BindStmt" 
        , toHie pat 
        , toHie body
        ]
      ApplicativeStmt stmts _ _ -> 
        [ mkNode "ApplicativeStmt" 
        , concatMapM (toHie . snd) stmts
        ]
      BodyStmt body _ _ _ -> 
        [ mkNode "BodyStmt" 
        , toHie body
        ]
      LetStmt binds -> 
        [ mkNode "LetStmt" 
        , toHie binds
        ]
      ParStmt parstmts _ _ _ -> 
        [ mkNode "ParStmt" 
        , concatMapM (\(ParStmtBlock stmts _ _) -> concatMapM toHie stmts) parstmts
        ]
      _ -> []
    where mkNode cons = pure [Node (simpleNodeInfo cons "StmtLR") span []]
  toHie _ = pure []

instance ( HieVar (IdP a)
         , HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , HasType (LPat a)
         , HasType (LHsBind a)
         , HasType (LHsExpr a)
         ) => ToHie (LHsLocalBinds a) where
  toHie (L (RealSrcSpan span) binds) = concatM $ case binds of
      EmptyLocalBinds -> [mkNode "EmptyLocalBinds"]
      HsIPBinds _ -> [mkNode "HsIPBinds"]
      HsValBinds valBinds ->
        [ mkNode "HsValBinds" 
        , toHie valBinds
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsLocalBindsLR") span []]
  toHie _ = pure []

instance ( HieVar (IdP a)
         , HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , HasType (LHsBind a)
         , HasType (LPat a)
         , HasType (LHsExpr a)
         ) => ToHie (HsValBindsLR a a) where
  toHie (ValBindsIn binds _) = concatMapM toHie $ bagToList binds
  toHie (ValBindsOut binds _) = concatMapM toHie $ concatMap (bagToList . snd) binds

instance ( HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , ToHie arg
         ) => ToHie (HsRecFields a arg) where
  toHie (HsRecFields fields _) = concatMapM toHie fields

instance (ToHie (Located label), ToHie arg) => ToHie (LHsRecField' label arg) where
  toHie (L (RealSrcSpan span) (HsRecField label expr _)) = concatM
      [ pure $ [Node (simpleNodeInfo "HsRecField" "HsRecField'") span []] 
      , toHie label
      , toHie expr
      ]
  toHie _ = pure []
  
instance ( HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         ) => ToHie (LFieldOcc a) where
  toHie (L nspan (FieldOcc _ name)) = pure $ varUse $ L nspan name 

instance ( HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         ) => ToHie (Located (AmbiguousFieldOcc a)) where
  toHie (L nspan (Unambiguous _ name)) = pure $ varUse $ L nspan name
  toHie (L nspan (Ambiguous _ name)) = pure $ varUse $ L nspan name

instance ( HieVar (IdP a)
         , HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , HasType (LPat a)
         , HasType (LHsBind a)
         , HasType (LHsExpr a)
         ) => ToHie (ApplicativeArg a a) where
  toHie (ApplicativeArgOne pat expr _) = concatM
    [ toHie pat
    , toHie expr
    ]
  toHie (ApplicativeArgMany stmts _ pat) = concatM
    [ concatMapM toHie stmts
    , toHie pat
    ]

instance (ToHie arg, ToHie rec) => ToHie (HsConDetails arg rec) where
  toHie (PrefixCon args) = concatMapM toHie args
  toHie (RecCon rec) = toHie rec
  toHie (InfixCon a b) = concatM [ toHie a, toHie b]

instance ( HieVar (IdP a)
         , HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , HasType (LPat a)
         , HasType (LHsBind a)
         , HasType (LHsExpr a)
         ) => ToHie (LHsCmdTop a) where
  toHie (L (RealSrcSpan span) (HsCmdTop cmd _ _ _)) = concatM
    [ pure [Node (simpleNodeInfo "HsCmdTop" "HsCmdTop") span []]
    , toHie cmd
    ]
  toHie _ = pure []

instance ( HieVar (IdP a)
         , HieVar (PostRn a (IdP a))
         , HieVar (PostTc a (IdP a))
         , HasType (LPat a)
         , HasType (LHsBind a)
         , HasType (LHsExpr a)
         ) => ToHie (LHsCmd a) where
  toHie (L (RealSrcSpan span) cmd) = concatM $ case cmd of
      HsCmdArrApp a b _ _ _ -> 
        [ mkNode "HsCmdArrApp"
        , toHie a
        , toHie b
        ]
      HsCmdArrForm a _ _ cmdtops ->
        [ mkNode "HsCmdArrForm"
        , toHie a
        , concatMapM toHie cmdtops
        ]
      HsCmdApp a b -> 
        [ mkNode "HsCmdApp"
        , toHie a
        , toHie b
        ]
      HsCmdLam mg ->
        [ mkNode "HsCmdLam"
        , toHie mg
        ]
      HsCmdPar a ->
        [ mkNode "HsCmdPar"
        , toHie a
        ]
      HsCmdCase expr alts ->
        [ mkNode "HsCmdCase"
        , toHie expr
        , toHie alts
        ]
      HsCmdIf _ a b c ->
        [ mkNode "HsCmdIf"
        , toHie a
        , toHie b
        , toHie c
        ]
      HsCmdLet binds cmd' ->
        [ mkNode "HsCmdLet"
        , toHie binds
        , toHie cmd'
        ]
      HsCmdDo (L _ stmts) _ ->
        [ mkNode "HsCmdDo"
        , concatMapM toHie stmts
        ]
      _ -> []
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsCmd") span []]
  toHie _ = pure []

instance ToHie (ArithSeqInfo a) where
  toHie _ = pure []

hieFromTypechecked :: forall m. GhcMonad m => TypecheckedSource -> m [HieAST Type]
hieFromTypechecked = go 
  where
    go binds = concatMapM toHie $ bagToList binds
