{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Haddock.Backends.Hyperlinker.HieAst (validAst, enrichHie, hieFromTypechecked) where

import GHC hiding (exprType, Token)
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
combineAst (Leaf (HieToken sp aInf aDet aTyp)) (Leaf (HieToken _ bInf bDet bTyp)) = 
  Leaf $ HieToken sp (aInf <|> bInf) (aDet <|> bDet) (aTyp <|> bTyp) 
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

enrichHie :: forall a. RenamedSource -> [Token] -> HieAST a
enrichHie src toks = Node (NodeInfo [] Nothing) spanFile (go src)
  where 
    spanFile = mkRealSrcSpan (mkRealSrcLoc "" 1 1) (mkRealSrcLoc "" 1 1)

    toHieToken (Token inf _ span) = Leaf (HieToken span (Just inf) Nothing Nothing)

    varDecl (L (RealSrcSpan span) name) = [Leaf $ HieToken span Nothing (Just $ RtkDecl name) Nothing]
    varDecl _ = []

    varBind (L (RealSrcSpan span) name) = [Leaf $ HieToken span Nothing (Just $ RtkBind name) Nothing]
    varBind _ = []
    
    varUse (L (RealSrcSpan span) name) = [Leaf $ HieToken span Nothing (Just $ RtkVar name) Nothing]
    varUse _ = []

    go :: RenamedSource -> [HieAST a]
    go (hsGrp, _, _, _) = mergeSortAsts $ (goGroup hsGrp) ++ (map toHieToken toks)

    goGroup hsGrp = goTopVals (hs_valds hsGrp)

    goTopVals = goVals varDecl
    goLocalVals = goVals varBind
    
    goVals var (ValBindsIn binds sigs) = (concatMap (goBind var) $ bagToList binds) 
    goVals var (ValBindsOut binds sigs) = (concatMap (goBind var) $ concatMap (bagToList . snd) binds)

    goBind var (L (RealSrcSpan span) bind) =  case bind of 
        FunBind name matches _ _ _ -> (mkNode "FunBind") : (var name) ++ (goMatches matches)
        PatBind lhs rhs _ _ _ -> (mkNode "PatBind") : (goPat' var lhs) ++ (goGRHSs rhs)
        VarBind _ expr _ -> (mkNode "VarBind") : (goExpr expr)
        AbsBinds _ _ _ _ binds _ -> (mkNode "AbsBinds") : (concatMap (goBind var) $ bagToList binds)
        _ -> []
      where mkNode cons = Node (simpleNodeInfo cons "HsBindLR") span []
    goBind _ _ = []

    goMatches (MG (L (RealSrcSpan span) alts) _ _ _) = 
      Node (simpleNodeInfo "Alts" "MatchGroup") span [] : (concatMap goAlts alts)
    goMatches _ = []

    goAlts (L (RealSrcSpan span) (Match _ pats grhss)) = 
      (Node (simpleNodeInfo "Match" "Match") span []) : (concatMap goPat pats) ++ (goGRHSs grhss)
    goAlts _ = []
    
    goPat = goPat' varBind

    goPat' var (L (RealSrcSpan pspan) opat) = case opat of
        VarPat lname -> mkNode "VarPat" : var lname
        LazyPat p -> mkNode "LazyPat" : goPat p
        AsPat lname lpat -> mkNode "AsPat" : (var lname) ++ (goPat' var lpat)
        ParPat pat -> mkNode "ParPat" : goPat' var pat
        BangPat pat -> mkNode "BangPat" : goPat' var pat
        ListPat pats _ _ -> mkNode "ListPat" : concatMap (goPat' var) pats
        TuplePat pats _ _ -> mkNode "TuplePat" : concatMap (goPat' var) pats
        SumPat pat _ _ _ -> mkNode "SumPat" : goPat' var pat
        PArrPat pats _ -> mkNode "PArrPat" : concatMap (goPat' var) pats
        ConPatIn c dets -> mkNode "ConPatIn" : (varUse c) ++ goConDets dets
        ViewPat expr pat _ -> mkNode "ViewPat" : (goExpr expr) ++ (goPat' var pat)
        SplicePat splice -> mkNode "SplicePat" : goSplice splice
        LitPat _ -> mkNode "LitPat" : []
        NPat _ _ _ _ -> mkNode "NPat" : []
        NPlusKPat lname _ _ _ _ _ -> mkNode "NPlusKPat" : var lname
        SigPatIn pat typ -> mkNode "SigPatIn" : (goPat' var pat) ++ (goSigWcType typ)
        _ -> []
      where mkNode cons = Node (simpleNodeInfo cons "Pat") pspan []
    goPat' _ _ = []

    goGRHSs (GRHSs grhss binds) = (concatMap goGRHS grhss) ++ (goLocalBinds binds)

    goGRHS (L (RealSrcSpan span) (GRHS guards body)) = 
      Node (simpleNodeInfo "GRHS" "GRHS") span [] : (concatMap goStmt guards) ++ (goExpr body)
    goGRHS _ = []

    goExpr (L (RealSrcSpan span) oexpr) = case oexpr of
        HsVar v -> mkNode "HsVar" : varUse v
        HsLam mg -> mkNode "HsLam" : goMatches mg
        HsLamCase mg -> mkNode "HsLamCase" : goMatches mg
        HsApp a b -> mkNode "HsApp" : (goExpr a) ++ (goExpr b)
        HsAppType expr typ -> mkNode "HsAppType" : (goExpr expr) ++ (goWcType typ)
        HsAppTypeOut expr typ -> mkNode "HsAppType" : (goExpr expr) ++ (goWcType typ)
        OpApp a b _ c -> mkNode "OpApp" : (goExpr a) ++ (goExpr b) ++ (goExpr c)
        NegApp a _ -> mkNode "NegApp" : goExpr a
        HsPar a -> mkNode "HsPar" : goExpr a
        SectionL a b -> mkNode "SectionL" : (goExpr a) ++ (goExpr b)
        SectionR a b -> mkNode "SectionR" : (goExpr a) ++ (goExpr b)
        ExplicitTuple args _ -> mkNode "ExplicitTyple" : concatMap goTupArg args
        ExplicitSum _ _ expr _ -> mkNode "ExplicitSum" : goExpr expr
        HsCase expr matches -> mkNode "HsCase" : (goExpr expr) ++ (goMatches matches)
        HsIf _ a b c -> mkNode "HsIf" : (goExpr a) ++ (goExpr b) ++ (goExpr c)
        HsMultiIf _ grhss -> mkNode "HsMultiIf" : concatMap goGRHS grhss
        HsLet binds expr -> mkNode "HsLet" : (goLocalBinds binds) ++ (goExpr expr)
        HsDo _ (L _ stmts) _ -> 
          mkNode "HsDo" : concatMap goStmt stmts
        ExplicitList _ _ exprs -> mkNode "ExplicitList" : concatMap goExpr exprs
        ExplicitPArr _ exprs -> mkNode "ExplicitPArr" : concatMap goExpr exprs
        RecordCon name _ _ binds -> mkNode "RecordCon" : (varUse name) ++ (goRecordBinds binds)
        RecordUpd expr upds _ _ _ _ -> mkNode "RecordUpd" : (goExpr expr) ++ (goRecordUpds upds)
        ExprWithTySig expr sig -> mkNode "ExprWithTySig" : (goExpr expr) ++ (goSigWcType sig)
        ExprWithTySigOut expr sig -> mkNode "ExprWithTySigOut" : (goExpr expr) ++ (goSigWcType sig)
        ArithSeq _ _ info -> mkNode "ArithSeq" : goArithSeqInfo info
        PArrSeq _ info -> mkNode "PArrSeq" : goArithSeqInfo info
        HsSCC _ _ expr -> mkNode "HsSCC" : goExpr expr
        HsCoreAnn _ _ expr -> mkNode "HsCoreAnn" : goExpr expr
        HsProc pat cmdtop -> mkNode "HsProc" : (goPat pat) ++ (goCmdTop cmdtop)
        HsStatic _ expr -> mkNode "HsStatic" : goExpr expr
        HsArrApp a b _ _ _ -> mkNode "HsArrApp" : (goExpr a) ++ (goExpr b)
        HsArrForm expr _ cmdtops -> mkNode "HsArrForm" : (goExpr expr) ++ (concatMap goCmdTop cmdtops)
        HsTick _ expr -> mkNode "HsTick" : goExpr expr
        HsBinTick _ _ expr -> mkNode "HsBinTick" : goExpr expr
        HsTickPragma _ _ _ expr -> mkNode "HsTickPragma" : goExpr expr
        EAsPat name expr -> mkNode "EAsPat" : (varUse name) ++ (goExpr expr)
        EViewPat a b -> mkNode "EViewPat" : (goExpr a) ++ (goExpr b)
        ELazyPat expr -> mkNode "ELazyPat" : goExpr expr
        _ -> []
      where mkNode cons = Node (simpleNodeInfo cons "HsExpr") span []
    goExpr _ = []

    goTupArg (L (RealSrcSpan span) arg) = case arg of
      Present expr -> mkNode "Present" : goExpr expr
      Missing _ -> mkNode "Missing" : []
      where mkNode cons = Node (simpleNodeInfo cons "HsTupArg") span []
    goTupArg _ = []

    goStmt (L (RealSrcSpan span) stmt) = case stmt of
        LastStmt body _ _ -> mkNode "LastStmt" : goExpr body
        BindStmt pat body _ _ _ -> mkNode "BindStmt" : (goPat pat) ++ (goExpr body)
        ApplicativeStmt stmts _ _ -> mkNode "ApplicativeStmt" : concatMap (goApplicativeArg . snd) stmts
        BodyStmt body _ _ _ -> mkNode "BodyStmt" : goExpr body
        LetStmt binds -> mkNode "LetStmt" : goLocalBinds binds
        ParStmt parstmts _ _ _ -> 
          mkNode "ParStmt" : concatMap (\(ParStmtBlock stmts _ _) -> concatMap goStmt stmts) parstmts
        _ -> []
      where mkNode cons = Node (simpleNodeInfo cons "StmtLR") span []
    goStmt _ = []

    goLocalBinds (L (RealSrcSpan span) binds) = case binds of
        EmptyLocalBinds -> [mkNode "EmptyLocalBinds"]
        HsIPBinds _ -> [mkNode "HsIPBinds"]
        HsValBinds valBinds -> mkNode "HsValBinds" : goLocalVals valBinds
      where mkNode cons = Node (simpleNodeInfo cons "HsLocalBindsLR") span []
    goLocalBinds _ = []

    goRecordBinds (HsRecFields fields _) = concatMap goRecordField fields

    goRecordField (L (RealSrcSpan span) (HsRecField label expr _)) = case label of
      L nspan (FieldOcc _ name) -> 
        Node (simpleNodeInfo "HsRecField" "HsRecField'") span [] : (varUse $ L nspan name) ++ (goExpr expr)
    goRecordField _ = []

    goRecordUpds upds = concatMap goRecordUpdField upds

    goRecordUpdField (L (RealSrcSpan span) (HsRecField label expr _)) = case label of
      L nspan (Unambiguous _ name) -> 
        Node (simpleNodeInfo "HsRecField" "HsRecField'") span [] : (varUse $ L nspan name) ++ (goExpr expr)
      _ -> []
    goRecordUpdField _ = []

    goSigWcType _ = []

    goWcType _ = []

    goApplicativeArg _ = []

    goConDets _ = []

    goSplice _ = []

    goCmdTop _ = []

    goArithSeqInfo _ = []


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
  varBind :: Monad m => Located a -> m [HieAST Type]
  varUse  :: Monad m => Located a -> m [HieAST Type]

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
  
instance HieVar Var where
  varBind (L (RealSrcSpan span) name)
    | isGlobalId name = pure [Leaf $ HieToken span Nothing (Just $ RtkDecl $ varName name) (Just $ varType name)]
    | otherwise       = pure [Leaf $ HieToken span Nothing (Just $ RtkBind $ varName name) (Just $ varType name)]
  varBind _ = pure []
  varUse (L (RealSrcSpan span) name) = 
    pure [Leaf $ HieToken span Nothing (Just $ RtkVar $ varName name) (Just $ varType name)]
  varUse _ = pure []
  
instance HieVar Name where
  varBind (L (RealSrcSpan span) name)
    | isExternalName name = pure [Leaf $ HieToken span Nothing (Just $ RtkDecl name) Nothing]
    | otherwise       = pure [Leaf $ HieToken span Nothing (Just $ RtkBind name) Nothing]
  varBind _ = pure []
  varUse (L (RealSrcSpan span) name) = 
    pure [Leaf $ HieToken span Nothing (Just $ RtkVar name) Nothing]
  varUse _ = pure []

instance ToHie (LHsBind GhcTc) where
  toHie b@(L (RealSrcSpan span) bind) = concatM $ case bind of 
      FunBind name matches _ _ _ ->
        [ mkTypeNode "FunBind" 
        , varBind name 
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

instance (ToHie body) => ToHie (MatchGroup GhcTc body) where
  toHie (MG (L (RealSrcSpan span) alts) _ _ _) = concatM
    [ pure [Node (simpleNodeInfo "Alts" "MatchGroup") span []]
    , concatMapM toHie alts
    ]
  toHie _ = pure []

instance (ToHie body) => ToHie (LMatch GhcTc body) where
  toHie (L (RealSrcSpan span) (Match _ pats grhss)) = concatM
    [ pure [Node (simpleNodeInfo "Match" "Match") span []] 
    , concatMapM toHie pats
    , toHie grhss
    ]
  toHie _ = pure []

instance ToHie (LPat GhcTc) where
  toHie (L (RealSrcSpan pspan) opat) = concatM $ case opat of
      WildPat _ ->
        [ mkNode "WildPat"
        ]
      VarPat lname ->
        [ mkNode "VarPat" 
        , varBind lname
        ]
      LazyPat p ->
        [ mkNode "LazyPat" 
        , toHie p
        ]
      AsPat lname lpat ->
        [ mkNode "AsPat" 
        , varBind lname 
        , toHie lpat
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
        , varUse c 
        , toHie dets
        ]
      ConPatOut con _ _ _ _ dets _ ->
        [ mkNode "ConPatIn" 
        , varUse $ fmap conLikeName con 
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
        , varBind n
        ]
      SigPatOut pat _ ->
        [ mkNode "SigPatOut" 
        , toHie pat
        ]
      _ -> []
    where mkNode cons = pure [makeTypeNode cons "Pat" pspan (hsPatType opat)]
  toHie _ = pure []

instance (ToHie body) => ToHie (GRHSs GhcTc body) where
  toHie (GRHSs grhss binds) = concatM
    [ concatMapM toHie grhss 
    , toHie binds
    ]

instance (ToHie body) => ToHie (LGRHS GhcTc body) where
  toHie (L (RealSrcSpan span) (GRHS guards body)) = concatM
    [ pure [Node (simpleNodeInfo "GRHS" "GRHS") span []]
    , concatMapM toHie guards 
    , toHie body
    ]
  toHie _ = pure []

instance ToHie (LHsExpr GhcTc) where
  toHie e@(L (RealSrcSpan span) oexpr) = concatM $ case oexpr of
      HsVar v -> 
        [ mkNode "HsVar" 
        , varUse v
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
        , varUse name 
        , toHie binds
        ]
      RecordUpd expr upds _ _ _ _ -> 
        [ mkNode "RecordUpd" 
        , toHie expr 
        , concatMapM toHie upds
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
      _ -> []
    where 
      mkNode cons = do
        hs_env <- getSession
        (_,mbe) <- liftIO $ deSugarExpr hs_env e
        pure [Node (NodeInfo [(cons,"HsExpr")] (exprType <$> mbe)) span []]
  toHie _ = pure []

instance ToHie (LHsTupArg GhcTc) where
  toHie (L (RealSrcSpan span) arg) = concatM $ case arg of
    Present expr -> 
      [ mkNode "Present" 
      , toHie expr
      ]
    Missing _ -> [ mkNode "Missing" ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsTupArg") span []]
  toHie _ = pure []

instance ToHie body => ToHie (LStmt GhcTc body) where
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

instance ToHie (LHsLocalBinds GhcTc) where
  toHie (L (RealSrcSpan span) binds) = concatM $ case binds of
      EmptyLocalBinds -> [mkNode "EmptyLocalBinds"]
      HsIPBinds _ -> [mkNode "HsIPBinds"]
      HsValBinds valBinds ->
        [ mkNode "HsValBinds" 
        , toHie valBinds
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsLocalBindsLR") span []]
  toHie _ = pure []

instance ToHie (HsValBindsLR GhcTc GhcTc) where
  toHie (ValBindsIn binds _) = concatMapM toHie $ bagToList binds
  toHie (ValBindsOut binds _) = concatMapM toHie $ concatMap (bagToList . snd) binds

instance (ToHie arg) => ToHie (HsRecFields GhcTc arg) where
  toHie (HsRecFields fields _) = concatMapM toHie fields

instance (ToHie (Located label), ToHie arg) => ToHie (LHsRecField' label arg) where
  toHie (L (RealSrcSpan span) (HsRecField label expr _)) = concatM
      [ pure $ [Node (simpleNodeInfo "HsRecField" "HsRecField'") span []] 
      , toHie label
      , toHie expr
      ]
  toHie _ = pure []
  
instance ToHie (LFieldOcc GhcTc) where
  toHie (L nspan (FieldOcc _ name)) = varUse $ L nspan name 

instance ToHie (Located (AmbiguousFieldOcc GhcTc)) where
  toHie (L nspan (Unambiguous _ name)) = varUse $ L nspan name
  toHie (L nspan (Ambiguous _ name)) = varUse $ L nspan name

instance ToHie (ApplicativeArg GhcTc GhcTc) where
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

instance ToHie (LHsCmdTop GhcTc) where
  toHie (L (RealSrcSpan span) (HsCmdTop cmd _ _ _)) = concatM
    [ pure [Node (simpleNodeInfo "HsCmdTop" "HsCmdTop") span []]
    , toHie cmd
    ]
  toHie _ = pure []

instance ToHie (LHsCmd GhcTc) where
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

instance ToHie (ArithSeqInfo GhcTc) where
  toHie _ = pure []

hieFromTypechecked :: forall m. GhcMonad m => TypecheckedSource -> m [HieAST Type]
hieFromTypechecked = go 
  where
    go binds = concatMapM toHie $ bagToList binds
