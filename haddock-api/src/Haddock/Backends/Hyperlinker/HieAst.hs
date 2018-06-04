{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Haddock.Backends.Hyperlinker.HieAst (validAst, enrichHie, ppHie) where

import GHC hiding (exprType, Token)
import Class (FunDep)
import BasicTypes
import FieldLabel
import BooleanFormula
import Outputable (ppr, showSDocUnsafe)
import Bag (Bag, bagToList)
import Var
import ConLike (conLikeName)
import TcHsSyn (hsPatType)
import MonadUtils
import Desugar (deSugarExpr)
import CoreUtils (exprType)
import SrcLoc (mkRealSrcSpan, mkRealSrcLoc)

import Haddock.Backends.Hyperlinker.Types
import Haddock.Backends.Hyperlinker.HieTypes
import Haddock.Backends.Hyperlinker.HieUtils

import Prelude hiding (span)

enrichHie :: GhcMonad m => TypecheckedSource -> RenamedSource -> [Token] -> m (HieAST Type)
enrichHie ts rs@(hsGrp, imports, exports, _) toks = do
    liftIO $ putStrLn $ showSDocUnsafe $ ppr ts
    liftIO $ putStrLn $ showSDocUnsafe $ ppr rs
    tasts <- toHie ts
    rasts <- processGrp hsGrp
    imps <- toHie imports
    exps <- toHie $ fmap (map fst) exports
    liftIO $ print imps
    liftIO $ print exps
    return $ Node (NodeInfo [] Nothing) spanFile $ mergeSortAsts $ concat
      [ tasts
      , rasts
--      , imps
--      , exps
      , map toHieToken toks
      ]
  where
    spanFile = mkRealSrcSpan (mkRealSrcLoc "" 1 1) (mkRealSrcLoc "" 1 1)

    processGrp grp = concatM
      [ toHie $ hs_valds grp
      , toHie $ hs_splcds grp
      , toHie $ hs_tyclds grp
      , toHie $ hs_derivds grp
      , toHie $ hs_fixds grp
      , toHie $ hs_defds grp
      , toHie $ hs_fords grp
      , toHie $ hs_warnds grp
      , toHie $ hs_annds grp
      , toHie $ hs_ruleds grp
      , toHie $ hs_vects grp
      ]

    toHieToken (Token inf _ span) = Leaf (HieToken span (Just inf) Nothing)

locOnly :: SrcSpan -> [HieAST a]
locOnly (RealSrcSpan span) = [Node (NodeInfo [] Nothing) span []]
locOnly _ = []

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

instance (ToHie a) => ToHie [a] where
  toHie = concatMapM toHie

instance (ToHie a) => ToHie (Bag a) where
  toHie = toHie . bagToList

instance (ToHie a) => ToHie (Maybe a) where
  toHie = maybe (pure []) toHie

data Context a = Bind a | Use a

instance ToHie (Located ModuleName) where
  toHie (L (RealSrcSpan span) name) = pure $ [Leaf $ HieToken span Nothing (Just $ RtkModule name)]
  toHie _ = pure []
instance ToHie (Context (Located PlaceHolder)) where
  toHie _ = pure []
instance ToHie (Context (Located Var)) where
  toHie _ = pure []
instance ToHie (Context (Located Name)) where
  toHie c = case c of
      Bind (L (RealSrcSpan span) name) -> pure varBind
        where
          varBind
            | isExternalName name = [Leaf $ HieToken span Nothing (Just $ RtkDecl name)]
            | otherwise       = [Leaf $ HieToken span Nothing (Just $ RtkBind name)]
      Use (L (RealSrcSpan span) name) -> pure $
        [Leaf $ HieToken span Nothing (Just $ RtkVar name)]
      _ -> pure []

-- | Dummy instances - never called
instance ToHie (LHsSigWcType GhcTc) where
  toHie _ = pure []
instance ToHie (LHsWcType GhcTc) where
  toHie _ = pure []
instance ToHie (LSig GhcTc) where
  toHie _ = pure []

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

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (LPat a)
         , ToHie (LHsExpr a)
         , ToHie (LSig a)
         , HasType (LHsBind a)
         ) => ToHie (LHsBind a) where
  toHie b@(L (RealSrcSpan span) bind) = concatM $ case bind of
      FunBind name matches _ _ _ ->
        [ mkTypeNode "FunBind"
        , toHie $ Bind name
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
        , toHie binds
        ]
      PatSynBind psb ->
        [ mkNode "PatSynBind"
        , toHie psb
        ]
    where mkNode cons = pure [makeNode cons "HsBindLR" span]
          mkTypeNode cons = getTypeNode b cons "HsBindLR" span
  toHie _ = pure []

instance ( ToHie (LMatch a body)
         , ToHie body
         ) => ToHie (MatchGroup a body) where
  toHie MG{ mg_alts = (L span alts) } = concatM
    [ pure $ locOnly span
    , toHie alts
    ]

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (LPat a)
         ) => ToHie (PatSynBind a a) where
    toHie (PSB var _ dets pat _) = concatM
      [ toHie $ Use var
      , toHie $ toBind dets
      , toHie pat
      ]
      where toBind (PrefixCon args) = PrefixCon $ map Bind args
            toBind (InfixCon a b) = InfixCon (Bind a) (Bind b)
            toBind (RecCon r) = RecCon r

instance ( ToHie body
         , ToHie (LPat a)
         , ToHie (GRHSs a body)
         ) => ToHie (LMatch a body) where
  toHie (L (RealSrcSpan span) Match{m_pats = pats, m_grhss =  grhss }) = concatM
    [ pure [Node (simpleNodeInfo "Match" "Match") span []]
    , toHie pats
    , toHie grhss
    ]
  toHie _ = pure []

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (HsRecFields a (LPat a))
         , ToHie (LHsExpr a)
         , ToHie (LHsSigWcType a)
         , HasType (LPat a)
         ) => ToHie (LPat a) where
  toHie lpat@(L ospan@(RealSrcSpan pspan) opat) = concatM $ case opat of
      WildPat _ ->
        [ mkNode "WildPat"
        ]
      VarPat lname ->
        [ mkNode "VarPat"
        , toHie $ Bind lname
        ]
      LazyPat p ->
        [ mkNode "LazyPat"
        , toHie p
        ]
      AsPat lname pat ->
        [ mkNode "AsPat"
        , toHie $ Bind lname
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
        , toHie pats
        ]
      TuplePat pats _ _ ->
        [ mkNode "TuplePat"
        , toHie pats
        ]
      SumPat pat _ _ _ ->
        [ mkNode "SumPat"
        , toHie pat
        ]
      PArrPat pats _ ->
        [ mkNode "PArrPat"
        , toHie pats
        ]
      ConPatIn c dets ->
        [ mkNode "ConPatIn"
        , toHie $ Use c
        , toHie dets
        ]
      ConPatOut {pat_con = con, pat_args = dets}->
        [ mkNode "ConPatIn"
        , toHie $ Use $ fmap conLikeName con
        , toHie dets
        ]
      ViewPat expr pat _ ->
        [ mkNode "ViewPat"
        , toHie expr
        , toHie pat
        ]
      SplicePat sp ->
        [ mkNode "SplicePat"
        , toHie $ L ospan sp
        ]
      LitPat _ ->
        [ mkNode "LitPat"
        ]
      NPat _ _ _ _ ->
        [ mkNode "NPat"
        ]
      NPlusKPat n _ _ _ _ _ ->
        [ mkNode "NPlusKPat"
        , toHie $ Bind n
        ]
      SigPatIn pat sig ->
        [ mkNode "SigPatIn"
        , toHie pat
        , toHie sig
        ]
      SigPatOut pat _ ->
        [ mkNode "SigPatOut"
        , toHie pat
        ]
      CoPat _ _ _ ->
        [ mkNode "CoPat"
        ]
    where mkNode cons = getTypeNode lpat cons "Pat" pspan
  toHie _ = pure []

instance ( ToHie body
         , ToHie (LGRHS a body)
         , ToHie (LHsLocalBinds a)
         ) => ToHie (GRHSs a body) where
  toHie (GRHSs grhss binds) = concatM
    [ toHie grhss
    , toHie binds
    ]

instance ( ToHie body
         , ToHie (GuardLStmt a)
         ) => ToHie (LGRHS a body) where
  toHie (L (RealSrcSpan span) (GRHS guards body)) = concatM
    [ pure [Node (simpleNodeInfo "GRHS" "GRHS") span []]
    , toHie guards
    , toHie body
    ]
  toHie _ = pure []

instance ( ToHie (Context (Located (IdP a)))
         , HasType (LHsExpr a)
         , ToHie (LPat a)
         , ToHie (HsRecordBinds a)
         , ToHie (Located (AmbiguousFieldOcc a))
         , ToHie (ArithSeqInfo a)
         , ToHie (LHsCmdTop a)
         , ToHie (HsRecFields a (LPat a))
         , ToHie (GuardLStmt a)
         , ToHie (LHsLocalBinds a)
         , ToHie (LHsSigWcType a)
         , ToHie (LHsWcType a)
         ) => ToHie (LHsExpr a) where
  toHie e@(L mspan oexpr) = concatM $ case oexpr of
      HsVar v ->
        [ mkNode "HsVar"
        , toHie $ Use v
        ]
      HsConLikeOut con ->
        [ mkNode "ConLikeOut"
        , toHie $ Use $ L mspan $ conLikeName con
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
        , toHie sig
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
        , toHie args
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
        , toHie grhss
        ]
      HsLet binds expr ->
        [ mkNode "HsLet"
        , toHie binds
        , toHie expr
        ]
      HsDo _ (L ispan stmts) _ ->
        [ mkNode "HsDo"
        , pure $ locOnly ispan
        , toHie stmts
        ]
      ExplicitList _ _ exprs ->
        [ mkNode "ExplicitList"
        , toHie exprs
        ]
      ExplicitPArr _ exprs ->
        [ mkNode "ExplicitPArr"
        , toHie exprs
        ]
      RecordCon {rcon_con_name = name, rcon_flds = binds}->
        [ mkNode "RecordCon"
        , toHie $ Use name
        , toHie binds
        ]
      RecordUpd {rupd_expr = expr, rupd_flds = upds}->
        [ mkNode "RecordUpd"
        , toHie expr
        , toHie upds
        ]
      ExprWithTySig expr sig ->
        [ mkNode "ExprWithTySig"
        , toHie expr
        , toHie sig
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
        , toHie cmds
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
      HsUnboundVar _ ->
        [ mkNode "HsUnboundVar"
        ]
      HsIPVar _ ->
        [ mkNode "HsIPVar"
        ]
      HsBracket b ->
        [ mkNode "HsBracket p"
        , toHie b
        ]
      HsRnBracketOut b p ->
        [ mkNode "HsRnBracketOut"
        , toHie b
        , toHie p
        ]
      HsTcBracketOut b p ->
        [ mkNode "HsTcBracketOut"
        , toHie b
        , toHie p
        ]
      HsSpliceE x ->
        [ mkNode "HsSpliceE"
        , toHie $ L mspan x
        ]
      EWildPat ->
        [ mkNode "EWildPat"
        ]
      EAsPat a b ->
        [ mkNode "EAsPat"
        , toHie $ Use a
        , toHie b
        ]
      EViewPat a b ->
        [ mkNode "EViewPat"
        , toHie a
        , toHie b
        ]
      ELazyPat a ->
        [ mkNode "ELazyPat"
        , toHie a
        ]
    where
      mkNode cons = case mspan of
        RealSrcSpan span -> getTypeNode e cons "HsExpr" span
        _ -> return []

instance ( ToHie (LHsExpr a)
         ) => ToHie (LHsTupArg a) where
  toHie (L (RealSrcSpan span) arg) = concatM $ case arg of
    Present expr ->
      [ mkNode "Present"
      , toHie expr
      ]
    Missing _ -> [ mkNode "Missing" ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsTupArg") span []]
  toHie _ = pure []

instance ( ToHie (LPat a)
         , ToHie (LHsExpr a)
         , ToHie (LHsBind a)
         , ToHie (LSig a)
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
        , concatMapM (\(ParStmtBlock stmts _ _) -> toHie stmts) parstmts
        ]
      TransStmt {trS_stmts = stmts, trS_using = using, trS_by = by} ->
        [ mkNode "TransStmt"
        , toHie stmts
        , toHie using
        , toHie by
        ]
      RecStmt {recS_stmts = stmts} ->
        [ mkNode "RecStmt"
        , toHie stmts
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "StmtLR") span []]
  toHie _ = pure []

instance ( ToHie (LHsExpr a)
         , ToHie (LPat a)
         , ToHie (LHsBind a)
         , ToHie (LSig a)
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

instance ( ToHie (LHsBind a)
         , ToHie (LPat a)
         , ToHie (LHsExpr a)
         , ToHie (LSig a)
         ) => ToHie (HsValBindsLR a a) where
  toHie (ValBindsIn binds sigs) = concatM
    [ toHie binds
    , toHie sigs
    ]
  toHie (ValBindsOut binds sigs) = concatM
    [ toHie $ concatMap (bagToList . snd) binds
    , toHie sigs
    ]

instance ( ToHie (Context (Located (PostRn a (IdP a))))
         , ToHie (Context (Located (PostTc a (IdP a))))
         , ToHie arg
         ) => ToHie (HsRecFields a arg) where
  toHie (HsRecFields fields _) = toHie fields

instance (ToHie (Located label), ToHie arg) => ToHie (LHsRecField' label arg) where
  toHie (L (RealSrcSpan span) recfld) = concatM $ case recfld of
    HsRecField label expr _ ->
      [ pure $ [Node (simpleNodeInfo "HsRecField" "HsRecField'") span []]
      , toHie label
      , toHie expr
      ]
  toHie _ = pure []

instance ( ToHie (Context (Located (PostRn a (IdP a))))
         , ToHie (Context (Located (PostTc a (IdP a))))
         ) => ToHie (LFieldOcc a) where
  toHie (L nspan (FieldOcc _ name)) = toHie $ Use $ L nspan name

instance ( ToHie (Context (Located (PostRn a (IdP a))))
         , ToHie (Context (Located (PostTc a (IdP a))))
         ) => ToHie (Located (AmbiguousFieldOcc a)) where
  toHie (L nspan (Unambiguous _ name)) = toHie $ Use $ L nspan name
  toHie (L nspan (Ambiguous _ name)) = toHie $ Use $ L nspan name

instance ( ToHie (LPat a)
         , ToHie (LHsBind a)
         , ToHie (LHsExpr a)
         , ToHie (LSig a)
         ) => ToHie (ApplicativeArg a a) where
  toHie (ApplicativeArgOne pat expr _) = concatM
    [ toHie pat
    , toHie expr
    ]
  toHie (ApplicativeArgMany stmts _ pat) = concatM
    [ toHie stmts
    , toHie pat
    ]

instance (ToHie arg, ToHie rec) => ToHie (HsConDetails arg rec) where
  toHie (PrefixCon args) = toHie args
  toHie (RecCon rec) = toHie rec
  toHie (InfixCon a b) = concatM [ toHie a, toHie b]

instance ( ToHie (LPat a)
         , ToHie (LHsBind a)
         , ToHie (LHsExpr a)
         , ToHie (LSig a)
         ) => ToHie (LHsCmdTop a) where
  toHie (L (RealSrcSpan span) top) = concatM $ case top of
    HsCmdTop cmd _ _ _ ->
      [ pure [Node (simpleNodeInfo "HsCmdTop" "HsCmdTop") span []]
      , toHie cmd
      ]
  toHie _ = pure []

instance ( ToHie (LPat a)
         , ToHie (LHsBind a)
         , ToHie (LHsExpr a)
         , ToHie (LSig a)
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
        , toHie cmdtops
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
      HsCmdDo (L ispan stmts) _ ->
        [ mkNode "HsCmdDo"
        , pure $ locOnly ispan
        , toHie stmts
        ]
      HsCmdWrap _ _ ->
        [ mkNode "HsCmdWrap"
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsCmd") span []]
  toHie _ = pure []

instance ToHie (TyClGroup GhcRn) where
  toHie (TyClGroup classes roles instances) = concatM
    [ toHie classes
    , toHie roles
    , toHie instances
    ]

instance ToHie (LTyClDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      FamDecl {tcdFam = fdecl} ->
        [ mkNode "FamDecl"
        , toHie (L (RealSrcSpan span) fdecl)
        ]
      SynDecl {tcdLName = name, tcdTyVars = vars, tcdRhs = typ} ->
        [ mkNode "SynDecl"
        , toHie $ Bind name
        , toHie vars
        , toHie typ
        ]
      DataDecl {tcdLName = name, tcdTyVars = vars, tcdDataDefn = defn} ->
        [ mkNode "DataDecl"
        , toHie $ Bind name
        , toHie vars
        , toHie defn
        ]
      ClassDecl { tcdCtxt = context
                , tcdLName = name
                , tcdTyVars = vars
                , tcdFDs = deps
                , tcdSigs = sigs
                , tcdMeths = meths
                , tcdATs = typs
                , tcdATDefs = deftyps
                } ->
        [ mkNode "ClassDecl"
        , toHie $ Bind name
        , toHie context
        , toHie vars
        , toHie deps
        , toHie sigs
        , toHie meths
        , toHie typs
        , concatMapM (pure . locOnly . getLoc) deftyps
        , toHie $ map unLoc deftyps
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "TyClDecl") span []]
  toHie _ = pure []

instance ToHie (LFamilyDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      FamilyDecl info name vars _ sig inj ->
        [ mkNode "FamilyDecl"
        , toHie $ Bind name
        , toHie info
        , toHie vars
        , toHie sig
        , toHie inj
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "FamilyDecl") span []]
  toHie _ = pure []

instance ToHie (FamilyInfo GhcRn) where
  toHie (ClosedTypeFamily (Just eqns)) = concatM $
    [ concatMapM (pure . locOnly . getLoc) eqns
    , toHie $ map unLoc eqns
    ]
  toHie _ = pure []

instance ToHie (LFamilyResultSig GhcRn) where
  toHie (L (RealSrcSpan span) sig) = concatM $ case sig of
      NoSig ->
        [ mkNode "NoSig" ]
      KindSig k ->
        [ mkNode "KindSig"
        , toHie k
        ]
      TyVarSig bndr ->
        [ mkNode "TyVarSig"
        , toHie bndr
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "FamilyResultSig") span []]
  toHie _ = pure []

instance ToHie (Located (FunDep (Located Name))) where
  toHie (L (RealSrcSpan span) (lhs, rhs)) = concatM $
    [ mkNode "FunDep"
    , toHie $ map Use lhs
    , toHie $ map Use rhs
    ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "FunDep") span []]
  toHie _ = pure []

instance (ToHie pats, ToHie rhs) => ToHie (FamEqn GhcRn pats rhs) where
  toHie (FamEqn var pats _ rhs) = concatM $
    [ toHie $ Bind var
    , toHie pats
    , toHie rhs
    ]

instance ToHie (LInjectivityAnn GhcRn) where
  toHie (L (RealSrcSpan span) ann) = concatM $ case ann of
      InjectivityAnn lhs rhs ->
        [ mkNode "InjectivityAnn"
        , toHie $ Use lhs
        , toHie $ map Use rhs
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "InjectivityAnn") span []]
  toHie _ = pure []

instance ToHie (HsDataDefn GhcRn) where
  toHie (HsDataDefn _ ctx _ mkind cons derivs) = concatM
    [ toHie ctx
    , toHie mkind
    , toHie cons
    , toHie derivs
    ]

instance ToHie (HsDeriving GhcRn) where
  toHie (L span clauses) = concatM
    [ pure $ locOnly span
    , toHie clauses
    ]

instance ToHie (LHsDerivingClause GhcRn) where
  toHie (L (RealSrcSpan span) cl) = concatM $ case cl of
      HsDerivingClause strat (L ispan tys) ->
        [ mkNode "HsDerivingClause"
        , toHie strat
        , pure $ locOnly ispan
        , toHie tys
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsDerivingClause") span []]
  toHie _ = pure []

instance ToHie (Located DerivStrategy) where
  toHie (L span _) = pure $ locOnly span

instance ToHie (Located OverlapMode) where
  toHie (L span _) = pure $ locOnly span

instance ToHie (LConDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      ConDeclGADT names sig _ ->
        [ mkNode "ConDeclGADT"
        , toHie $ map Bind names
        , toHie sig
        ]
      ConDeclH98 name qvars ctx dets _ ->
        [ mkNode "ConDeclH98"
        , toHie $ Bind name
        , toHie qvars
        , toHie ctx
        , toHie dets
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "ConDecl") span []]
  toHie _ = pure []

instance ToHie (Located [LConDeclField GhcRn]) where
  toHie (L span decls) = concatM $
    [ pure $ locOnly span
    , toHie decls
    ]

instance ToHie thing => ToHie (HsImplicitBndrs GhcRn thing) where
  toHie (HsIB _ a _) = toHie a

instance ToHie thing => ToHie (HsWildCardBndrs GhcRn thing) where
  toHie (HsWC _ a) = toHie a

instance ToHie (LSig GhcRn) where
  toHie (L sp@(RealSrcSpan span) sig) = concatM $ case sig of
      TypeSig names typ ->
        [ mkNode "TypeSig"
        , toHie $ map Use names
        , toHie typ
        ]
      PatSynSig names typ ->
        [ mkNode "PatSynSig"
        , toHie $ map Use names
        , toHie typ
        ]
      ClassOpSig _ names typ ->
        [ mkNode "ClassOpSig"
        , toHie $ map Bind names
        , toHie typ
        ]
      IdSig _ -> []
      FixSig fsig ->
        [ mkNode "FixSig"
        , toHie $ L sp fsig
        ]
      InlineSig name _ ->
        [ mkNode "InlineSig"
        , toHie $ Use name
        ]
      SpecSig name typs _ ->
        [ mkNode "SpecSig"
        , toHie $ Use name
        , toHie typs
        ]
      SpecInstSig _ typ ->
        [ mkNode "SpecInstSig"
        , toHie typ
        ]
      MinimalSig _ form ->
        [ mkNode "MinimalSig"
        , toHie form
        ]
      SCCFunSig _ name _ ->
        [ mkNode "SCCFunSig"
        , toHie $ Use name
        ]
      CompleteMatchSig _ (L ispan names) typ ->
        [ mkNode "CompleteMatchSig"
        , pure $ locOnly ispan
        , toHie $ map Use names
        , toHie $ fmap Use typ
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "Sig") span []]
  toHie _ = pure []


instance ToHie (LHsType GhcRn) where
  toHie (L ospan@(RealSrcSpan span) t) = concatM $ case t of
      HsForAllTy bndrs body ->
        [ mkNode "HsForAllTy"
        , toHie bndrs
        , toHie body
        ]
      HsQualTy ctx body ->
        [ mkNode "HsQualTy"
        , toHie ctx
        , toHie body
        ]
      HsTyVar _ var ->
        [ mkNode "HsTyVar"
        , toHie $ Use var
        ]
      HsAppsTy apps ->
        [ mkNode "HsAppsTy"
        , toHie apps
        ]
      HsAppTy a b ->
        [ mkNode "HsAppTy"
        , toHie a
        , toHie b
        ]
      HsFunTy a b ->
        [ mkNode "HsFunTy"
        , toHie a
        , toHie b
        ]
      HsListTy a ->
        [ mkNode "HsListTy"
        , toHie a
        ]
      HsPArrTy a ->
        [ mkNode "HsPArrTy"
        , toHie a
        ]
      HsTupleTy _ tys ->
        [ mkNode "HsTupleTy"
        , toHie tys
        ]
      HsSumTy tys ->
        [ mkNode "HsSymTy"
        , toHie tys
        ]
      HsOpTy a op b ->
        [ mkNode "HsOpTy"
        , toHie a
        , toHie $ Use op
        , toHie b
        ]
      HsParTy a ->
        [ mkNode "HsParTy"
        , toHie a
        ]
      HsIParamTy ip ty ->
        [ mkNode "IParamTy"
        , toHie ip
        , toHie ty
        ]
      HsEqTy a b ->
        [ mkNode "HsEqTy"
        , toHie a
        , toHie b
        ]
      HsKindSig a b ->
        [ mkNode "HsKindSig"
        , toHie a
        , toHie b
        ]
      HsSpliceTy a _ ->
        [ mkNode "HsSpliceTy"
        , toHie $ L ospan a
        ]
      HsDocTy a _ ->
        [ mkNode "HsDocTy"
        , toHie a
        ]
      HsBangTy _ ty ->
        [ mkNode "HsBangTy"
        , toHie ty
        ]
      HsRecTy fields ->
        [ mkNode "HsRecTy"
        , toHie fields
        ]
      HsCoreTy _ ->
        [ mkNode "HsCoreTy"
        ]
      HsExplicitListTy _ _ tys ->
        [ mkNode "HsExplicitListTy"
        , toHie tys
        ]
      HsExplicitTupleTy _ tys ->
        [ mkNode "HsExplicitTupleTy"
        , toHie tys
        ]
      HsTyLit _ ->
        [ mkNode "HsTyLit"
        ]
      HsWildCardTy _ ->
        [ mkNode "HsWildCardTy"
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsType") span []]
  toHie _ = pure []

instance ToHie (LHsTyVarBndr GhcRn) where
  toHie (L (RealSrcSpan span) bndr) = concatM $ case bndr of
      UserTyVar var ->
        [ mkNode "UserTyVar"
        , toHie $ Bind var
        ]
      KindedTyVar var kind ->
        [ mkNode "KindedTyVar"
        , toHie $ Bind var
        , toHie kind
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsTyVarBndr") span []]
  toHie _ = pure []

instance ToHie (LHsQTyVars GhcRn) where
  toHie (HsQTvs _ vars _) = toHie vars

instance ToHie (LHsContext GhcRn) where
  toHie (L span tys) = concatM $
      [ pure $ locOnly span
      , toHie tys
      ]

instance ToHie (LConDeclField GhcRn) where
  toHie (L (RealSrcSpan span) field) = concatM $ case field of
      ConDeclField fields typ _ ->
        [ mkNode "ConDeclField"
        , toHie fields
        , toHie typ
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsConDeclField") span []]
  toHie _ = pure []

instance ToHie (LHsExpr a) => ToHie (ArithSeqInfo a) where
  toHie (From expr) = toHie expr
  toHie (FromThen a b) = concatM $
    [ toHie a
    , toHie b
    ]
  toHie (FromTo a b) = concatM $
    [ toHie a
    , toHie b
    ]
  toHie (FromThenTo a b c) = concatM $
    [ toHie a
    , toHie b
    , toHie c
    ]

instance ToHie (LSpliceDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      SpliceDecl splice _ ->
        [ mkNode "SpliceDecl"
        , toHie splice
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "SpliceDecl") span []]
  toHie _ = pure []

instance ToHie (HsBracket a) where
  toHie _ = pure []

instance ToHie PendingRnSplice where
  toHie _ = pure []

instance ToHie PendingTcSplice where
  toHie _ = pure []

instance ToHie (LBooleanFormula (Located Name)) where
  toHie (L (RealSrcSpan span) form) = concatM $ case form of
      Var a ->
        [ mkNode "Var"
        , toHie $ Use a
        ]
      And forms ->
        [ mkNode "And"
        , toHie forms
        ]
      Or forms ->
        [ mkNode "Or"
        , toHie forms
        ]
      Parens f ->
        [ mkNode "Parens"
        , toHie f
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "BooleanFormula") span []]
  toHie _ = pure []

instance ToHie (Located (HsAppType GhcRn)) where
  toHie (L (RealSrcSpan span) typ) = concatM $ case typ of
      HsAppInfix var ->
        [ mkNode "HsAppInfix"
        , toHie $ Use var
        ]
      HsAppPrefix t ->
        [ mkNode "HsAppPrefix"
        , toHie t
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsAppType") span []]
  toHie _ = pure []

instance ToHie (Located HsIPName) where
  toHie (L (RealSrcSpan span) _) = pure $ [Node (simpleNodeInfo "HsIPName" "HsIPName") span []]
  toHie _ = pure []

instance ToHie (LHsExpr a) => ToHie (Located (HsSplice a)) where
  toHie (L (RealSrcSpan span) sp) = concatM $ case sp of
      HsTypedSplice _ _ expr ->
        [ mkNode "HsTypedSplice"
        , toHie expr
        ]
      HsUntypedSplice _ _ expr ->
        [ mkNode "HsUnTypedSplice"
        , toHie expr
        ]
      HsQuasiQuote _ _ ispan _ ->
        [ mkNode "HsQuasiQuote"
        , pure $ locOnly ispan
        ]
      HsSpliced _ _ ->
        [ mkNode "HsSpliced"
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "HsSplice") span []]
  toHie _ = pure []

instance ToHie (LRoleAnnotDecl GhcRn) where
  toHie (L (RealSrcSpan span) annot) = concatM $ case annot of
      RoleAnnotDecl var roles ->
        [ mkNode "RoleAnnotDecl"
        , toHie $ Use var
        , concatMapM (pure . locOnly . getLoc) roles
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "RoleAnnotDecl") span []]
  toHie _ = pure []

instance ToHie (LInstDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      ClsInstD d ->
        [ mkNode "ClsInstD"
        , toHie d
        ]
      DataFamInstD d ->
        [ mkNode "DataFamInstD"
        , toHie d
        ]
      TyFamInstD d ->
        [ mkNode "TyFamInstD"
        , toHie d
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "InstDecl") span []]
  toHie _ = pure []

instance ToHie (ClsInstDecl GhcRn) where
  toHie decl = concatM
    [ toHie $ cid_poly_ty decl
    , toHie $ cid_binds decl
    , toHie $ cid_sigs decl
    , pure $ concatMap (locOnly . getLoc) $ cid_tyfam_insts decl
    , toHie $ map unLoc $ cid_tyfam_insts decl
    , pure $ concatMap (locOnly . getLoc) $ cid_datafam_insts decl
    , toHie $ map unLoc $ cid_datafam_insts decl
    , toHie $ cid_overlap_mode decl
    ]

instance ToHie (DataFamInstDecl GhcRn) where
  toHie (DataFamInstDecl d) = toHie d

instance ToHie (TyFamInstDecl GhcRn) where
  toHie (TyFamInstDecl d) = toHie d

instance ToHie (Context a) => ToHie (RecordPatSynField a)where
  toHie (RecordPatSynField a b) = concatM $
    [ toHie $ Use a
    , toHie $ Bind b
    ]

instance ToHie (LDerivDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      DerivDecl typ strat overlap ->
        [ mkNode "DerivDecl"
        , toHie typ
        , toHie strat
        , toHie overlap
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "DerivDecl") span []]
  toHie _ = pure []

instance ToHie (LFixitySig GhcRn) where
  toHie (L (RealSrcSpan span) sig) = concatM $ case sig of
      FixitySig vars _ ->
        [ mkNode "FixitySig"
        , toHie $ map Use vars
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "FixitySig") span []]
  toHie _ = pure []

instance ToHie (LDefaultDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      DefaultDecl typs ->
        [ mkNode "DefaultDecl"
        , toHie typs
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "DefaultDecl") span []]
  toHie _ = pure []

instance ToHie (LForeignDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      ForeignImport {fd_name = name, fd_sig_ty = sig, fd_fi = fi} ->
        [ mkNode "ForeignImport"
        , toHie $ Bind name
        , toHie sig
        , toHie fi
        ]
      ForeignExport {fd_name = name, fd_sig_ty = sig, fd_fe = fe} ->
        [ mkNode "ForeignExport"
        , toHie $ Use name
        , toHie sig
        , toHie fe
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "ForeignDecl") span []]
  toHie _ = pure []

instance ToHie ForeignImport where
  toHie (CImport (L a _) (L b _) _ _ (L c _)) = pure $ concat $
    [ locOnly a
    , locOnly b
    , locOnly c
    ]

instance ToHie ForeignExport where
  toHie (CExport (L a _) (L b _)) = pure $ concat $
    [ locOnly a
    , locOnly b
    ]

instance ToHie (LWarnDecls GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      Warnings _ warnings ->
        [ mkNode "Warning"
        , toHie warnings
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "WarnDecls") span []]
  toHie _ = pure []

instance ToHie (LWarnDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      Warning vars _ ->
        [ mkNode "Warning"
        , toHie $ map Use vars
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "WarnDecl") span []]
  toHie _ = pure []

instance ToHie (LAnnDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      HsAnnotation _ prov expr ->
        [ mkNode "HsAnnotation"
        , toHie prov
        , toHie expr
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "AnnDecl") span []]
  toHie _ = pure []

instance ToHie (Context (Located a)) => ToHie (AnnProvenance a) where
  toHie (ValueAnnProvenance a) = toHie $ Use a
  toHie (TypeAnnProvenance a) = toHie $ Use a
  toHie ModuleAnnProvenance = pure []

instance ToHie (LRuleDecls GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      HsRules _ rules ->
        [ mkNode "HsRules"
        , toHie rules
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "RuleDecls") span []]
  toHie _ = pure []

instance ToHie (LRuleDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      HsRule rname _ bndrs exprA _ exprB _->
        [ mkNode "HsRule"
        , pure $ locOnly $ getLoc rname
        , toHie bndrs
        , toHie exprA
        , toHie exprB
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "RuleDecl") span []]
  toHie _ = pure []

instance ToHie (LRuleBndr GhcRn) where
  toHie (L (RealSrcSpan span) bndr) = concatM $ case bndr of
      RuleBndr var ->
        [ mkNode "RuleBndr"
        , toHie $ Use var
        ]
      RuleBndrSig var typ ->
        [ mkNode "RuleBndrSig"
        , toHie $ Use var
        , toHie typ
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "RuleBndr") span []]
  toHie _ = pure []

instance ToHie (LVectDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      HsVect _ var expr ->
        [ mkNode "HsVect"
        , toHie $ Use var
        , toHie expr
        ]
      HsNoVect _ var ->
        [ mkNode "HsNoVect"
        , toHie $ Use var
        ]
      HsVectTypeIn _ _ var mvar ->
        [ mkNode "HsVectTypeIn"
        , toHie $ Use var
        , toHie $ fmap Use mvar
        ]
      HsVectClassIn _ var ->
        [ mkNode "HsVectClassIn"
        , toHie $ Use var
        ]
      HsVectInstIn typ ->
        [ mkNode "HsVectInstIn"
        , toHie typ
        ]
      _ -> []
    where mkNode cons = pure [Node (simpleNodeInfo cons "VectDecl") span []]
  toHie _ = pure []

instance ToHie (LImportDecl GhcRn) where
  toHie (L (RealSrcSpan span) decl) = concatM $ case decl of
      ImportDecl { ideclName = name, ideclAs = as, ideclHiding = hidden } ->
        [ mkNode "ImportDecl"
        , toHie name
        , toHie as
        , maybe (pure []) goIE hidden
        ]
    where
      mkNode cons = pure [Node (simpleNodeInfo cons "ImportDecl") span []]
      goIE (_, (L sp liens)) = concatM $
        [ pure $ locOnly sp
        , toHie liens
        ]
  toHie _ = pure []

instance ToHie (LIE GhcRn) where
  toHie (L (RealSrcSpan span) ie) = concatM $ case ie of
      IEVar n ->
        [ mkNode "IEVar"
        , toHie n
        ]
      IEThingAbs n ->
        [ mkNode "IEThingAbs"
        , toHie n
        ]
      IEThingAll n ->
        [ mkNode "IEThingAll"
        , toHie n
        ]
      IEThingWith n _ ns flds ->
        [ mkNode "IEThingWith"
        , toHie n
        , toHie ns
        , toHie flds
        ]
      IEModuleContents n ->
        [ mkNode "IEModuleContents"
        , toHie n
        ]
      IEGroup _ _ ->
        [ mkNode "IEGroup"
        ]
      IEDoc _ ->
        [ mkNode "IEDoc"
        ]
      IEDocNamed _ ->
        [ mkNode "IEDocNamed"
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "IE") span []]
  toHie _ = pure []

instance ToHie (LIEWrappedName Name) where
  toHie (L (RealSrcSpan span) iewn) = concatM $ case iewn of
      IEName n ->
        [ mkNode "IEName"
        , toHie $ Use n
        ]
      IEPattern p ->
        [ mkNode "IEPattern"
        , toHie $ Use p
        ]
      IEType n ->
        [ mkNode "IEType"
        , toHie $ Use n
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "IEWrappedName") span []]
  toHie _ = pure []

instance ToHie (Located (FieldLbl Name)) where
  toHie (L sp@(RealSrcSpan span) lbl) = concatM $ case lbl of
      FieldLabel _ _ n ->
        [ mkNode "FieldLabel"
        , toHie $ Use $ L sp n
        ]
    where mkNode cons = pure [Node (simpleNodeInfo cons "FieldLbl") span []]
  toHie _ = pure []
