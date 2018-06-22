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
import SrcLoc (realSrcSpanStart, realSrcSpanEnd, mkRealSrcSpan, mkRealSrcLoc, combineSrcSpans)
import FastString (FastString)

import Haddock.Backends.Hyperlinker.HieTypes
import Haddock.Backends.Hyperlinker.HieUtils

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List hiding (span)
import Control.Monad (when)

import Prelude hiding (span)

type Token = ()

enrichHie :: GhcMonad m => TypecheckedSource -> RenamedSource -> [Token] -> m (M.Map FastString (HieAST Type))
enrichHie ts rs@(hsGrp, imports, exports, _) toks = do
    tasts <- toHie $ fmap (FS ModuleScope) ts
    rasts <- processGrp hsGrp
    imps <- toHie $ filter (not . ideclImplicit . unLoc) imports
    exps <- toHie $ fmap (map fst) exports
    let spanFile children = case children of
          [] -> mkRealSrcSpan (mkRealSrcLoc "" 1 1) (mkRealSrcLoc "" 1 1)
          _ -> mkRealSrcSpan (realSrcSpanStart $ astSpan $ head children)
                             (realSrcSpanEnd   $ astSpan $ last children)

        modulify xs =
          Node (simpleNodeInfo "Module" "Module") (spanFile xs) xs

        asts = resolveTyVarScopes
          $ M.map (modulify . mergeSortAsts)
          $ M.fromListWith (++) $ map (\x -> (srcSpanFile (astSpan x),[x])) flat_asts

        flat_asts = concat
          [ tasts
          , rasts
          , imps
          , exps
--          , map toHieToken toks
          ]
    return asts
  where
    processGrp grp = concatM
      [ toHie $ fmap (FS ModuleScope) hs_valds grp
      , toHie $ hs_splcds grp
      , toHie $ hs_tyclds grp
      , toHie $ hs_derivds grp
      , toHie $ hs_fixds grp
      , toHie $ hs_defds grp
      , toHie $ hs_fords grp
      , toHie $ hs_warnds grp
      , toHie $ hs_annds grp
      , toHie $ hs_ruleds grp
      ]

--    toHieToken (Token inf _ span) = Leaf (HieToken span (Just inf) Nothing)

locOnly :: SrcSpan -> [HieAST a]
locOnly (RealSrcSpan span) =
  [Node (NodeInfo S.empty Nothing Nothing (M.empty,Nothing)) span []]
locOnly _ = []

bindingsOnly :: SrcSpan -> [Context Name] -> [HieAST a]
bindingsOnly (RealSrcSpan span) cs =
    [Node (NodeInfo S.empty Nothing Nothing (M.fromList csm, Nothing)) span []]
  where csm = map (\(C c n) -> (n, (Nothing, c))) cs
bindingsOnly _ _ = []

concatM :: Monad m => [m [a]] -> m [a]
concatM xs = concat <$> sequence xs

grhss_span :: GRHSs p body -> SrcSpan
grhss_span (GRHSs _ xs binds) = foldr combineSrcSpans (getLoc binds) (getLoc <$> xs)
grhss_span (XGRHSs _) = error "XGRHS has no span"

mkScope :: SrcSpan -> Scope
mkScope (RealSrcSpan sp) = LocalScope sp
mkScope _ = NoScope

mkLScope :: Located a -> Scope
mkLScope = mkScope . getLoc

combineScopes :: Scope -> Scope -> Scope
combineScopes ModuleScope _ = ModuleScope
combineScopes _ ModuleScope = ModuleScope
combineScopes NoScope x = x
combineScopes x NoScope = x
combineScopes (LocalScope a) (LocalScope b) =
  mkScope $ combineSrcSpans (RealSrcSpan a) (RealSrcSpan b)

patScopes :: Scope -> Scope -> [LPat a] -> [PScoped (LPat a)]
patScopes useScope patScope xs =
  map (\(RS sc a) -> PS useScope sc a) $ listScopes patScope xs

-- Each element scopes over the elements to the right
listScopes :: Scope -> [Located a] -> [RScoped (Located a)]
listScopes _ [] = []
listScopes rhsScope [pat] = [RS rhsScope pat]
listScopes rhsScope (pat : pats) = RS sc pat : pats'
  where
    pats'@((RS scope p):_) = listScopes rhsScope pats
    sc = combineScopes scope $ mkScope $ getLoc p

makeNode :: Applicative m => String -> SrcSpan -> String -> m [HieAST a]
makeNode typ (RealSrcSpan span) cons = pure [Node (simpleNodeInfo cons typ) span []]
makeNode _ _ _ = pure []

makeTypeNode :: String -> String -> SrcSpan -> Type -> [HieAST Type]
makeTypeNode cons typ spn etyp = case spn of
  RealSrcSpan span ->
    [Node (NodeInfo (S.singleton (cons,typ)) Nothing (Just etyp) (M.empty,Nothing)) span []]
  _ -> []

data Context a = C ContextInfo a

data RScoped a = RS Scope a
-- ^ Scope spans over everything to the right of a, (mostly) not
-- including a (Includes a in a few special cases like recursive do bindings)

data PScoped a = PS Scope Scope a
-- ^ First Scope spans over the use site of the pattern, second spans over the
-- patterns to the right of a, not including a

data FScoped a = FS Scope a
-- ^ Scope spans over all of a's scope, including a itself

data CScoped a = CS Scope Scope Scope a
-- ^ Context scope, binder scope, class decl scope

data TScoped a = TS TyVarScope a

data TVScoped a = TVS TyVarScope Scope a

class ToHie a where
  toHie :: GhcMonad m => a -> m [HieAST Type]

class HasType a where
  getTypeNode :: GhcMonad m => a -> String -> m [HieAST Type]

instance (ToHie a) => ToHie [a] where
  toHie = concatMapM toHie

instance (ToHie a) => ToHie (Bag a) where
  toHie = toHie . bagToList

instance (ToHie a) => ToHie (Maybe a) where
  toHie = maybe (pure []) toHie

instance ToHie (Context (Located NoExt)) where
  toHie _ = pure []

instance ToHie (Located ModuleName) where
  toHie (L (RealSrcSpan span) name) =
    pure $ [Node (NodeInfo S.empty Nothing Nothing (M.empty, Just name)) span []]
  toHie _ = pure []

instance ToHie (Context (Located Var)) where
  toHie c = case c of
      C context (L (RealSrcSpan span) name) -> pure $
        [Node (NodeInfo S.empty Nothing Nothing
          (M.singleton (varName name) (Just $ varType name, context),Nothing)) span []]
      _ -> pure []

instance ToHie (Context (Located Name)) where
  toHie c = case c of
      C context (L (RealSrcSpan span) name) -> pure $
        [Node (NodeInfo S.empty Nothing Nothing
          (M.singleton name (Nothing, context),Nothing)) span []]
      _ -> pure []

-- | Dummy instances - never called
instance ToHie (TScoped (LHsSigWcType GhcTc)) where
  toHie _ = pure []
instance ToHie (TScoped (LHsWcType GhcTc)) where
  toHie _ = pure []
instance ToHie (LSig GhcTc) where
  toHie _ = pure []
instance ToHie (TScoped Type) where
  toHie _ = pure []

instance HasType (LHsBind GhcRn) where
  getTypeNode (L spn _) cons = makeNode "HsBindLR" spn cons

instance HasType (LHsBind GhcTc) where
  getTypeNode (L spn bind) cons = case bind of
      FunBind{fun_id = name} -> pure $ makeTypeNode cons "HsBindLR" spn (varType $ unLoc name)
      _ -> makeNode "HsBindLR" spn cons

instance HasType (LPat GhcRn) where
  getTypeNode (L spn _) cons = makeNode "Pat" spn cons

instance HasType (LPat GhcTc) where
  getTypeNode (L spn opat) cons =
    pure $ makeTypeNode cons "Pat" spn (hsPatType opat)

instance HasType (LHsExpr GhcRn) where
  getTypeNode (L spn _) cons = makeNode "HsExpr" spn cons

instance HasType (LHsExpr GhcTc) where
  getTypeNode e@(L spn _) cons = do
    hs_env <- getSession
    (_,mbe) <- liftIO $ deSugarExpr hs_env e
    case mbe of
      Just te -> pure $ makeTypeNode cons "HsExpr" spn (exprType te)
      Nothing -> makeNode "HsExpr" spn cons

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (MatchGroup a (LHsExpr a))
         , ToHie (PScoped (LPat a))
         , ToHie (GRHSs a (LHsExpr a))
         , ToHie (LHsExpr a)
         , ToHie (FScoped (PatSynBind a a))
         , HasType (LHsBind a)
         ) => ToHie (FScoped (LHsBind a)) where
  toHie (FS scope b@(L span bind)) = concatM $ case bind of
      FunBind{fun_id = name, fun_matches = matches} ->
        [ mkTypeNode "FunBind"
        , toHie $ C (Bind scope) name
        , toHie matches
        ]
      PatBind{pat_lhs = lhs, pat_rhs = rhs} ->
        [ mkNode "PatBind"
        , toHie $ PS scope NoScope lhs
        , toHie rhs
        ]
      VarBind{var_rhs = expr} ->
        [ mkNode "VarBind"
        , toHie expr
        ]
      AbsBinds{abs_binds = binds} ->
        [ mkNode "AbsBinds"
        , toHie $ fmap (FS scope) binds
        ]
      PatSynBind _ psb ->
        [ mkNode "PatSynBind"
        , toHie $ FS scope psb
        ]
      XHsBindsLR _ -> []
    where mkNode = makeNode "HsBindLR" span
          mkTypeNode cons = getTypeNode b cons

instance ( ToHie (LMatch a body)
         ) => ToHie (MatchGroup a body) where
  toHie mg = concatM $ case mg of
    MG{ mg_alts = (L span alts) } ->
      [ pure $ locOnly span -- causes crash in PrimOp.hs
      , toHie alts
      ]
    XMatchGroup _ -> []

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (PScoped (LPat a))
         , ToHie (HsPatSynDir a)
         ) => ToHie (FScoped (PatSynBind a a)) where
    toHie (FS scope psb) = concatM $ case psb of
      PSB{psb_id=var, psb_args=dets, psb_def=pat, psb_dir=dir} ->
        [ toHie $ C (Bind scope) var
        , toHie $ toBind dets
        , toHie $ PS lhsScope NoScope pat
        , toHie dir
        ]
        where
          lhsScope = combineScopes varScope detScope
          varScope = mkLScope var
          detScope = case dets of
            (PrefixCon args) -> foldr combineScopes NoScope $ map mkLScope args
            (InfixCon a b) -> combineScopes (mkLScope a) (mkLScope b)
            (RecCon r) -> foldr go NoScope r
          go (RecordPatSynField a b) c = combineScopes c
            $ combineScopes (mkLScope a) (mkLScope b)
      XPatSynBind _ -> []
      where toBind (PrefixCon args) = PrefixCon $ map (C Use) args
            toBind (InfixCon a b) = InfixCon (C Use a) (C Use b)
            toBind (RecCon r) = RecCon $ map (FS scope) r

instance ( ToHie (MatchGroup a (LHsExpr a))
         ) => ToHie (HsPatSynDir a) where
  toHie dir = case dir of
    ExplicitBidirectional mg -> toHie mg
    _ -> pure []

instance ( ToHie body
         , ToHie (HsMatchContext (NameOrRdrName (IdP a)))
         , ToHie (PScoped (LPat a))
         , ToHie (GRHSs a body)
         ) => ToHie (LMatch a body) where
  toHie (L span m ) = concatM $ case m of
    Match{m_ctxt=mctx, m_pats = pats, m_grhss =  grhss } ->
      [ makeNode "Match" span "Match"
      , toHie mctx
      , let rhsScope = mkScope $ grhss_span grhss
          in toHie $ patScopes rhsScope NoScope pats
      , toHie grhss
      ]
    XMatch _ -> []

instance ( ToHie (Context (Located a))
         ) => ToHie (HsMatchContext a) where
  toHie (FunRhs{mc_fun=name}) = toHie $ C MatchBind name
  toHie (StmtCtxt a) = toHie a
  toHie _ = pure []

instance ( ToHie (HsMatchContext a)
         ) => ToHie (HsStmtContext a) where
  toHie (PatGuard a) = toHie a
  toHie (ParStmtCtxt a) = toHie a
  toHie (TransStmtCtxt a) = toHie a
  toHie _ = pure []

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (HsRecFields a (PScoped (LPat a)))
         , ToHie (LHsExpr a)
         , ToHie (TScoped (LHsSigWcType a))
         , ToHie (TScoped (XSigPat a))
         , HasType (LPat a)
         ) => ToHie (PScoped (LPat a)) where
  toHie (PS scope pscope lpat@(L ospan opat)) = concatM $ case opat of
      WildPat _ ->
        [ mkNode "WildPat"
        ]
      VarPat _ lname ->
        [ mkNode "VarPat"
        , toHie $ C (PatBindScope scope pscope) lname
        ]
      LazyPat _ p ->
        [ mkNode "LazyPat"
        , toHie $ PS scope pscope p
        ]
      AsPat _ lname pat ->
        [ mkNode "AsPat"
        , toHie $ C (PatBindScope scope $ combineScopes (mkLScope pat) pscope) lname
        , toHie $ PS scope pscope pat
        ]
      ParPat _ pat ->
        [ mkNode "ParPat"
        , toHie $ PS scope pscope pat
        ]
      BangPat _ pat ->
        [ mkNode "BangPat"
        , toHie $ PS scope pscope pat
        ]
      ListPat _ pats ->
        [ mkNode "ListPat"
        , toHie $ patScopes scope pscope pats
        ]
      TuplePat _ pats _ ->
        [ mkNode "TuplePat"
        , toHie $ patScopes scope pscope pats
        ]
      SumPat _ pat _ _ ->
        [ mkNode "SumPat"
        , toHie $ PS scope pscope pat
        ]
      ConPatIn c dets ->
        [ mkNode "ConPatIn"
        , toHie $ C Use c
        , toHie $ contextify dets
        ]
      ConPatOut {pat_con = con, pat_args = dets}->
        [ mkNode "ConPatIn"
        , toHie $ C Use $ fmap conLikeName con
        , toHie $ contextify dets
        ]
      ViewPat _ expr pat ->
        [ mkNode "ViewPat"
        , toHie expr
        , toHie $ PS scope pscope pat
        ]
      SplicePat _ sp ->
        [ mkNode "SplicePat"
        , toHie $ L ospan sp
        ]
      LitPat _ _ ->
        [ mkNode "LitPat"
        ]
      NPat _ _ _ _ ->
        [ mkNode "NPat"
        ]
      NPlusKPat _ n _ _ _ _ ->
        [ mkNode "NPlusKPat"
        , toHie $ C (PatBindScope scope pscope) n
        ]
      SigPat sig pat ->
        [ mkNode "SigPat"
        , toHie $ PS scope pscope pat
        , toHie $ TS (ResolvedScopes [mkLScope pat, scope, pscope]) sig
        ]
      CoPat _ _ _ _ ->
        [ mkNode "CoPat"
        ]
      XPat _ -> []
    where mkNode cons = getTypeNode lpat cons
          contextify (PrefixCon args) = PrefixCon $ patScopes scope pscope args
          contextify (InfixCon a b) = InfixCon a' b'
            where [a', b'] = patScopes scope pscope [a,b]
          contextify (RecCon r) = RecCon $ contextify_rec r
          contextify_rec (HsRecFields fields a) = HsRecFields (map go $ scoped_fields) a
            where
              go (RS fscope (L sp (HsRecField lbl pat pun))) = L sp $ HsRecField lbl (PS scope fscope pat) pun
              scoped_fields = listScopes pscope fields

instance ( ToHie body
         , ToHie (LGRHS a body)
         , ToHie (RScoped (LHsLocalBinds a))
         ) => ToHie (GRHSs a body) where
  toHie grhs = concatM $ case grhs of
    GRHSs _ grhss binds ->
     [ toHie grhss
     , toHie $ RS (mkScope $ grhss_span grhs) binds
     ]
    XGRHSs _ -> []

instance ( ToHie (Located body)
         , ToHie (RScoped (GuardLStmt a))
         ) => ToHie (LGRHS a (Located body)) where
  toHie (L span g) = concatM $ case g of
    GRHS _ guards body ->
      [ makeNode "GRHS" span "GRHS"
      , toHie $ listScopes (mkLScope body) guards
      , toHie body
      ]
    XGRHS _ -> []

instance ( ToHie (Context (Located (IdP a)))
         , HasType (LHsExpr a)
         , ToHie (PScoped (LPat a))
         , ToHie (MatchGroup a (LHsExpr a))
         , ToHie (LGRHS a (LHsExpr a))
         , ToHie (HsRecordBinds a)
         , ToHie (Located (AmbiguousFieldOcc a))
         , ToHie (ArithSeqInfo a)
         , ToHie (LHsCmdTop a)
         , ToHie (RScoped (GuardLStmt a))
         , ToHie (RScoped (LHsLocalBinds a))
         , ToHie (TScoped (XAppTypeE a))
         , ToHie (TScoped (XExprWithTySig a))
         ) => ToHie (LHsExpr a) where
  toHie e@(L mspan oexpr) = concatM $ case oexpr of
      HsVar _ (L _ var) ->
        [ mkNode "HsVar"
        , toHie $ C Use (L mspan var) -- Patch up var location since typechecker removes it
        ]
      HsUnboundVar _ _ ->
        [ mkNode "HsUnboundVar"
        ]
      HsConLikeOut _ con ->
        [ mkNode "ConLikeOut"
        , toHie $ C Use $ L mspan $ conLikeName con
        ]
      HsRecFld _ fld ->
        [ mkNode "HsRecFld"
        , toHie (L mspan fld)
        ]
      HsOverLabel _ _ _ ->
        [ mkNode "HsOverLable"
        ]
      HsIPVar _ _ ->
        [ mkNode "HsIPVar"
        ]
      HsOverLit _ _ ->
        [ mkNode "HsOverLit"
        ]
      HsLit _ _ ->
        [ mkNode "HsLit"
        ]
      HsLam _ mg ->
        [ mkNode "HsLam"
        , toHie mg
        ]
      HsLamCase _ mg ->
        [ mkNode "HsLamCase"
        , toHie mg
        ]
      HsApp _ a b ->
        [ mkNode "HsApp"
        , toHie a
        , toHie b
        ]
      HsAppType sig expr ->
        [ mkNode "HsAppType"
        , toHie expr
        , toHie $ TS (ResolvedScopes []) sig
        ]
      OpApp _ a b c ->
        [ mkNode "OpApp"
        , toHie a
        , toHie b
        , toHie c
        ]
      NegApp _ a _ ->
        [ mkNode "NegApp"
        , toHie a
        ]
      HsPar _ a ->
        [ mkNode "HsPar"
        , toHie a
        ]
      SectionL _ a b ->
        [ mkNode "SectionL"
        , toHie a
        , toHie b
        ]
      SectionR _ a b ->
        [ mkNode "SectionR"
        , toHie a
        , toHie b
        ]
      ExplicitTuple _ args _ ->
        [ mkNode "ExplicitTyple"
        , toHie args
        ]
      ExplicitSum _ _ _ expr ->
        [ mkNode "ExplicitSum"
        , toHie expr
        ]
      HsCase _ expr matches ->
        [ mkNode "HsCase"
        , toHie expr
        , toHie matches
        ]
      HsIf _ _ a b c ->
        [ mkNode "HsIf"
        , toHie a
        , toHie b
        , toHie c
        ]
      HsMultiIf _ grhss ->
        [ mkNode "HsMultiIf"
        , toHie grhss
        ]
      HsLet _ binds expr ->
        [ mkNode "HsLet"
        , toHie $ RS (mkLScope expr) binds
        , toHie expr
        ]
      HsDo _ _ (L ispan stmts) ->
        [ mkNode "HsDo"
        , pure $ locOnly ispan
        , toHie $ listScopes NoScope stmts
        ]
      ExplicitList _ _ exprs ->
        [ mkNode "ExplicitList"
        , toHie exprs
        ]
      RecordCon {rcon_con_name = name, rcon_flds = binds}->
        [ mkNode "RecordCon"
        , toHie $ C Use name
        , toHie binds
        ]
      RecordUpd {rupd_expr = expr, rupd_flds = upds}->
        [ mkNode "RecordUpd"
        , toHie expr
        , toHie upds
        ]
      ExprWithTySig sig expr ->
        [ mkNode "ExprWithTySig"
        , toHie expr
        , toHie $ TS (ResolvedScopes [mkLScope expr]) sig
        ]
      ArithSeq _ _ info ->
        [ mkNode "ArithSeq"
        , toHie info
        ]
      HsSCC _ _ _ expr ->
        [ mkNode "HsSCC"
        , toHie expr
        ]
      HsCoreAnn _ _ _ expr ->
        [ mkNode "HsCoreAnn"
        , toHie expr
        ]
      HsProc _ pat cmdtop ->
        [ mkNode "HsProc"
        , toHie $ PS (mkLScope cmdtop) NoScope pat
        , toHie cmdtop
        ]
      HsStatic _ expr ->
        [ mkNode "HsStatic"
        , toHie expr
        ]
      HsArrApp _ a b _ _ ->
        [ mkNode "HsArrApp"
        , toHie a
        , toHie b
        ]
      HsArrForm _ expr _ cmds ->
        [ mkNode "HsArrForm"
        , toHie expr
        , toHie cmds
        ]
      HsTick _ _ expr ->
        [ mkNode "HsTick"
        , toHie expr
        ]
      HsBinTick _ _ _ expr ->
        [ mkNode "HsBinTick"
        , toHie expr
        ]
      HsTickPragma _ _ _ _ expr ->
        [ mkNode "HsTickPragma"
        , toHie expr
        ]
      HsWrap _ _ a ->
        [ mkNode "HsWrap"
        , toHie $ L mspan a
        ]
      HsBracket _ b ->
        [ mkNode "HsBracket p"
        , toHie b
        ]
      HsRnBracketOut _ b p ->
        [ mkNode "HsRnBracketOut"
        , toHie b
        , toHie p
        ]
      HsTcBracketOut _ b p ->
        [ mkNode "HsTcBracketOut"
        , toHie b
        , toHie p
        ]
      HsSpliceE _ x ->
        [ mkNode "HsSpliceE"
        , toHie $ L mspan x
        ]
      EWildPat _ ->
        [ mkNode "EWildPat"
        ]
      EAsPat _ a b ->
        [ mkNode "EAsPat"
        , toHie $ C Use a
        , toHie b
        ]
      EViewPat _ a b ->
        [ mkNode "EViewPat"
        , toHie a
        , toHie b
        ]
      ELazyPat _ a ->
        [ mkNode "ELazyPat"
        , toHie a
        ]
      XExpr _ -> []
    where
      mkNode cons = getTypeNode e cons

instance ( ToHie (LHsExpr a)
         ) => ToHie (LHsTupArg a) where
  toHie (L span arg) = concatM $ case arg of
    Present _ expr ->
      [ mkNode "Present"
      , toHie expr
      ]
    Missing _ -> [ mkNode "Missing" ]
    XTupArg _ -> []
    where mkNode = makeNode "HsTupArg" span

instance ( ToHie (PScoped (LPat a))
         , ToHie (LHsExpr a)
         , ToHie (LSig a)
         , ToHie (RScoped (LHsLocalBinds a))
         , ToHie (RScoped (ApplicativeArg a))
         , ToHie body
         ) => ToHie (RScoped (LStmt a body)) where
  toHie (RS scope (L span stmt)) = concatM $ case stmt of
      LastStmt _ body _ _ ->
        [ mkNode "LastStmt"
        , toHie body
        ]
      BindStmt _ pat body _ _ ->
        [ mkNode "BindStmt"
        , toHie $ PS scope NoScope pat
        , toHie body
        ]
      ApplicativeStmt _ stmts _ ->
        [ mkNode "ApplicativeStmt"
        , concatMapM (toHie . RS scope . snd) stmts
        ]
      BodyStmt _ body _ _ ->
        [ mkNode "BodyStmt"
        , toHie body
        ]
      LetStmt _ binds ->
        [ mkNode "LetStmt"
        , toHie $ RS scope binds
        ]
      ParStmt _ parstmts _ _ ->
        [ mkNode "ParStmt"
        , concatMapM (\(ParStmtBlock _ stmts _ _) -> toHie $ listScopes NoScope stmts) parstmts
        ]
      TransStmt {trS_stmts = stmts, trS_using = using, trS_by = by} ->
        [ mkNode "TransStmt"
        , toHie $ listScopes scope stmts
        , toHie using
        , toHie by
        ]
      RecStmt {recS_stmts = stmts} ->
        [ mkNode "RecStmt"
        , toHie $ map (RS $ combineScopes scope (mkScope span)) stmts
        ]
      XStmtLR _ -> []
    where mkNode = makeNode "StmtLR" span

instance ( ToHie (LHsExpr a)
         , ToHie (PScoped (LPat a))
         , ToHie (FScoped (LHsBind a))
         , ToHie (LSig a)
         , ToHie (FScoped (HsValBindsLR a a))
         ) => ToHie (RScoped (LHsLocalBinds a)) where
  toHie (RS scope (L span binds)) = concatM $ case binds of
      EmptyLocalBinds _ -> [mkNode "EmptyLocalBinds"]
      HsIPBinds _ _ -> [mkNode "HsIPBinds"]
      HsValBinds _ valBinds ->
        [ mkNode "HsValBinds"
        , toHie $ (FS $ combineScopes scope $ mkScope span) valBinds
        ]
      XHsLocalBindsLR _ -> []
    where mkNode = makeNode "HsLocalBindsLR" span

instance ( ToHie (FScoped (LHsBind a))
         , ToHie (LSig a)
         , ToHie (FScoped (XXValBindsLR a a))
         ) => ToHie (FScoped (HsValBindsLR a a)) where
  toHie (FS sp v) = concatM $ case v of
    ValBinds _ binds sigs ->
      [ toHie $ fmap (FS sp) binds
      , toHie sigs
      ]
    XValBindsLR x -> [ toHie $ FS sp x ]

instance ToHie (FScoped (NHsValBindsLR GhcTc)) where
  toHie (FS sp (NValBinds binds sigs)) = concatM $
    [ toHie (concatMap (map (FS sp) . bagToList . snd) binds)
    , toHie sigs
    ]
instance ToHie (FScoped (NHsValBindsLR GhcRn)) where
  toHie (FS sp (NValBinds binds sigs)) = concatM $
    [ toHie (concatMap (map (FS sp) . bagToList . snd) binds)
    , toHie sigs
    ]

instance ( ToHie (LHsRecField a arg)
         ) => ToHie (HsRecFields a arg) where
  toHie (HsRecFields fields _) = toHie fields

instance (ToHie (Located label), ToHie arg) => ToHie (LHsRecField' label arg) where
  toHie (L span recfld) = concatM $ case recfld of
    HsRecField label expr _ ->
      [ makeNode "HsRecField" span "HsRecField'"
      , toHie label
      , toHie expr
      ]

instance ( ToHie (Context (Located (XFieldOcc a)))
         ) => ToHie (LFieldOcc a) where
  toHie (L nspan f) = concatM $ case f of
    FieldOcc name _ ->
      [ toHie $ C Use $ L nspan name
      ]
    XFieldOcc _ -> []

instance ( ToHie (Context (Located (XUnambiguous a)))
         , ToHie (Context (Located (XAmbiguous a)))
         ) => ToHie (Located (AmbiguousFieldOcc a)) where
  toHie (L nspan afo) = concatM $ case afo of
    Unambiguous name _ ->
      [ toHie $ C Use $ L nspan name
      ]
    Ambiguous name _ ->
      [ toHie $ C Use $ L nspan name
      ]
    XAmbiguousFieldOcc _ -> []

instance ( ToHie (PScoped (LPat a))
         , ToHie (FScoped (LHsBind a))
         , ToHie (LHsExpr a)
         , ToHie (LSig a)
         , ToHie (FScoped (HsValBindsLR a a))
         ) => ToHie (RScoped (ApplicativeArg a)) where
  toHie (RS sc (ApplicativeArgOne _ pat expr _)) = concatM
    [ toHie $ PS sc NoScope pat
    , toHie expr
    ]
  toHie (RS sc (ApplicativeArgMany _ stmts _ pat)) = concatM
    [ toHie $ listScopes NoScope stmts
    , toHie $ PS sc NoScope pat
    ]
  toHie (RS _ (XApplicativeArg _)) = pure []

instance (ToHie arg, ToHie rec) => ToHie (HsConDetails arg rec) where
  toHie (PrefixCon args) = toHie args
  toHie (RecCon rec) = toHie rec
  toHie (InfixCon a b) = concatM [ toHie a, toHie b]

instance ( ToHie (LHsCmd a)
         ) => ToHie (LHsCmdTop a) where
  toHie (L span top) = concatM $ case top of
    HsCmdTop _ cmd ->
      [ makeNode "HsCmdTop" span "HsCmdTop"
      , toHie cmd
      ]
    XCmdTop _ -> []

instance ( ToHie (PScoped (LPat a))
         , ToHie (FScoped (LHsBind a))
         , ToHie (LHsExpr a)
         , ToHie (MatchGroup a (LHsCmd a))
         , ToHie (LSig a)
         , ToHie (FScoped (HsValBindsLR a a))
         ) => ToHie (LHsCmd a) where
  toHie (L span cmd) = concatM $ case cmd of
      HsCmdArrApp _ a b _ _ ->
        [ mkNode "HsCmdArrApp"
        , toHie a
        , toHie b
        ]
      HsCmdArrForm _ a _ _ cmdtops ->
        [ mkNode "HsCmdArrForm"
        , toHie a
        , toHie cmdtops
        ]
      HsCmdApp _ a b ->
        [ mkNode "HsCmdApp"
        , toHie a
        , toHie b
        ]
      HsCmdLam _ mg ->
        [ mkNode "HsCmdLam"
        , toHie mg
        ]
      HsCmdPar _ a ->
        [ mkNode "HsCmdPar"
        , toHie a
        ]
      HsCmdCase _ expr alts ->
        [ mkNode "HsCmdCase"
        , toHie expr
        , toHie alts
        ]
      HsCmdIf _ _ a b c ->
        [ mkNode "HsCmdIf"
        , toHie a
        , toHie b
        , toHie c
        ]
      HsCmdLet _ binds cmd' ->
        [ mkNode "HsCmdLet"
        , toHie $ RS (mkLScope cmd') binds
        , toHie cmd'
        ]
      HsCmdDo _ (L ispan stmts) ->
        [ mkNode "HsCmdDo"
        , pure $ locOnly ispan
        , toHie $ listScopes NoScope stmts
        ]
      HsCmdWrap _ _ _ ->
        [ mkNode "HsCmdWrap"
        ]
      XCmd _ -> []
    where mkNode = makeNode "HsCmd" span

instance ToHie (TyClGroup GhcRn) where
  toHie (TyClGroup _ classes roles instances) = concatM
    [ toHie classes
    , toHie roles
    , toHie instances
    ]
  toHie (XTyClGroup _) = pure []

instance ToHie (LTyClDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      FamDecl {tcdFam = fdecl} ->
        [ mkNode "FamDecl"
        , toHie (L span fdecl)
        ]
      SynDecl {tcdLName = name, tcdTyVars = vars, tcdRhs = typ} ->
        [ mkNode "SynDecl"
        , toHie $ C (Bind ModuleScope) name
        , toHie $ RS (mkScope $ getLoc typ) vars
        , toHie typ
        ]
      DataDecl {tcdLName = name, tcdTyVars = vars, tcdDataDefn = defn} ->
        [ mkNode "DataDecl"
        , toHie $ C (Bind ModuleScope) name
        , toHie $ CS quant_scope NoScope rhs_scope vars
        , toHie defn
        ]
        where
          quant_scope = mkLScope $ dd_ctxt defn
          rhs_scope = combineScopes sig_scope (combineScopes constr_scope deriving_scope)
          sig_scope = maybe NoScope mkLScope $ dd_kindSig defn
          constr_scope = foldr combineScopes NoScope $ map mkLScope $ dd_cons defn
          deriving_scope = mkLScope $ dd_derivs defn
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
        , toHie $ C (Bind ModuleScope) name
        , toHie context
        , toHie $ RS (mkScope span) vars
        , toHie deps
        , toHie sigs
        , toHie $ fmap (FS ModuleScope) meths
        , toHie typs
        , concatMapM (pure . locOnly . getLoc) deftyps
        , toHie $ map (go . unLoc) deftyps
        ]
        where
          go :: TyFamDefltEqn GhcRn -> FamEqn GhcRn (RScoped (LHsQTyVars GhcRn)) (LHsType GhcRn)
          go (FamEqn a var pat b rhs) = FamEqn a var (RS (mkLScope rhs) pat) b rhs
          go (XFamEqn NoExt) = XFamEqn NoExt
      XTyClDecl _ -> []
    where mkNode = makeNode "TyClDecl" span

instance ToHie (LFamilyDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      FamilyDecl _ info name vars _ sig inj ->
        [ mkNode "FamilyDecl"
        , toHie $ C (Bind ModuleScope) name
        , toHie $ RS rhsSpan vars
        , toHie info
        , toHie $ RS injSpan sig
        , toHie inj
        ]
        where
          rhsSpan = sigSpan `combineScopes` injSpan
          sigSpan = mkScope $ getLoc sig
          injSpan = maybe NoScope (mkScope . getLoc) inj
      XFamilyDecl _ -> []
    where mkNode = makeNode "FamilyDecl" span

instance ToHie (FamilyInfo GhcRn) where
  toHie (ClosedTypeFamily (Just eqns)) = concatM $
    [ concatMapM (pure . locOnly . getLoc) eqns
    , toHie $ map go eqns
    ]
    where
      go (L l ib) = TS (ResolvedScopes [mkScope l]) ib
  toHie _ = pure []

instance ToHie (RScoped (LFamilyResultSig GhcRn)) where
  toHie (RS sc (L span sig)) = concatM $ case sig of
      NoSig _ ->
        [ mkNode "NoSig" ]
      KindSig _ k ->
        [ mkNode "KindSig"
        , toHie k
        ]
      TyVarSig _ bndr ->
        [ mkNode "TyVarSig"
        , toHie $ TVS (ResolvedScopes []) sc bndr
        ]
      XFamilyResultSig _ -> []
    where mkNode = makeNode "FamilyResultSig" span

instance ToHie (Located (FunDep (Located Name))) where
  toHie (L span (lhs, rhs)) = concatM $
    [ mkNode "FunDep"
    , toHie $ map (C Use) lhs
    , toHie $ map (C Use) rhs
    ]
    where mkNode = makeNode "FunDep" span

instance (ToHie pats, ToHie rhs) => ToHie (TScoped (FamEqn GhcRn pats rhs)) where
  toHie (TS _ f) = toHie f

instance (ToHie pats, ToHie rhs) => ToHie (FamEqn GhcRn pats rhs) where
  toHie (FamEqn _ var pats _ rhs) = concatM $
    [ toHie $ C InstBind var
    , toHie pats
    , toHie rhs
    ]
  toHie (XFamEqn _) = pure []

instance ToHie (LInjectivityAnn GhcRn) where
  toHie (L span ann) = concatM $ case ann of
      InjectivityAnn lhs rhs ->
        [ mkNode "InjectivityAnn"
        , toHie $ C Use lhs
        , toHie $ map (C Use) rhs
        ]
    where mkNode = makeNode "InjectivityAnn" span

instance ToHie (HsDataDefn GhcRn) where
  toHie (HsDataDefn _ _ ctx _ mkind cons derivs) = concatM
    [ toHie ctx
    , toHie mkind
    , toHie cons
    , toHie derivs
    ]
  toHie (XHsDataDefn _) = pure []

instance ToHie (HsDeriving GhcRn) where
  toHie (L span clauses) = concatM
    [ pure $ locOnly span
    , toHie clauses
    ]

instance ToHie (LHsDerivingClause GhcRn) where
  toHie (L span cl) = concatM $ case cl of
      HsDerivingClause _ strat (L ispan tys) ->
        [ mkNode "HsDerivingClause"
        , toHie strat
        , pure $ locOnly ispan
        , toHie $ map (TS (ResolvedScopes [])) tys
        ]
      XHsDerivingClause _ -> []
    where mkNode = makeNode "HsDerivingClause" span

instance ToHie (Located (DerivStrategy GhcRn)) where
  toHie (L span strat) = concatM $ case strat of
      StockStrategy ->
        [ mkNode "StockStrategy"
        ]
      AnyclassStrategy ->
        [ mkNode "AnyclassStrategy"
        ]
      NewtypeStrategy ->
        [ mkNode "NewtypeStrategy"
        ]
      ViaStrategy s ->
        [ mkNode "ViaStrategy"
        , toHie $ TS (ResolvedScopes []) s
        ]
    where mkNode = makeNode "DerivStrategy" span

instance ToHie (Located OverlapMode) where
  toHie (L span _) = pure $ locOnly span

instance ToHie (LConDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ConDeclGADT{con_names=names, con_qvars=qvars, con_mb_cxt=ctx, con_args=args, con_res_ty=typ} ->
        [ mkNode "ConDeclGADT"
        , toHie $ map (C (Bind ModuleScope)) names
        , toHie $ RS rhsScope qvars
        , toHie ctx
        , toHie args
        , toHie typ
        ]
        where
          rhsScope = combineScopes ctxScope (combineScopes argsScope tyScope)
          ctxScope = maybe NoScope mkLScope ctx
          argsScope = condecl_scope args
          tyScope = mkLScope typ
      ConDeclH98{con_name=name, con_ex_tvs=qvars, con_mb_cxt=ctx, con_args=dets} ->
        [ mkNode "ConDeclH98"
        , toHie $ C (Bind ModuleScope) name
        , toHie $ map (\(RS sc a)-> TVS (ResolvedScopes []) sc a) $ listScopes rhsScope qvars
        , toHie ctx
        , toHie dets
        ]
        where
          rhsScope = combineScopes ctxScope argsScope
          ctxScope = maybe NoScope mkLScope ctx
          argsScope = condecl_scope dets
      XConDecl _ -> []
    where mkNode = makeNode "ConDecl" span
          condecl_scope args = case args of
            PrefixCon xs -> foldr combineScopes NoScope $ map mkLScope xs
            InfixCon a b -> combineScopes (mkLScope a) (mkLScope b)
            RecCon x -> mkLScope x

instance ToHie (Located [LConDeclField GhcRn]) where
  toHie (L span decls) = concatM $
    [ pure $ locOnly span
    , toHie decls
    ]

class HasLoc a where
  loc :: a -> SrcSpan

instance HasLoc thing => HasLoc (HsImplicitBndrs a thing) where
  loc (HsIB _ a) = loc a
  loc _ = noSrcSpan

instance HasLoc thing => HasLoc (HsWildCardBndrs a thing) where
  loc (HsWC _ a) = loc a
  loc _ = noSrcSpan

instance HasLoc (Located a) where
  loc (L l _) = l

instance HasLoc a => HasLoc [a] where
  loc [] = noSrcSpan
  loc xs = foldl1' combineSrcSpans $ map loc xs

instance (HasLoc a, HasLoc b) => HasLoc (FamEqn s a b) where
  loc (FamEqn _ a b _ c) = foldl1' combineSrcSpans [loc a, loc b, loc c]
  loc _ = noSrcSpan

instance HasLoc (HsDataDefn GhcRn) where
  loc def@(HsDataDefn{}) = loc $ dd_cons def -- Only used for data family instances, so we only need rhs
  loc _ = noSrcSpan

instance (HasLoc thing, ToHie (TScoped thing)) => ToHie (TScoped (HsImplicitBndrs GhcRn thing)) where
  toHie (TS sc (HsIB ibrn a)) = concatM $
      [ pure $ bindingsOnly span $ map (C $ ScopedTyVarBind (mkScope span) sc) $ hsib_vars ibrn
      , toHie $ TS sc a
      ]
    where span = loc a
  toHie (TS sc (XHsImplicitBndrs _)) = pure []

instance (HasLoc thing, ToHie (TScoped thing)) => ToHie (TScoped (HsWildCardBndrs GhcRn thing)) where
  toHie (TS sc (HsWC names a)) = concatM $
      [ pure $ bindingsOnly span $ map (C $ ScopedTyVarBind (mkScope span) sc) names
      , toHie $ TS sc a
      ]
    where span = loc a
  toHie (TS sc (XHsWildCardBndrs _)) = pure []

instance ToHie (LSig GhcRn) where
  toHie (L span sig) = concatM $ case sig of
      TypeSig _ names typ ->
        [ mkNode "TypeSig"
        , toHie $ map (C TyDecl) names
        , toHie $ TS (UnresolvedScope $ map unLoc names) typ
        ]
      PatSynSig _ names typ ->
        [ mkNode "PatSynSig"
        , toHie $ map (C TyDecl) names
        , toHie $ TS (UnresolvedScope $ map unLoc names) typ
        ]
      ClassOpSig _ _ names typ ->
        [ mkNode "ClassOpSig"
        , toHie $ map (C InstBind) names
        , toHie $ TS (ResolvedScopes []) typ
        ]
      IdSig _ _ -> []
      FixSig _ fsig ->
        [ mkNode "FixSig"
        , toHie $ L span fsig
        ]
      InlineSig _ name _ ->
        [ mkNode "InlineSig"
        , toHie $ (C Use) name
        ]
      SpecSig _ name typs _ ->
        [ mkNode "SpecSig"
        , toHie $ (C Use) name
        , toHie $ map (TS (ResolvedScopes [])) typs
        ]
      SpecInstSig _ _ typ ->
        [ mkNode "SpecInstSig"
        , toHie $ TS (ResolvedScopes []) typ
        ]
      MinimalSig _ _ form ->
        [ mkNode "MinimalSig"
        , toHie form
        ]
      SCCFunSig _ _ name mtxt ->
        [ mkNode "SCCFunSig"
        , toHie $ (C Use) name
        , pure $ maybe [] (locOnly . getLoc) mtxt
        ]
      CompleteMatchSig _ _ (L ispan names) typ ->
        [ mkNode "CompleteMatchSig"
        , pure $ locOnly ispan
        , toHie $ map (C Use) names
        , toHie $ fmap (C Use) typ
        ]
      XSig _ -> []
    where mkNode = makeNode "Sig" span

instance ToHie (LHsType GhcRn) where
  toHie x = toHie $ TS (ResolvedScopes []) x

instance ToHie (TScoped (LHsType GhcRn)) where
  toHie (TS tsc (L span t)) = concatM $ case t of
      HsForAllTy _ bndrs body ->
        [ mkNode "HsForAllTy"
        , toHie $ map (\(RS sc a) -> TVS tsc sc a)
            $ listScopes (mkScope $ getLoc body) bndrs
        , toHie body
        ]
      HsQualTy _ ctx body ->
        [ mkNode "HsQualTy"
        , toHie ctx
        , toHie body
        ]
      HsTyVar _ _ var ->
        [ mkNode "HsTyVar"
        , toHie $ C Use var
        ]
      HsAppTy _ a b ->
        [ mkNode "HsAppTy"
        , toHie a
        , toHie b
        ]
      HsFunTy _ a b ->
        [ mkNode "HsFunTy"
        , toHie a
        , toHie b
        ]
      HsListTy _ a ->
        [ mkNode "HsListTy"
        , toHie a
        ]
      HsTupleTy _ _ tys ->
        [ mkNode "HsTupleTy"
        , toHie tys
        ]
      HsSumTy _ tys ->
        [ mkNode "HsSymTy"
        , toHie tys
        ]
      HsOpTy _ a op b ->
        [ mkNode "HsOpTy"
        , toHie a
        , toHie $ C Use op
        , toHie b
        ]
      HsParTy _ a ->
        [ mkNode "HsParTy"
        , toHie a
        ]
      HsIParamTy _ ip ty ->
        [ mkNode "IParamTy"
        , toHie ip
        , toHie ty
        ]
      HsKindSig _ a b ->
        [ mkNode "HsKindSig"
        , toHie a
        , toHie b
        ]
      HsSpliceTy _ a ->
        [ mkNode "HsSpliceTy"
        , toHie $ L span a
        ]
      HsDocTy _ a _ ->
        [ mkNode "HsDocTy"
        , toHie a
        ]
      HsBangTy _ _ ty ->
        [ mkNode "HsBangTy"
        , toHie ty
        ]
      HsRecTy _ fields ->
        [ mkNode "HsRecTy"
        , toHie fields
        ]
      HsExplicitListTy _ _ tys ->
        [ mkNode "HsExplicitListTy"
        , toHie tys
        ]
      HsExplicitTupleTy _ tys ->
        [ mkNode "HsExplicitTupleTy"
        , toHie tys
        ]
      HsTyLit _ _ ->
        [ mkNode "HsTyLit"
        ]
      HsWildCardTy e ->
        [ mkNode "HsWildCardTy"
        , toHie e
        ]
      HsStarTy _ _ -> []
      XHsType _ -> []
    where mkNode = makeNode "HsType" span

instance ToHie HsWildCardInfo where
  toHie (AnonWildCard name) = toHie $ C Use name

instance ToHie (TVScoped (LHsTyVarBndr GhcRn)) where
  toHie (TVS tsc sc (L span bndr)) = concatM $ case bndr of
      UserTyVar _ var ->
        [ mkNode "UserTyVar"
        , toHie $ C (ScopedTyVarBind sc tsc) var
        ]
      KindedTyVar _ var kind ->
        [ mkNode "KindedTyVar"
        , toHie $ C (ScopedTyVarBind sc tsc) var
        , toHie kind
        ]
      XTyVarBndr _ -> []
    where mkNode = makeNode "HsTyVarBndr" span

instance ToHie (CScoped (LHsTyVarBndr GhcRn)) where
  toHie (CS quantsc varsc bodysc (L span bndr)) = concatM $ case bndr of
      UserTyVar _ var ->
        [ mkNode "UserTyVar"
        , toHie $ C (ClassTyVarScope quantsc varsc bodysc) var
        ]
      KindedTyVar _ var kind ->
        [ mkNode "KindedTyVar"
        , toHie $ C (ClassTyVarScope quantsc varsc bodysc) var
        , toHie kind
        ]
      XTyVarBndr _ -> []
    where mkNode = makeNode "HsTyVarBndr" span

instance ToHie (CScoped (LHsQTyVars GhcRn)) where
  toHie (CS quant sc body (HsQTvs _ vars)) =
    toHie $ map (\(RS varsc a) -> CS quant varsc body a) $ listScopes sc vars
  toHie (CS _ _ _ (XLHsQTyVars _)) = pure []

instance ToHie (RScoped (LHsQTyVars GhcRn)) where
  toHie (RS scope (HsQTvs _ vars)) =
    toHie $ map (\(RS sc a) -> TVS (ResolvedScopes []) sc a) $ listScopes scope vars
  toHie (RS _ (XLHsQTyVars _)) = pure []

instance ToHie (LHsContext GhcRn) where
  toHie (L span tys) = concatM $
      [ pure $ locOnly span
      , toHie tys
      ]

instance ToHie (LConDeclField GhcRn) where
  toHie (L span field) = concatM $ case field of
      ConDeclField _ fields typ _ ->
        [ mkNode "ConDeclField"
        , toHie fields
        , toHie typ
        ]
      XConDeclField _ -> []
    where mkNode = makeNode "HsConDeclField" span

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
  toHie (L span decl) = concatM $ case decl of
      SpliceDecl _ splice _ ->
        [ mkNode "SpliceDecl"
        , toHie splice
        ]
      XSpliceDecl _ -> []
    where mkNode = makeNode "SpliceDecl" span

instance ToHie (HsBracket a) where
  toHie _ = pure []

instance ToHie PendingRnSplice where
  toHie _ = pure []

instance ToHie PendingTcSplice where
  toHie _ = pure []

instance ToHie (LBooleanFormula (Located Name)) where
  toHie (L span form) = concatM $ case form of
      Var a ->
        [ mkNode "Var"
        , toHie $ C Use a
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
    where mkNode = makeNode "BooleanFormula" span

instance ToHie (Located HsIPName) where
  toHie (L span _) = makeNode "HsIPName" span "HsIPName"

instance ToHie (LHsExpr a) => ToHie (Located (HsSplice a)) where
  toHie (L span sp) = concatM $ case sp of
      HsTypedSplice _ _ _ expr ->
        [ mkNode "HsTypedSplice"
        , toHie expr
        ]
      HsUntypedSplice _ _ _ expr ->
        [ mkNode "HsUnTypedSplice"
        , toHie expr
        ]
      HsQuasiQuote _ _ _ ispan _ ->
        [ mkNode "HsQuasiQuote"
        , pure $ locOnly ispan
        ]
      HsSpliced _ _ _ ->
        [ mkNode "HsSpliced"
        ]
      XSplice _ -> []
    where mkNode = makeNode "HsSplice" span

instance ToHie (LRoleAnnotDecl GhcRn) where
  toHie (L span annot) = concatM $ case annot of
      RoleAnnotDecl _ var roles ->
        [ mkNode "RoleAnnotDecl"
        , toHie $ C Use var
        , concatMapM (pure . locOnly . getLoc) roles
        ]
      XRoleAnnotDecl _ -> []
    where mkNode = makeNode "RoleAnnotDecl" span

instance ToHie (LInstDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ClsInstD _ d ->
        [ mkNode "ClsInstD"
        , toHie $ L span d
        ]
      DataFamInstD _ d ->
        [ mkNode "DataFamInstD"
        , toHie $ L span d
        ]
      TyFamInstD _ d ->
        [ mkNode "TyFamInstD"
        , toHie $ L span d
        ]
      XInstDecl _ -> []
    where mkNode = makeNode "InstDecl" span

instance ToHie (LClsInstDecl GhcRn) where
  toHie (L span decl) = concatM
    [ toHie $ TS (ResolvedScopes [mkScope span]) $ cid_poly_ty decl
    , toHie $ fmap (FS ModuleScope) $ cid_binds decl
    , toHie $ cid_sigs decl
    , pure $ concatMap (locOnly . getLoc) $ cid_tyfam_insts decl
    , toHie $ cid_tyfam_insts decl
    , pure $ concatMap (locOnly . getLoc) $ cid_datafam_insts decl
    , toHie $ cid_datafam_insts decl
    , toHie $ cid_overlap_mode decl
    ]

instance ToHie (LDataFamInstDecl GhcRn) where
  toHie (L sp (DataFamInstDecl d)) = toHie $ TS (ResolvedScopes [mkScope sp]) d

instance ToHie (LTyFamInstDecl GhcRn) where
  toHie (L sp (TyFamInstDecl d)) = toHie $ TS (ResolvedScopes [mkScope sp]) d

instance ToHie (Context a) => ToHie (FScoped (RecordPatSynField a))where
  toHie (FS sp (RecordPatSynField a b)) = concatM $
    [ toHie $ C (Bind sp) a
    , toHie $ C Use b
    ]

instance ToHie (LDerivDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      DerivDecl _ typ strat overlap ->
        [ mkNode "DerivDecl"
        , toHie $ TS (ResolvedScopes []) typ
        , toHie strat
        , toHie overlap
        ]
      XDerivDecl _ -> []
    where mkNode = makeNode "DerivDecl" span

instance ToHie (LFixitySig GhcRn) where
  toHie (L span sig) = concatM $ case sig of
      FixitySig _ vars _ ->
        [ mkNode "FixitySig"
        , toHie $ map (C Use) vars
        ]
      XFixitySig _ -> []
    where mkNode = makeNode "FixitySig" span

instance ToHie (LDefaultDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      DefaultDecl _ typs ->
        [ mkNode "DefaultDecl"
        , toHie typs
        ]
      XDefaultDecl _ -> []
    where mkNode = makeNode "DefaultDecl" span

instance ToHie (LForeignDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ForeignImport {fd_name = name, fd_sig_ty = sig, fd_fi = fi} ->
        [ mkNode "ForeignImport"
        , toHie $ C (Bind ModuleScope) name
        , toHie $ TS (ResolvedScopes []) sig
        , toHie fi
        ]
      ForeignExport {fd_name = name, fd_sig_ty = sig, fd_fe = fe} ->
        [ mkNode "ForeignExport"
        , toHie $ C Use name
        , toHie $ TS (ResolvedScopes []) sig
        , toHie fe
        ]
      XForeignDecl _ -> []
    where mkNode = makeNode "ForeignDecl" span

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
  toHie (L span decl) = concatM $ case decl of
      Warnings _ _ warnings ->
        [ mkNode "Warning"
        , toHie warnings
        ]
      XWarnDecls _ -> []
    where mkNode = makeNode "WarnDecls" span

instance ToHie (LWarnDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      Warning _ vars _ ->
        [ mkNode "Warning"
        , toHie $ map (C Use) vars
        ]
      XWarnDecl _ -> []
    where mkNode = makeNode "WarnDecl" span

instance ToHie (LAnnDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      HsAnnotation _ _ prov expr ->
        [ mkNode "HsAnnotation"
        , toHie prov
        , toHie expr
        ]
      XAnnDecl _ -> []
    where mkNode = makeNode "AnnDecl" span

instance ToHie (Context (Located a)) => ToHie (AnnProvenance a) where
  toHie (ValueAnnProvenance a) = toHie $ C Use a
  toHie (TypeAnnProvenance a) = toHie $ C Use a
  toHie ModuleAnnProvenance = pure []

instance ToHie (LRuleDecls GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      HsRules _ _ rules ->
        [ mkNode "HsRules"
        , toHie rules
        ]
      XRuleDecls _ -> []
    where mkNode = makeNode "RuleDecls" span

instance ToHie (LRuleDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      HsRule _ rname _ bndrs exprA exprB ->
        [ mkNode "HsRule"
        , pure $ locOnly $ getLoc rname
        , toHie bndrs
        , toHie exprA
        , toHie exprB
        ]
      XRuleDecl _ -> []
    where mkNode = makeNode "RuleDecl" span

instance ToHie (LRuleBndr GhcRn) where
  toHie (L span bndr) = concatM $ case bndr of
      RuleBndr _ var ->
        [ mkNode "RuleBndr"
        , toHie $ C Use var
        ]
      RuleBndrSig _ var typ ->
        [ mkNode "RuleBndrSig"
        , toHie $ C Use var
        , toHie $ TS (ResolvedScopes []) typ
        ]
      XRuleBndr _ -> []
    where mkNode = makeNode "RuleBndr" span

instance ToHie (LImportDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ImportDecl { ideclName = name, ideclAs = as, ideclHiding = hidden } ->
        [ mkNode "ImportDecl"
        , toHie name
        , toHie as
        , maybe (pure []) goIE hidden
        ]
      XImportDecl _ -> []
    where
      mkNode = makeNode "ImportDecl" span
      goIE (_, (L sp liens)) = concatM $
        [ pure $ locOnly sp
        , toHie liens
        ]

instance ToHie (LIE GhcRn) where
  toHie (L span ie) = concatM $ case ie of
      IEVar _ n ->
        [ mkNode "IEVar"
        , toHie n
        ]
      IEThingAbs _ n ->
        [ mkNode "IEThingAbs"
        , toHie n
        ]
      IEThingAll _ n ->
        [ mkNode "IEThingAll"
        , toHie n
        ]
      IEThingWith _ n _ ns flds ->
        [ mkNode "IEThingWith"
        , toHie n
        , toHie ns
        , toHie flds
        ]
      IEModuleContents _ n ->
        [ mkNode "IEModuleContents"
        , toHie n
        ]
      IEGroup _ _ _ ->
        [ mkNode "IEGroup"
        ]
      IEDoc _ _ ->
        [ mkNode "IEDoc"
        ]
      IEDocNamed _ _ ->
        [ mkNode "IEDocNamed"
        ]
      XIE _ -> []
    where mkNode = makeNode "IE" span

instance ToHie (LIEWrappedName Name) where
  toHie (L span iewn) = concatM $ case iewn of
      IEName n ->
        [ mkNode "IEName"
        , toHie $ C Use n
        ]
      IEPattern p ->
        [ mkNode "IEPattern"
        , toHie $ C Use p
        ]
      IEType n ->
        [ mkNode "IEType"
        , toHie $ C Use n
        ]
    where mkNode = makeNode "IEWrappedName" span

instance ToHie (Located (FieldLbl Name)) where
  toHie (L span lbl) = concatM $ case lbl of
      FieldLabel _ _ n ->
        [ mkNode "FieldLabel"
        , toHie $ C Use $ L span n
        ]
    where mkNode = makeNode "FieldLbl" span
