{-# LANGUAGE OverloadedStrings #-}
module Haddock.Backends.Hyperlinker.HieAst (enrichHie) where

import qualified GHC
import Bag
import SrcLoc (containsSpan, srcSpanStartCol, srcSpanStartLine, srcSpanEndCol, srcSpanEndLine, srcSpanFile, mkRealSrcSpan, mkRealSrcLoc)

import Haddock.Backends.Hyperlinker.Types

import Control.Applicative
import Prelude hiding (span)

astSpan :: HieAST -> Span
astSpan (Leaf x) = htkSpan x
astSpan (Node _ sp _) = sp

-- | One must contain the other. Leaf nodes cannot contain anything
combineAst :: HieAST -> HieAST -> HieAST
combineAst (Leaf (HieToken inf sp aDet aTyp)) (Leaf (HieToken _ _ bDet bTyp)) = 
  Leaf $ HieToken inf sp (aDet <|> bDet) (aTyp <|> bTyp) 
-- ^ Since one must contain the other, and leaf nodes cannot contain anything, we assume they are the same token
combineAst a b@(Leaf _) = combineAst b a
combineAst a@(Node aInf aSpn xs) b@(Node bInf bSpn ys)
  | aSpn == bSpn = Node (aInf ++ bInf) aSpn (mergeAsts xs ys)
  | aSpn `containsSpan` bSpn = combineAst b a
combineAst a (Node xs span children) = Node xs span (insertAst a children) -- a is a Leaf node or is contained in span

-- | Insert an AST in a sorted list of disjoint Asts
insertAst :: HieAST -> [HieAST] -> [HieAST]
insertAst x xs = mergeAsts [x] xs

-- Merge two sorted, disjoint lists of ASTs, combining when necessary
mergeAsts :: [HieAST] -> [HieAST] -> [HieAST]
mergeAsts xs [] = xs
mergeAsts [] ys = ys
mergeAsts xs@(a:as) ys@(b:bs)
  | astSpan a `containsSpan` astSpan b = mergeAsts (combineAst a b : as) bs
  | astSpan b `containsSpan` astSpan a = mergeAsts as (combineAst a b : bs)
  | astSpan a `rightOf` astSpan b = b : mergeAsts xs bs
  | astSpan a `leftOf`  astSpan b = a : mergeAsts as ys
  | otherwise = error $ "mergeAsts: Spans overlapping " ++ show a ++ " and " ++ show b

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
mergeSortAsts :: [HieAST] -> [HieAST]
mergeSortAsts = go . map pure
  where
    go :: [[HieAST]] -> [HieAST]
    go [] = []
    go [xs] = xs
    go xss = go (mergePairs xss)
    mergePairs :: [[HieAST]] -> [[HieAST]]
    mergePairs [] = []
    mergePairs [xs] = [xs]
    mergePairs (xs:ys:xss) = mergeAsts xs ys : mergePairs xss

enrichHie :: GHC.RenamedSource -> [Token] -> HieAST
enrichHie src toks = Node ["Module"] spanFile (go src)
  where 
    spanFile = mkRealSrcSpan (mkRealSrcLoc "" 1 1) (mkRealSrcLoc "" 1 1)

    toHieToken (Token inf _ span) = Leaf (HieToken inf span Nothing Nothing)

    varDecl (GHC.L (GHC.RealSrcSpan span) name) = [Leaf $ HieToken TkIdentifier span (Just $ RtkDecl name) Nothing]
    varDecl _ = []

    varBind (GHC.L (GHC.RealSrcSpan span) name) = [Leaf $ HieToken TkIdentifier span (Just $ RtkBind name) Nothing]
    varBind _ = []
    
    varUse (GHC.L (GHC.RealSrcSpan span) name) = [Leaf $ HieToken TkIdentifier span (Just $ RtkVar name) Nothing]
    varUse _ = []

    go :: GHC.RenamedSource -> [HieAST]
    go (hsGrp, _, _, _) = mergeSortAsts $ (goGroup hsGrp) ++ (map toHieToken toks)

    goGroup hsGrp = goTopVals (GHC.hs_valds hsGrp)

    goTopVals = goVals varDecl
    goLocalVals = goVals varBind
    
    goVals var (GHC.ValBindsIn binds sigs) = mergeSortAsts (concatMap (goBind var) $ bagToList binds) 
    goVals var (GHC.ValBindsOut binds sigs) = mergeSortAsts (concatMap (goBind var) $ concatMap (bagToList . snd) binds)

    goBind var (GHC.L (GHC.RealSrcSpan span) bind) =  case bind of 
      GHC.FunBind id matches _ _ _ -> [Node ["FunBind","HsBindLR"] span $ (var id) ++ (goMatches matches)]
      GHC.PatBind lhs rhs _ _ _ -> [Node ["PatBind","HsBindLR"] span $ (goPat' var lhs) ++ (goGRHSs rhs)]
      _ -> []
    goBind _ _ = []

    goMatches (GHC.MG (GHC.L (GHC.RealSrcSpan span) alts) _ _ _) = [Node ["Alts","MatchGroup"] span $ concatMap goAlts alts]
    goMatches _ = []

    goAlts (GHC.L (GHC.RealSrcSpan span) (GHC.Match _ pats grhss)) = 
      [Node ["Match","Match"] span $ mergeSortAsts $ concatMap goPat pats ++ goGRHSs grhss]
    goAlts _ = []
    
    goPat = goPat' varBind

    goPat' var (GHC.L (GHC.RealSrcSpan pspan) pat) = case pat of
        GHC.VarPat lname -> mkNode "VarPat" $ var lname
        GHC.LazyPat p -> mkNode "LazyPat" $ goPat p
        GHC.AsPat lname lpat -> mkNode "AsPat" $ (var lname) ++ (goPat' var lpat)
        GHC.ParPat pat -> mkNode "ParPat" $ goPat' var pat
        GHC.BangPat pat -> mkNode "BangPat" $ goPat' var pat
        GHC.ListPat pats _ _ -> mkNode "ListPat" $ concatMap (goPat' var) pats
        GHC.TuplePat pats _ _ -> mkNode "TuplePat" $ concatMap (goPat' var) pats
        GHC.SumPat pat _ _ _ -> mkNode "SumPat" $ goPat' var pat
        GHC.PArrPat pats _ -> mkNode "PArrPat" $ concatMap (goPat' var) pats
        GHC.ConPatIn c dets -> mkNode "ConPatIn" $ (varUse c) ++ goConDets dets
        GHC.ViewPat expr pat _ -> mkNode "ViewPat" $ (goExpr expr) ++ (goPat' var pat)
        GHC.SplicePat splice -> mkNode "SplicePat" $ goSplice splice
        GHC.LitPat _ -> mkNode "LitPat" []
        GHC.NPat _ _ _ _ -> mkNode "NPat" []
        GHC.NPlusKPat lname _ _ _ _ _ -> mkNode "NPlusKPat" $ var lname
        GHC.SigPatIn pat typ -> mkNode "SigPatIn" $ (goPat' var pat) ++ (goSigWcType typ)
        _ -> []
      where mkNode cons children = pure $ Node [cons,"Pat"] pspan children
    goPat' _ _ = []

    goGRHSs (GHC.GRHSs grhss binds) = (concatMap goGRHS grhss) ++ (goLocalBinds binds)

    goGRHS (GHC.L (GHC.RealSrcSpan span) (GHC.GRHS guards body)) = 
      pure $ Node ["GRHS","GRHS"] span $ mergeSortAsts $ (concatMap goStmt guards) ++ (goExpr body)
    goGRHS _ = []

    goExpr (GHC.L (GHC.RealSrcSpan span) expr) = case expr of
        GHC.HsVar v -> mkNode "HsVar" $ varUse v
        GHC.HsLam mg -> mkNode "HsLam" $ goMatches mg
        GHC.HsLamCase mg -> mkNode "HsLamCase" $ goMatches mg
        GHC.HsApp a b -> mkNode "HsApp" $ (goExpr a) ++ (goExpr b)
        GHC.HsAppType expr typ -> mkNode "HsAppType" $ (goExpr expr) ++ (goWcType typ)
        GHC.HsAppTypeOut expr typ -> mkNode "HsAppType" $ (goExpr expr) ++ (goWcType typ)
        GHC.OpApp a b _ c -> mkNode "OpApp" $ mergeSortAsts $ (goExpr a) ++ (goExpr b) ++ (goExpr c)
        GHC.NegApp a _ -> mkNode "NegApp" $ goExpr a
        GHC.HsPar a -> mkNode "HsPar" $ goExpr a
        GHC.SectionL a b -> mkNode "SectionL" $ mergeSortAsts $ (goExpr a) ++ (goExpr b)
        GHC.SectionR a b -> mkNode "SectionR" $ mergeSortAsts $ (goExpr a) ++ (goExpr b)
        GHC.ExplicitTuple args _ -> mkNode "ExplicitTyple" $ concatMap goTupArg args
        GHC.ExplicitSum _ _ expr _ -> mkNode "ExplicitSum" $ goExpr expr
        GHC.HsCase expr matches -> mkNode "HsCase" $ (goExpr expr) ++ (goMatches matches)
        GHC.HsIf _ a b c -> mkNode "HsIf" $ (goExpr a) ++ (goExpr b) ++ (goExpr c)
        GHC.HsMultiIf _ grhss -> mkNode "HsMultiIf" $ concatMap goGRHS grhss
        GHC.HsLet binds expr -> mkNode "HsLet" $ (goLocalBinds binds) ++ (goExpr expr)
        GHC.HsDo _ (GHC.L (GHC.RealSrcSpan dspan) stmts) _ -> 
          mkNode "HsDo" $ pure $ Node ["DoStmts"] dspan $ concatMap goStmt stmts
        GHC.ExplicitList _ _ exprs -> mkNode "ExplicitList" $ concatMap goExpr exprs
        GHC.ExplicitPArr _ exprs -> mkNode "ExplicitPArr" $ concatMap goExpr exprs
        GHC.RecordCon name _ _ binds -> mkNode "RecordCon" $ (varUse name) ++ (goRecordBinds binds)
        GHC.RecordUpd expr upds _ _ _ _ -> mkNode "RecordUpd" $ (goExpr expr) ++ (goRecordUpds upds)
        GHC.ExprWithTySig expr sig -> mkNode "ExprWithTySig" $ (goExpr expr) ++ (goSigWcType sig)
        GHC.ExprWithTySigOut expr sig -> mkNode "ExprWithTySigOut" $ (goExpr expr) ++ (goSigWcType sig)
        GHC.ArithSeq _ _ info -> mkNode "ArithSeq" $ goArithSeqInfo info
        GHC.PArrSeq _ info -> mkNode "PArrSeq" $ goArithSeqInfo info
        GHC.HsSCC _ _ expr -> mkNode "HsSCC" $ goExpr expr
        GHC.HsCoreAnn _ _ expr -> mkNode "HsCoreAnn" $ goExpr expr
        GHC.HsProc pat cmdtop -> mkNode "HsProc" $ (goPat pat) ++ (goCmdTop cmdtop)
        GHC.HsStatic _ expr -> mkNode "HsStatic" $ goExpr expr
        GHC.HsArrApp a b _ _ _ -> mkNode "HsArrApp" $ (goExpr a) ++ (goExpr b)
        GHC.HsArrForm expr _ cmdtops -> mkNode "HsArrForm" $ (goExpr expr) ++ (concatMap goCmdTop cmdtops)
        GHC.HsTick _ expr -> mkNode "HsTick" $ goExpr expr
        GHC.HsBinTick _ _ expr -> mkNode "HsBinTick" $ goExpr expr
        GHC.HsTickPragma _ _ _ expr -> mkNode "HsTickPragma" $ goExpr expr
        GHC.EAsPat id expr -> mkNode "EAsPat" $ (varUse id) ++ (goExpr expr)
        GHC.EViewPat a b -> mkNode "EViewPat" $ (goExpr a) ++ (goExpr b)
        GHC.ELazyPat expr -> mkNode "ELazyPat" $ goExpr expr
        _ -> []
      where mkNode cons children = pure $ Node [cons,"HsExpr"] span children
    goExpr _ = []

    goTupArg (GHC.L (GHC.RealSrcSpan span) arg) = case arg of
      GHC.Present expr -> pure $ Node ["Present","HsTupArg"] span $ goExpr expr
      GHC.Missing _ -> pure $ Node ["Missing","HsTupArg"] span []
    goTupArg _ = []

    goStmt (GHC.L (GHC.RealSrcSpan span) stmt) = case stmt of
        GHC.LastStmt body _ _ -> mkNode "LastStmt" $ goExpr body
        GHC.BindStmt pat body _ _ _ -> mkNode "BindStmt" $ (goPat pat) 
        GHC.ApplicativeStmt stmts _ _ -> mkNode "ApplicativeStmt" $ mergeSortAsts $ concatMap (goApplicativeArg . snd) stmts
        GHC.BodyStmt body _ _ _ -> mkNode "BodyStmt" $ goExpr body
        GHC.LetStmt binds -> mkNode "LetStmt" $ goLocalBinds binds
        GHC.ParStmt parstmts _ _ _ -> 
          mkNode "ParStmt" $ concatMap (\(GHC.ParStmtBlock stmts _ _) -> concatMap goStmt stmts) parstmts
        _ -> []
      where mkNode cons children = pure $ Node [cons,"StmtLR"] span children
    goStmt _ = []

    goLocalBinds (GHC.L (GHC.RealSrcSpan span) binds) = case binds of
        GHC.EmptyLocalBinds -> mkNode "EmptyLocalBinds" []
        GHC.HsIPBinds ipbinds -> mkNode "HsIPBinds" []
        GHC.HsValBinds valBinds -> mkNode "HsValBinds" $ goLocalVals valBinds
      where mkNode cons children = pure $ Node [cons, "HsLocalBindsLR"] span children

    goRecordUpds _ = []

    goRecordBinds _ = []

    goSigWcType _ = []

    goWcType _ = []

    goApplicativeArg _ = []

    goConDets _ = []

    goSplice _ = []

    goCmdTop _ = []

    goArithSeqInfo _ = []

