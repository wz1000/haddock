module Haddock.Backends.Hyperlinker.HieUtils where

import Prelude hiding (span)
import Haddock.Backends.Hyperlinker.HieTypes
import SrcLoc
import Name
import FastString (FastString)
import Control.Applicative
import Control.Monad
import Data.Monoid
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

astSpan :: HieAST a -> Span
astSpan (Node _ sp _) = sp

ppHies :: (Show k, Show a) => M.Map k (HieAST a) -> String
ppHies = M.foldrWithKey go ""
  where
    go k a rest = unlines $
      [ "File: " ++ show k
      , ppHie a
      , show $ validAst a
      , rest
      ]

resolveTyVarScopes :: M.Map FastString (HieAST a) -> M.Map FastString (HieAST a)
resolveTyVarScopes asts = M.map go asts
  where
    go ast = resolveTyVarScopeLocal ast asts

resolveTyVarScopeLocal :: HieAST a -> M.Map FastString (HieAST a) -> HieAST a
resolveTyVarScopeLocal ast asts = go ast
  where
    resolveNameScope (typ, ScopedTyVarBind sc tysc) =
      (typ, ScopedTyVarBind sc (resolveScope tysc))
    resolveNameScope x = x
    resolveScope tysc@(UnresolvedScope names) =
      ResolvedScopes $ concatMap (\name -> map LocalScope $ maybeToList $ getNameBinding name asts) names
    resolveScope tysc = tysc
    go (Node info span children) = Node info' span $ map go children
      where
        info' = info { nodeIdentifiers = idents }
        idents = case nodeIdentifiers info of
          (names, mdl) -> (names', mdl)
            where
              names' = M.map resolveNameScope names

getNameBinding :: Name -> M.Map FastString (HieAST a) -> Maybe Span
getNameBinding n asts = case nameSrcSpan n of
  RealSrcSpan sp -> do -- @Maybe
    ast <- M.lookup (srcSpanFile sp) asts
    let bindCond = any ((=="HsBindLR") . snd) . S.elems . nodeAnnotations . nodeInfo
    defNode <- smallestContainingSatisfying sp bindCond ast
    return $ astSpan defNode
  _ -> Nothing

getNameScope :: Name -> M.Map FastString (HieAST a) -> Maybe [Scope]
getNameScope n asts = case nameSrcSpan n of
  RealSrcSpan sp -> do -- @Maybe
    ast <- M.lookup (srcSpanFile sp) asts
    defNode <- selectLargestContainedBy sp ast
    getFirst $ foldMap First $ do -- @[]
      node <- flattenAst defNode
      (_, inf) <- maybeToList
        $ M.lookup n $ fst $ nodeIdentifiers $ nodeInfo node
      return $ case inf of
        Bind sc -> Just [sc]
        PatBindScope a b -> Just [a, b]
        ClassTyVarScope a b c -> Just [a,b,c]
        ScopedTyVarBind a (ResolvedScopes xs) -> Just $ a:xs
        ScopedTyVarBind a _ -> Just [a]
        _ -> Nothing
  _ -> Nothing

flattenAst :: HieAST a -> [HieAST a]
flattenAst n =
  n{nodeChildren = []} : concatMap flattenAst (nodeChildren n)

smallestContainingSatisfying :: Span -> (HieAST a -> Bool) -> HieAST a -> Maybe (HieAST a)
smallestContainingSatisfying sp cond node
  | astSpan node `containsSpan` sp = getFirst $ mconcat
      [ foldMap (First . smallestContainingSatisfying sp cond) $ nodeChildren node
      , First $ if cond node then Just node else Nothing
      ]
  | sp `containsSpan` astSpan node = Nothing
  | otherwise = Nothing

selectLargestContainedBy :: Span -> HieAST a -> Maybe (HieAST a)
selectLargestContainedBy sp node
  | sp `containsSpan` astSpan node = Just node
  | astSpan node `containsSpan` sp =
      getFirst $ foldMap (First . selectLargestContainedBy sp) $ nodeChildren node
  | otherwise = Nothing

selectSmallestContaining :: Span -> HieAST a -> Maybe (HieAST a)
selectSmallestContaining sp node
  | astSpan node `containsSpan` sp = getFirst $ mconcat
      [ foldMap (First . selectSmallestContaining sp) $ nodeChildren node
      , First (Just node)
      ]
  | sp `containsSpan` astSpan node = Nothing
  | otherwise = Nothing

validAst :: HieAST a -> Either String ()
validAst (Node _ span children) = do
  checkContainment children
  checkSorted children
  forM_ children validAst
  where
    checkSorted [] = return ()
    checkSorted [_] = return ()
    checkSorted (x:y:xs)
      | astSpan x `leftOf` astSpan y = checkSorted (y:xs)
      | otherwise = Left $ unwords
          [ show $ astSpan x
          , "is not to the left of"
          , show $ astSpan y
          ]
    checkContainment [] = return ()
    checkContainment (x:xs)
      | span `containsSpan` (astSpan x) = checkContainment xs
      | otherwise = Left $ unwords
          [ show $ span
          , "does not contain"
          , show $ astSpan x
          ]

combineIdentifierDetails :: IdentifierDetails a -> IdentifierDetails a -> IdentifierDetails a
combineIdentifierDetails (mt1, ci) (mt2, _) = (mt1 <|> mt2, ci)

combineNodeIdentifiers :: NodeIdentifiers a -> NodeIdentifiers a -> NodeIdentifiers a
combineNodeIdentifiers (names1, mdl1) (names2, mdl2) = (names, mdl1 <|> mdl2)
  where
    names = M.unionWith combineIdentifierDetails names1 names2

combineNodeInfo :: NodeInfo a -> NodeInfo a -> NodeInfo a
combineNodeInfo (NodeInfo as ta ai ad) (NodeInfo bs tb bi bd) =
  NodeInfo (S.union as bs) (ta <|> tb) (ai <|> bi) (combineNodeIdentifiers ad bd)

-- | One must contain the other. Leaf nodes cannot contain anything
combineAst :: Show a => HieAST a -> HieAST a -> HieAST a
combineAst a@(Node aInf aSpn xs) b@(Node bInf bSpn ys)
  | aSpn == bSpn = Node (combineNodeInfo aInf bInf) aSpn (mergeAsts xs ys)
  | aSpn `containsSpan` bSpn = combineAst b a
combineAst a (Node xs span children) = Node xs span (insertAst a children)

-- | Insert an AST in a sorted list of disjoint Asts
insertAst :: Show a => HieAST a -> [HieAST a] -> [HieAST a]
insertAst x = mergeAsts [x]

-- Merge two sorted, disjoint lists of ASTs, combining when necessary
mergeAsts :: Show a => [HieAST a] -> [HieAST a] -> [HieAST a]
mergeAsts xs [] = xs
mergeAsts [] ys = ys
mergeAsts xs@(a:as) ys@(b:bs)
  | astSpan a `containsSpan` astSpan b = mergeAsts (combineAst a b : as) bs
  | astSpan b `containsSpan` astSpan a = mergeAsts as (combineAst a b : bs)
  | astSpan a `rightOf` astSpan b = b : mergeAsts xs bs
  | astSpan a `leftOf`  astSpan b = a : mergeAsts as ys
  | otherwise = error $ unwords $
      [ "mergeAsts: Spans overlapping"
      , show a
      , "and"
      , show b
      ]

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
mergeSortAsts :: Show a => [HieAST a] -> [HieAST a]
mergeSortAsts = go . map pure
  where
    go [] = []
    go [xs] = xs
    go xss = go (mergePairs xss)
    mergePairs [] = []
    mergePairs [xs] = [xs]
    mergePairs (xs:ys:xss) = mergeAsts xs ys : mergePairs xss

simpleNodeInfo :: String -> String -> NodeInfo a
simpleNodeInfo cons typ = NodeInfo (S.singleton (cons, typ)) Nothing Nothing (M.empty, Nothing)
