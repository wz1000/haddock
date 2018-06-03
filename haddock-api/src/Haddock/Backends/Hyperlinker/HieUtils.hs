module Haddock.Backends.Hyperlinker.HieUtils where

import Prelude hiding (span)
import Haddock.Backends.Hyperlinker.Types
import SrcLoc
import Control.Applicative

astSpan :: HieAST a -> Span
astSpan (Leaf x) = htkSpan x
astSpan (Node _ sp _) = sp

validAst :: HieAST a -> Bool
validAst (Leaf _ ) = True
validAst (Node _ span children) = all validAst children
                               && all ((span `containsSpan`) . astSpan) children
                               && astSorted children
  where astSorted [] = True
        astSorted [_] = True
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
insertAst x = mergeAsts [x]

-- Merge two sorted, disjoint lists of ASTs, combining when necessary
mergeAsts :: [HieAST a] -> [HieAST a] -> [HieAST a]
mergeAsts xs [] = xs
mergeAsts [] ys = ys
mergeAsts xs@(a:as) ys@(b:bs)
  | astSpan a `containsSpan` astSpan b = mergeAsts (combineAst a b : as) bs
  | astSpan b `containsSpan` astSpan a = mergeAsts as (combineAst a b : bs)
  | astSpan a `rightOf` astSpan b = b : mergeAsts xs bs
  | astSpan a `leftOf`  astSpan b = a : mergeAsts as ys
  | otherwise = error $ "mergeAsts: Spans overlapping " ++ show (astSpan a) ++ " and " ++ show (astSpan b)

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
