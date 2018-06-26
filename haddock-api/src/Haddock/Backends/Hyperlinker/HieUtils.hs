module Haddock.Backends.Hyperlinker.HieUtils where

import Prelude hiding (span)
import Haddock.Backends.Hyperlinker.HieTypes
import SrcLoc
import Name
import GHC (Type)
import FastString (FastString)
import Control.Applicative
import Control.Monad
import Data.Monoid
import Data.Maybe
import Data.Either
import qualified Data.Map as M
import qualified Data.Set as S

astSpan :: HieAST a -> Span
astSpan (Node _ sp _) = sp

ppHies :: Show a => M.Map FastString (HieAST a) -> String
ppHies asts = unlines $
    [ M.foldrWithKey go "" asts
    , case validateScopes asts of
        [] -> "Scopes are valid"
        xs -> unlines $ "Scopes are invalid with errors: ":xs
    ]
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
    resolveNameScope dets = dets{identInfo = S.map resolveScope (identInfo dets)}
    resolveScope (TyVarBind sc (UnresolvedScope names Nothing)) =
      TyVarBind sc $ ResolvedScopes
        $ concatMap (\name -> map LocalScope $ maybeToList $ getNameBinding name asts) names
    resolveScope (TyVarBind sc (UnresolvedScope names (Just sp))) =
      TyVarBind sc $ ResolvedScopes
        $ concatMap (\name ->
            map LocalScope $ maybeToList $ getNameBindingInClass name sp asts) names
    resolveScope scope = scope
    go (Node info span children) = Node info' span $ map go children
      where
        info' = info { nodeIdentifiers = idents }
        idents = M.map resolveNameScope $ nodeIdentifiers info

getNameBinding :: Name -> M.Map FastString (HieAST a) -> Maybe Span
getNameBinding n asts = do
  (_,msp) <- getNameScopeAndBinding n asts
  msp

getNameScope :: Name -> M.Map FastString (HieAST a) -> Maybe [Scope]
getNameScope n asts = do
  (scopes,_) <- getNameScopeAndBinding n asts
  return scopes

getNameBindingInClass :: Name -> Span -> M.Map FastString (HieAST a) -> Maybe Span
getNameBindingInClass n sp asts = do
  ast <- M.lookup (srcSpanFile sp) asts
  getFirst $ foldMap First $ do
    child <- flattenAst ast
    dets <- maybeToList
      $ M.lookup (Right n) $ nodeIdentifiers $ nodeInfo child
    let binding = getFirst $ foldMap (First . getBindSiteFromContext) (identInfo dets)
    return binding

getNameScopeAndBinding :: Name -> M.Map FastString (HieAST a) -> Maybe ([Scope], Maybe Span)
getNameScopeAndBinding n asts = case nameSrcSpan n of
  RealSrcSpan sp -> do -- @Maybe
    ast <- M.lookup (srcSpanFile sp) asts
    defNode <- selectLargestContainedBy sp ast
    getFirst $ foldMap First $ do -- @[]
      node <- flattenAst defNode
      dets <- maybeToList
        $ M.lookup (Right n) $ nodeIdentifiers $ nodeInfo node
      scopes <- maybeToList $ foldMap getScopeFromContext (identInfo dets)
      let binding = getFirst $ foldMap (First . getBindSiteFromContext) (identInfo dets)
      return $ Just (scopes, binding)
  _ -> Nothing

getScopeFromContext :: ContextInfo -> Maybe [Scope]
getScopeFromContext (ValBind _ sc _) = Just [sc]
getScopeFromContext (PatBindScope a b _) = Just [a, b]
getScopeFromContext (ClassTyDecl _) = Just [ModuleScope]
getScopeFromContext (Decl _ _) = Just [ModuleScope]
getScopeFromContext (TyVarBind a (ResolvedScopes xs)) = Just $ a:xs
getScopeFromContext (TyVarBind a _) = Just [a]
getScopeFromContext _ = Nothing

getBindSiteFromContext :: ContextInfo -> Maybe Span
getBindSiteFromContext (ValBind _ _ sp) = sp
getBindSiteFromContext (PatBindScope _ _ sp) = sp
getBindSiteFromContext _ = Nothing

flattenAst :: HieAST a -> [HieAST a]
flattenAst n =
  n : concatMap flattenAst (nodeChildren n)

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

validateScopes :: M.Map FastString (HieAST a) -> [String]
validateScopes asts = foldMap go asts
  where
    go ast = do
      child <- flattenAst ast
      let nodeIdents = nodeIdentifiers $ nodeInfo child
      ident <- rights $ M.keys nodeIdents
      guard (any isOccurrence $ identInfo $ nodeIdents M.! Right ident)
      case getNameScope ident asts of
        Nothing
          | definedInAsts asts ident && notDerivingJunk ident ->
            [ "Can't resolve scopes for"
            , "Name", show ident, "at position", show (astSpan child)
            , "defined at", show (nameSrcSpan ident)]
          | otherwise -> []
        Just scopes ->
          if any (`scopeContainsSpan` (astSpan child)) scopes
          then []
          else return $ unwords $
            [ "Name", show ident, "at position", show (astSpan child)
            , "doesn't occur in calculated scope", show scopes]

notDerivingJunk :: Name -> Bool
notDerivingJunk n = x /= "c" && x /= "C"
  where x = (take 1 $ reverse $ takeWhile (/='$') $ reverse $ getOccString n)

definedInAsts :: M.Map FastString (HieAST a) -> Name -> Bool
definedInAsts asts n = case nameSrcSpan n of
  RealSrcSpan sp -> srcSpanFile sp `elem` M.keys asts
  _ -> False

isOccurrence :: ContextInfo -> Bool
isOccurrence Use = True
isOccurrence _ = False

scopeContainsSpan :: Scope -> Span -> Bool
scopeContainsSpan NoScope _ = False
scopeContainsSpan ModuleScope _ = True
scopeContainsSpan (LocalScope a) b = a `containsSpan` b

-- | One must contain the other. Leaf nodes cannot contain anything
combineAst :: Show a => HieAST a -> HieAST a -> HieAST a
combineAst a@(Node aInf aSpn xs) b@(Node bInf bSpn ys)
  | aSpn == bSpn = Node (aInf <> bInf) aSpn (mergeAsts xs ys)
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
simpleNodeInfo cons typ = NodeInfo (S.singleton (cons, typ)) Nothing Nothing M.empty

locOnly :: SrcSpan -> [HieAST a]
locOnly (RealSrcSpan span) =
  [Node mempty span []]
locOnly _ = []

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

makeNode :: Applicative m => String -> SrcSpan -> String -> m [HieAST a]
makeNode typ (RealSrcSpan span) cons = pure [Node (simpleNodeInfo cons typ) span []]
makeNode _ _ _ = pure []

makeTypeNode :: String -> String -> SrcSpan -> Type -> [HieAST Type]
makeTypeNode cons typ spn etyp = case spn of
  RealSrcSpan span ->
    [Node (NodeInfo (S.singleton (cons,typ)) Nothing (Just etyp) M.empty) span []]
  _ -> []

