{-# LANGUAGE StandaloneDeriving #-}
module Haddock.Backends.Hyperlinker.HieTypes where


import qualified GHC
import qualified Outputable as GHC
import qualified Name
import qualified Module

import Data.Array (Array)

type Position = GHC.RealSrcLoc
type Span = GHC.RealSrcSpan

data TokenType
    = TkIdentifier
    | TkKeyword
    | TkString
    | TkChar
    | TkNumber
    | TkOperator
    | TkGlyph
    | TkSpecial
    | TkSpace
    | TkComment
    | TkCpp
    | TkPragma
    | TkUnknown
    deriving (Show, Eq)

data TokenDetails
    = RtkVar GHC.Name
    | RtkType GHC.Name
    | RtkBind GHC.Name
    | RtkDecl GHC.Name
    | RtkModule GHC.ModuleName
    deriving (Eq)

data HieToken a = HieToken
    { htkSpan :: Span
    , htkInfo :: Maybe TokenType
    , htkDetails :: Maybe TokenDetails
    } deriving Show

type TypeIndex = Int

ppHie :: Show a => HieAST a -> String
ppHie = go 0
  where
    pad n = replicate n ' '
    go n (Leaf a) = pad n ++ show a ++ "\n"
    go n (Node inf sp children) = pad n ++ "Node " ++ show sp ++ show inf ++ "\n" ++ concatMap (go (n+2)) children

data HieAST a =
    Leaf (HieToken a)
  | Node
    { nodeInfo :: NodeInfo a
    , nodeSpan :: Span
    , nodeChildren :: [HieAST a]
    } deriving Show

data HieFile = HieFile
    { hieVersion :: String
    , ghcVersion :: String
    , hsFile     :: String
    , hieTypes   :: Array TypeIndex GHC.Type
    , hieAST     :: HieAST TypeIndex
    , hsSrc      :: String
    }

data NodeInfo a = NodeInfo 
    { nodeAnnotations :: [(String,String)] -- Constr, Type
    , nodeType :: Maybe a
    } deriving Show

deriving instance Show TokenDetails

instance Show Name.Name where
  show = Name.nameStableString
instance Show GHC.Type where
  show = GHC.showSDocUnsafe . GHC.ppr
instance Show GHC.ModuleName where
  show = Module.moduleNameString
