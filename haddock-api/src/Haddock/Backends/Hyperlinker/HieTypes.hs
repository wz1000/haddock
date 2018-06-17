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
    = RtkVar GHC.Name ContextInfo
    | RtkModule GHC.ModuleName
    deriving (Eq)

type TypeIndex = Int

data ContextInfo =
    Use
  | InstBind
  | TyDecl
  | Bind Scope
  | PatBindScope Scope Scope
  | ClassTyVarScope Scope Scope Scope
  | ScopedTyVarBind Scope TyVarScope
    deriving (Eq, Show)

data Scope =
    ModuleScope
  | LocalScope Span
  | NoScope
    deriving (Eq, Show)

data TyVarScope =
    ResolvedScope Scope
  | UnresolvedScope Name.Name
    deriving (Eq, Show)

ppHie :: Show a => HieAST a -> String
ppHie = go 0
  where
    pad n = replicate n ' '
    go n (Node inf sp children) = unwords
      [ pad n
      , "Node"
      , show sp
      , show inf
      , "\n" ++ concatMap (go (n+2)) children
      ]

data HieAST a =
  Node
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
    , tokenInfo :: Maybe TokenType
    , tokenDetails :: [TokenDetails]
    } deriving Show

deriving instance Show TokenDetails

instance Show Name.Name where
  show = Name.nameStableString
instance Show GHC.Type where
  show = GHC.showSDocUnsafe . GHC.ppr
instance Show GHC.ModuleName where
  show = Module.moduleNameString
