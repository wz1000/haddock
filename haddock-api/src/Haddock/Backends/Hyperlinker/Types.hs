module Haddock.Backends.Hyperlinker.Types where


import qualified GHC
import qualified Name
import qualified Module

import Data.Map (Map)
import Data.Array (Array)

data HieToken a = HieToken
    { htkSpan :: Span
    , htkInfo :: Maybe TokenType
    , htkDetails :: Maybe TokenDetails
    , htkType :: Maybe a
    } deriving Show

type TypeIndex = Int

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

data Token = Token
    { tkType :: TokenType
    , tkValue :: String
    , tkSpan :: {-# UNPACK #-} !Span
    }
    deriving (Show)

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


data RichToken = RichToken
    { rtkToken :: Token
    , rtkDetails :: Maybe TokenDetails
    }

data TokenDetails
    = RtkVar GHC.Name
    | RtkType GHC.Name
    | RtkBind GHC.Name
    | RtkDecl GHC.Name
    | RtkModule GHC.ModuleName
    deriving (Eq, Show)

instance Show Name.Name where
  show = Name.nameStableString
instance Show GHC.ModuleName where
  show = Module.moduleNameString


rtkName :: TokenDetails -> Either GHC.Name GHC.ModuleName
rtkName (RtkVar name) = Left name
rtkName (RtkType name) = Left name
rtkName (RtkBind name) = Left name
rtkName (RtkDecl name) = Left name
rtkName (RtkModule name) = Right name


-- | Path for making cross-package hyperlinks in generated sources.
--
-- Used in 'SrcMap' to determine whether module originates in current package
-- or in an external package.
data SrcPath
    = SrcExternal FilePath
    | SrcLocal

-- | Mapping from modules to cross-package source paths.
type SrcMap = Map GHC.Module SrcPath

