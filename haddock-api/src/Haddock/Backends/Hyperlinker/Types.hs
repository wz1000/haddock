module Haddock.Backends.Hyperlinker.Types where


import qualified GHC
import qualified Outputable as GHC
import qualified Name
import qualified Module

import Data.Map (Map)
import Data.Array (Array)

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
    deriving (Eq)

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

