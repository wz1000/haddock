{-# LANGUAGE StandaloneDeriving #-}
module Haddock.Backends.Hyperlinker.HieTypes where


import qualified GHC
import qualified Outputable as GHC
import qualified Name
import qualified Module

import Data.Array (Array)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Monoid
import Control.Applicative ((<|>))

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

type TypeIndex = Int

data ContextInfo =
    Use
  | IEThing -- Import or Export
  | TyDecl
  | ValBind BindType Scope (Maybe Span) -- Span of entire binding
  | PatBindScope Scope Scope (Maybe Span) -- Span of entire binding
  | ClassTyDecl (Maybe Span)
  | Decl DeclType (Maybe Span) -- Span of entire binding
  | TyVarBind Scope TyVarScope
    deriving (Eq, Ord, Show)

data BindType =
    RegularBind
  | InstanceBind
    deriving (Eq, Ord, Show)

data DeclType = 
    FamDec
  | SynDec
  | DataDec
  | ConDec
  | PatSynDec
  | ClassDec
  | InstDec
    deriving (Eq, Ord, Show)

data Scope =
    NoScope
  | LocalScope Span
  | ModuleScope
    deriving (Eq, Ord, Show)

data TyVarScope =
    ResolvedScopes [Scope]
  | UnresolvedScope [Name.Name] (Maybe Span)
    -- ^ The Span is the location of the instance/class declaration
    deriving (Eq, Ord, Show)

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

data HieFile = HieFile
    { hieVersion :: String
    , ghcVersion :: String
    , hsFile     :: String
    , hieTypes   :: Array TypeIndex GHC.Type
    , hieAST     :: HieAST TypeIndex
    , hsSrc      :: String
    }

data HieAST a =
  Node
    { nodeInfo :: NodeInfo a
    , nodeSpan :: Span
    , nodeChildren :: [HieAST a]
    } deriving Show

data NodeInfo a = NodeInfo
    { nodeAnnotations :: Set (String,String) -- Constr, Type
    , tokenInfo :: Maybe TokenType -- The kind of token this corresponds to,
                                   -- if any, for syntax highlighting purposes
    , nodeType :: Maybe a -- The haskell type of this node, if any
    , nodeIdentifiers :: NodeIdentifiers a -- All the identifiers and their details
    } deriving Show

type Identifier = Either GHC.ModuleName GHC.Name

type NodeIdentifiers a = Map Identifier (IdentifierDetails a)

data IdentifierDetails a = IdentifierDetails
  { identType :: Maybe a
  , identInfo :: Set (ContextInfo)
  } deriving Show
-- ^ We need to include types with identifiers because sometimes multiple
-- identifiers occur in the same span(Overloaded Record Fields and so on)

instance Semigroup (NodeInfo a) where
  (NodeInfo as ta ai ad) <> (NodeInfo bs tb bi bd) =
    NodeInfo (S.union as bs) (ta <|> tb) (ai <|> bi) (combineNodeIdentifiers ad bd)
instance Monoid (NodeInfo a) where
  mempty = NodeInfo S.empty Nothing Nothing M.empty

instance Semigroup (IdentifierDetails a) where
  d1 <> d2 =
    IdentifierDetails (identType d1 <|> identType d2) (S.union (identInfo d1) (identInfo d2))
instance Monoid (IdentifierDetails a) where
  mempty = IdentifierDetails Nothing S.empty

combineNodeIdentifiers :: NodeIdentifiers a -> NodeIdentifiers a -> NodeIdentifiers a
combineNodeIdentifiers i1 i2 = M.unionWith (<>) i1 i2

instance Show Name.Name where
  show = Name.nameStableString
instance Show GHC.Type where
  show = GHC.showSDocUnsafe . GHC.ppr
instance Show GHC.ModuleName where
  show = Module.moduleNameString
