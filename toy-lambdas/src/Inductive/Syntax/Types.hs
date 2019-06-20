module Inductive.Syntax.Types
  ( Type(..)
  , Field(..)
  , TypeParam
  , TypeName
  , TypeDefBody(..)
  , TypeDef(..)
  , ValConstructor(..)
  ) where

data Field = Field { name :: String, tp :: Type } deriving (Eq, Show)

-- | 'Type' represents a type in the object language
data Type
    -- | 'TypeName' constructs a 'Type' from a 'String', such as an 'Int' type
    = TypeName String
    -- | 'ProdType' constructs a product type.
    | ProdType [Type]
    -- | 'FnType' constructs a function type with a domain type and a codomain
    -- type
    | FnType {domain :: Type, codomain :: Type}
    deriving (Eq, Show)
        

-- | A 'TypeParam' represents a type parameter in parametric polymorphism
-- For instance, in the type @List a@ the type parameter is @a@. 'TypeParam's
-- must start with a lowercase letter and consist only of lowercase letters and
-- digits.
type TypeParam = String

-- | A 'TypeName' represents a type, and consists of an uppercase letter follwed
-- by any sequence of alphanumeric characters and/or underscores
type TypeName  = String

-- | A 'ValConstructor' represents a value constructor in a type definition.
data ValConstructor = ValConstructor TypeName [Type]
  deriving (Eq, Show)

data TypeDefBody = TpDefRecord    [Field]
                 | TpDefValConstr [ValConstructor]
                 | TpDefLiteral Type
                 deriving (Eq, Show)

data TypeDef = TypeDef { tdName   :: TypeName
                       , tdParams ::  [TypeParam]
                       , tdBody   :: TypeDefBody
                       } deriving (Eq, Show)

