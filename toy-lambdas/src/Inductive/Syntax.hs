module Inductive.Syntax
  ( Type(..)
  , Field(..)
  , TypeParam
  , TypeName
  , TypeDefBody(..)
  , TypeDef(..)
  , ValConstructor(..)
  ) where

data Field = Field { name :: String, tp :: Type } deriving (Eq, Show)

data Type = TypeName String
          | ProdType [Type]
          | FnType {domain :: Type, codomain :: Type}
          deriving (Eq, Show)
        

type TypeParam = String
type TypeName  = String

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

