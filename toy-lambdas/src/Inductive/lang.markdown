# Inductive Language Definition

## Type Definitions

```haskell
fieldName   ::= NAME
typeName    ::= TYPENAME

typeLiteral ::= typeName
             |  sumType
             |  prodType
             |  fnType

prodType     ::= typeLiteral AST typeLiteral prodTypeTail
prodTypeTail ::=
              |  AST typeLiteral prodTypeTail

fnFreeType   ::= typeName
              |  sumType
              |  prodType
              |  LPAREN fnType RPAREN

fnType       ::= fnFreeType RIGHTARROW typeLiteral

typeDef ::= DATA typeName optTypeParams EQ typeDefBody

optTypeParams ::=
               |  "::" many1TypeVars "=>"

many1TypeVars ::= typeVar
               |  typeVar COMMA many1TypeVars

typeVar ::= name

typeDefBody ::=
             |  LBRACE recordEntryList RBRACE
             |  valConstructorBody
             |  typeLiteral

-- RECORDS
-- Records may be empty or contain a comma-separated list of record entries
recordEntryList          ::= emptyRecordEntryList
                          |  populatedRecordEntryList
emptyRecordEntryList     ::=
populatedRecordEntryList ::= recordEntry
                          |  recordEntry COMMA populatedRecordEntryList

-- A record entry has a fieldName and a typeName
recordEntry ::= fieldName typeName

-- VALURE CONSTRUCTORS
valConstructorBody ::= valConstructorList
valConstructorList ::= valConstructor
                    |  valConstructor VBAR valConstructorList
valConstructor     ::= typeName typeLiteral

```

