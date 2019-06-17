module SimplyTyped
    (checkContextInvariant
    , Type (..)
    , Decl (..)
    , Context
    , Term (..)
    , parse
    , parseType
    , pprint
    , pprint_
    , pprint_tp_
    , substitute
    , betaReduce
    , exec
    , check
    ) where

import SimplyTyped.Syntax
import SimplyTyped.Print
import SimplyTyped.Parse
import SimplyTyped.Semantics
