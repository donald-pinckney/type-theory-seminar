module defs.Identifier

import Shared.ParseUtils

export
record Identifier where
    constructor MkIdentifier
    token : SourceString

export
text : Identifier -> String
text = pack . (map snd) . token

export
sameIdentifier : Identifier -> Identifier -> Bool
sameIdentifier a b = text a == text b


export
implementation Eq Identifier where
    id1 == id2 = text id1 == text id2

export
implementation Show Identifier where
    show id = text id
