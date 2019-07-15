module defs.Identifier

import ParseUtils

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
