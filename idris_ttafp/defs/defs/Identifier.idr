module defs.Identifier

import ParseUtils

export
record Identifier where
    constructor MkIdentifier
    token : SourceString

export
text : Identifier -> String
text = pack . (map snd) . token
