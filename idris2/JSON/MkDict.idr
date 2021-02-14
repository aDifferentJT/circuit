module JSON.MkDict

import JSON.Type
import JSON.Value

%default total

public export
Nil : JSONValue (JSONDict t)
Nil = JSONMkDict []

public export
(::) : (String, JSONValue t) -> JSONValue (JSONDict t) -> JSONValue (JSONDict t)
x :: (JSONMkDict xs) = JSONMkDict (x :: xs)

