module JSON.MkArray

import JSON.Type
import JSON.Value

%default total

public export
Nil : JSONValue (JSONArray t)
Nil = JSONMkArray []

public export
(::) : JSONValue t -> JSONValue (JSONArray t) -> JSONValue (JSONArray t)
x :: (JSONMkArray xs) = JSONMkArray (x :: xs)

