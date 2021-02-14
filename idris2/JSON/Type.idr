module JSON.Type

%default total

public export
data JSONType : Type where
  JSONBool : JSONType
  JSONNumber : JSONType
  JSONString : JSONType
  JSONArray : JSONType -> JSONType
  JSONDict : JSONType -> JSONType
  JSONObject : List (String, JSONType) -> JSONType

