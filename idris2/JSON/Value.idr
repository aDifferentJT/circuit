module JSON.Value

import Data.List
import Data.Strings
import JSON.Type

%default total

public export
data JSONValue : JSONType -> Type where
  JSONMkBool : Bool -> JSONValue JSONBool
  JSONMkNumber : Double -> JSONValue JSONNumber
  JSONMkString : String -> JSONValue JSONString
  JSONMkArray : List (JSONValue t) -> JSONValue (JSONArray t)
  JSONMkDict : List (String, JSONValue t) -> JSONValue (JSONDict t)
  Nil : JSONValue (JSONObject [])
  (::) : (x : (String, JSONValue t)) -> JSONValue (JSONObject ts) -> JSONValue (JSONObject ((fst x, t) :: ts))

public export
fromInteger : Integer -> JSONValue JSONNumber
fromInteger = JSONMkNumber . fromInteger

public export
negate : JSONValue JSONNumber -> JSONValue JSONNumber
negate (JSONMkNumber x) = JSONMkNumber $ negate x

public export
fromString : String -> JSONValue JSONString
fromString = JSONMkString . fromString

export
Show (JSONValue _) where
  show (JSONMkBool True) = "true"
  show (JSONMkBool False) = "false"
  show (JSONMkNumber x) = show x
  show (JSONMkString x) = show x
  show (JSONMkArray xs) = show xs
  show (JSONMkDict xs) =
    "{" ++ (concat $ intersperse "," $ map (\(k, x) => show k ++ ":" ++ show x) xs) ++ "}"
  show [] = "{}"
  show [(k, x)] = "{" ++ show k ++ ":" ++ show x ++ "}"
  show ((k, x) :: xs) = "{" ++ show k ++ ":" ++ show x ++ "," ++ (assert_total $ strTail $ show xs)

