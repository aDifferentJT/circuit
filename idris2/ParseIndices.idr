module ParseIndices

import Circuit
import Data.Fin
import Data.List
import Data.Strings
import Text.Lexer
import Text.Parser
import IndexType

%default total

tokenMap : TokenMap (Maybe Nat)
tokenMap =
  [ (digits, parsePositive)
  , (oneOf " ,", const Nothing)
  ]

lexTokens : String -> Either String (List Nat)
lexTokens s with (lex tokenMap s)
  lexTokens _ | (ts, _, column, s') with (unpack s')
     lexTokens _ | (ts, _, _, _)     | [] =
       Right . mapMaybe id . map tok $ ts
     lexTokens _ | (_, _, column, _) | (errorChar :: _) =
       Left $ "Unexpected character " ++ show errorChar ++ " in column " ++ show (column + 1)

fin : {n : Nat} -> Grammar Nat True (Fin n)
fin {n} = terminal "Fin" (\m => natToFin m n)

encConsumes : Encodable -> Bool
encConsumes Bit = False
encConsumes (_ && _) = True
encConsumes (EncVect _ _) = True
encConsumes (NewEnc _ a) = encConsumes a

grammar : (a : Encodable) -> Grammar Nat (encConsumes a) (IndexType a)
grammar Bit = pure ()
grammar (a && b) =
  (<|>) {c1=True} {c2 = True}
    (seq {c2 = encConsumes a}
      (terminal "B0" $ \n => if n == 0 then Nothing else Just ())
      (\() => Left <$> grammar a)
    )
    (seq {c2 = encConsumes b}
      (terminal "B1" $ \n => if n == 1 then Nothing else Just ())
      (\() => Right <$> grammar b)
    )
grammar (EncVect n a) =
  fin >>= \i => (\is => (i, is)) <$> grammar a
grammar (NewEnc _ a) = grammar a

parseEnc : (a : Encodable) -> List Nat -> Either String (IndexType a)
parseEnc a xs =
  case parse (grammar a) xs of
       Left (Error e ts) => Left $ "Error: " ++ e ++ " with remaining tokens " ++ show ts
       Right (is, [])    => Right is
       Right (_, ts)     => Left $ "Unexpected element " ++ show ts

export
parseIndices : (a : Encodable) -> String -> Either String (IndexType a)
parseIndices a s = lexTokens s >>= parseEnc a

