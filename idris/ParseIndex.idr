module ParseIndex

import Circuit
import Data.Fin
import Data.String
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

nat : Grammar Nat True Nat
nat = terminal Just

fin : {n : Nat} -> Grammar Nat True (Fin n)
fin {n} = terminal (\m => natToFin m n)

encConsumes : Encodable -> Bool
encConsumes Bit = False
encConsumes UnitEnc = False
encConsumes (_ && _) = True
encConsumes (EncVect _ _) = True
encConsumes (NewEnc _ a) = encConsumes a

andFalse : (c : Bool) -> c && Delay False = False
andFalse True = Refl
andFalse False = Refl

eraseConsume : {c : _} -> Grammar tok c a -> Grammar tok False a
eraseConsume {c} {a} x = rewrite sym $ andFalse c in x <|> the (Grammar tok False a) (fail "")

grammar : (a : Encodable) -> Grammar Nat (encConsumes a) (IndexType a)
grammar Bit = pure EmptyIndex
grammar UnitEnc = fail "Cannot index into a UnitEnc"
grammar (a && b) = nat >>= f (a && b)
  where
    f : (c : Encodable) -> Nat -> Grammar Nat False (IndexType c)
    f (c && _) Z = LeftIndex <$> eraseConsume (grammar c)
    f (_ && c) (S i) = RightIndex <$> f c i
    f _ _ = fail "Index too large for tuple"
grammar (EncVect n a) = fin >>= f
  where
    f : Fin n' -> Grammar Nat (encConsumes a) (IndexType (EncVect n' a))
    f FZ = HeadIndex <$> grammar a
    f (FS i) = TailIndex <$> f i
grammar (NewEnc _ a) = NewEncIndex <$> grammar a

export
parseIndex' : (a : Encodable) -> List Nat -> Either String (IndexType a)
parseIndex' a xs =
  case parse (grammar a) xs of
       Left (Error e ts) => Left $ "Error: " ++ e ++ " with remaining tokens " ++ show ts
       Right (is, [])    => Right is
       Right (_, ts)     => Left $ "Unexpected element " ++ show ts

export
parseIndex : (a : Encodable) -> String -> Either String (IndexType a)
parseIndex a s = lexTokens s >>= parseIndex' a

