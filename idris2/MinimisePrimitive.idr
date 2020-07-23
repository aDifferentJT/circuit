module MinimisePrimitive

import Circuit
import Control.Monad.ExceptT
import Control.Monad.Random
import Data.List
import Encoding
import IndexType
import Minimiser.Boom
import public Minimiser.Literal
import Utils

%default total

combine : (a -> b -> c) -> List a -> List b -> List c
combine f [] ys = []
combine f (x :: xs) ys = map (f x) ys ++ combine f xs ys

allInputs : {a : Encodable} -> List (Encoding (BitType Bit) a, List (Literal (IndexType a)))
allInputs {a = Bit} = [(BitEncoding B0, [Neg EmptyIndex]), (BitEncoding B1, [Pos EmptyIndex])]
allInputs {a = UnitEnc} = [(UnitEnc, [])]
allInputs {a = a && b} =
  combine ((&&) **** (++))
    (map (second $ map $ map LeftIndex) allInputs)
    (map (second $ map $ map RightIndex) allInputs)
allInputs {a = EncVect Z a} = [([], [])]
allInputs {a = EncVect (S k) a} =
  combine ((::) **** (++))
    (map (second $ map $ map HeadIndex) allInputs)
    (map (second $ map $ map TailIndex) $ allInputs {a = assert_smaller (EncVect (S k) a) $ EncVect k a})
allInputs {a = NewEnc _ a} = map (NewEncoding *** (map $ map NewEncIndex)) allInputs

analysePrimitive
  :  {a : Encodable}
  -> {b : Encodable}
  -> (Encoding (BitType Bit) a -> Encoding (BitType Bit) b)
  -> Encoding (BitType (List (List (Literal (IndexType a))), List (List (Literal (IndexType a))))) b 
analysePrimitive f =
  foldl
    (\onOffSets, (bits, term) => zipWith (uncurry $ addTerm term) onOffSets $ f bits
    )
    (replicate ([], []))
    allInputs
  where
    addTerm
      :  List (Literal (IndexType a))
      -> ( onSet : List (List (Literal (IndexType a))))
      -> (offSet : List (List (Literal (IndexType a))))
      -> Bit
      -> ( List (List (Literal (IndexType a)))
         , List (List (Literal (IndexType a)))
         )
    addTerm term onSet offSet B0 = (onSet, term :: offSet)
    addTerm term onSet offSet B1 = (term :: onSet, offSet)

export
minimisePrimitive
  :  {a : Encodable}
  -> {b : Encodable}
  -> (Encoding (BitType Bit) a -> Encoding (BitType Bit) b)
  -> ExceptT String RandomM (Encoding (BitType (List (List (Literal (IndexType a))))) b)
minimisePrimitive = traverse (uncurry boom) . analysePrimitive

