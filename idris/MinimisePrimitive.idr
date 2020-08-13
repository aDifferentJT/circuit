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

allInputs : (a : Encodable) -> List (Encoding (BitType Bit) a, List (Literal (IndexType a)))
allInputs Bit = [(BitEncoding B0, [Neg EmptyIndex]), (BitEncoding B1, [Pos EmptyIndex])]
allInputs UnitEnc = [(UnitEnc, [])]
allInputs (a && b) =
  combine ((&&) **** (++))
    (map (second $ map $ map LeftIndex) $ allInputs a)
    (map (second $ map $ map RightIndex) $ allInputs b)
allInputs (EncVect Z a) = [([], [])]
allInputs (EncVect (S k) a) =
  combine ((::) **** (++))
    (map (second $ map $ map HeadIndex) $ allInputs a)
    (map (second $ map $ map TailIndex) $ allInputs $ assert_smaller (EncVect (S k) a) $ EncVect k a)
allInputs (NewEnc _ a) = map (NewEncoding *** (map $ map NewEncIndex)) $ allInputs a

analysePrimitive
  :  {a : Encodable}
  -> {b : Encodable}
  -> (Encoding (BitType Bit) a -> Encoding (BitType Bit) b)
  -> Encoding (BitType (List (List (Literal (IndexType a))), List (List (Literal (IndexType a))))) b 
analysePrimitive {a} f =
  foldl
    (\onOffSets, (bits, term) => zipWith (uncurry $ addTerm term) onOffSets $ f bits)
    (replicate ([], []))
    (allInputs a)
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
minimisePrimitive {a} = traverse (uncurry (boom {a = IndexType a})) . analysePrimitive

