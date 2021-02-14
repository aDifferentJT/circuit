module TUI

import Circuit
import Data.DPair
import Data.DPair.Extra
import Data.HVect
import Data.List
import Data.Nat
import Data.Strings
import Data.Vect
import IndexType
import LinearUtils
import LineDrawing
import NatProofs
import Utils
import VectProofs

%default total

%ambiguity_depth 10

half : (n : Nat) -> (m1 : Nat ** m2 : Nat ** m1 + m2 = n)
half Z =
  (Z ** Z ** Refl)
half (S Z) =
  (Z ** S Z ** Refl)
half (S (S n)) =
  let (m1 ** m2 ** pf) = half n in
      (S m1 ** S m2 ** rewrite sym $ plusSuccRightSucc m1 m2 in cong S $ cong S $ pf)

cPad : {m : Nat} -> {n : Nat} -> {auto smaller : LTE m n} -> a -> Vect m a -> Vect n a
cPad x xs = 
  let (lPad ** rPad ** sumHalves) = half (n `minus` m) in
      rewrite sym (plusMinusCancel n m {smaller}) in
              rewrite sym $ sumHalves in
                      rewrite plusCommutative m (lPad + rPad) in
                              rewrite sym $ plusAssociative lPad rPad m in
                                      rewrite sym $ plusCommutative m rPad in
                                              (replicate lPad x) ++ xs ++ (replicate rPad x)

rPad : {m : Nat} -> {n : Nat} -> {auto smaller : LTE m n} -> a -> Vect m a -> Vect n a
rPad {m} {n} x xs = 
  rewrite sym $ plusMinusCancel n m in
          rewrite plusCommutative m (n `minus` m) in
                  (replicate (n `minus` m) x) ++ xs

mapHead : Not (n = Z) -> (a -> a) -> Vect n a -> Vect n a
mapHead p f [] = absurd $ p Refl
mapHead _ f (x :: xs) = f x :: xs

bracketWidth : Vect _ Nat -> Nat
bracketWidth [] = 1
bracketWidth (n :: ns) = 1 + n + bracketWidth ns

bracketWidthNotZ : {ns : Vect _ Nat} -> Not (bracketWidth ns = Z)
bracketWidthNotZ {ns = []} = SIsNotZ
bracketWidthNotZ {ns = _ :: _} = SIsNotZ

bracketMerge : (xs : Vect m (n : Nat ** Vect n (Either LineDir Char))) -> Vect (bracketWidth (map DPair.fst xs)) (Either LineDir Char)
bracketMerge []               = [Left space]
bracketMerge ((_ ** x) :: xs) = [Left space] ++ x ++ bracketMerge xs

bracket : Maybe (Fin m) -> (ns : Vect m Nat) -> Vect (bracketWidth ns) LineDir
bracket Nothing [] = [MkLineDir None Thin None None]
bracket Nothing (n :: ns) =
  [MkLineDir None Thin None Thin]
  ++ replicate n (MkLineDir None None Thin Thin)
  ++ mapHead bracketWidthNotZ (record {lineW = Thin}) (bracket Nothing ns)
bracket (Just FZ) (n :: ns) =
  [MkLineDir None Bold None Bold]
  ++ replicate n (MkLineDir None None Bold Bold)
  ++ mapHead bracketWidthNotZ (record {lineW = Bold, lineS = Bold}) (bracket Nothing ns)
bracket (Just (FS highlight)) (n :: ns) =
  [MkLineDir None Thin None Thin]
  ++ replicate n (MkLineDir None None Thin Thin)
  ++ mapHead bracketWidthNotZ (record {lineW = Thin}) (bracket (Just highlight) ns)

tupleToList
  :  (0 a : Encodable)
  -> Maybe (Exists (PartialIndex a))
  -> Encoding (BitType t) a
  -> (  n : Nat
     ** Exists {type = Vect n Encodable} (\as =>
        ( Maybe (k : Fin n ** Exists (PartialIndex (index k as)))
        , HVect (map (Encoding $ BitType t) as)
        )
        )
     )
tupleToList (a && UnitEnc) Nothing (x && UnitEnc) = (1 ** Evidence [a] (Nothing, [x]))
tupleToList (a && UnitEnc) (Just (Evidence b (LeftIndex i))) (x && UnitEnc) = (1 ** Evidence [a] (Just (0 ** Evidence b i), [x]))
tupleToList (a1 && a2) Nothing (x1 && x2) =
  let (n ** Evidence as (_, xs)) = tupleToList a2 Nothing x2 in
      (S n ** Evidence (a1 :: as) (Nothing, x1 :: xs))
tupleToList (a1 && a2) (Just (Evidence b i)) (x1 && x2) =
  case i of
       EmptyIndex => let (n ** Evidence as (_, xs)) = tupleToList a2 Nothing x2 in
                         (S n ** Evidence (a1 :: as) (Nothing, x1 :: xs))
       LeftIndex i' => let (n ** Evidence as (_, xs)) = tupleToList a2 Nothing x2 in
                           (S n ** Evidence (a1 :: as) (Just (0 ** Evidence b i'), x1 :: xs))
       RightIndex i' => case tupleToList a2 (Just (Evidence b i')) x2 of
                             (n ** Evidence as (Nothing, xs)) => (S n ** Evidence (a1 :: as) (Nothing, x1 :: xs))
                             (n ** Evidence as (Just (k ** Evidence b' i''), xs)) => (S n ** Evidence (a1 :: as) (Just (FS k ** Evidence b' i''), x1 :: xs))
tupleToList a Nothing x = (1 ** Evidence [a] (Nothing, [x]))
tupleToList a (Just (Evidence b i)) x = (1 ** Evidence [a] (Just (0 ** Evidence b i), [x]))

extractVect
  :  (0 a : Encodable)
  -> Maybe (Exists (PartialIndex (EncVect n a)))
  -> Encoding (BitType t) (EncVect n a)
  -> (  n : Nat
     ** ( Maybe (k : Fin n ** Exists (PartialIndex (index k $ replicate a)))
        , HVect (map (Encoding $ BitType t) $ replicate n a)
        )
     )
extractVect a _ [] = (Z ** (Nothing, []))
extractVect a Nothing (x :: xs) =
  let (n ** (_, xs')) = extractVect a Nothing xs in
      (S n ** (Nothing, x :: xs'))
extractVect a (Just (Evidence b i)) (x :: xs) =
  case i of
       EmptyIndex => let (n ** (_, xs')) = extractVect a Nothing xs in
                         (S n ** (Nothing, x :: xs'))
       HeadIndex i' => let (n ** (_, xs')) = extractVect a Nothing xs in
                           (S n ** (Just (FZ ** Evidence b i'), x :: xs'))
       TailIndex i' => case extractVect a (Just (Evidence b i')) xs of
                             (n ** (Nothing, xs')) => (S n ** (Nothing, x :: xs'))
                             (n ** (Just (k ** Evidence b' i''), xs')) => (S n ** (Just (FS k ** Evidence b' i''), x :: xs'))

makeNewEncIndex
  :  Maybe (Exists (PartialIndex (NewEnc ident a)))
  -> Maybe (Exists (PartialIndex a))
makeNewEncIndex Nothing = Nothing
makeNewEncIndex (Just (Evidence _ EmptyIndex)) = Nothing
makeNewEncIndex (Just (Evidence b (NewEncIndex i))) = Just (Evidence b i)

extractVectIndex : Maybe (k : Fin n ** Exists (PartialIndex (index k as))) -> Maybe (Fin n)
extractVectIndex Nothing = Nothing
extractVectIndex (Just (k ** Evidence _ i)) =
  case i of
       EmptyIndex => Just k
       _ => Nothing

VectPrettys : Nat -> Type
VectPrettys n = Vect n (height' : Nat ** width' : Nat ** Vect height' (Vect width' (Either LineDir Char)))

VectHeightProofs : Nat -> Nat -> Type
VectHeightProofs n height = Vect n (pretty : (height' : Nat ** width' : Nat ** Vect height' (Vect width' (Either LineDir Char))) ** LTE (fst pretty) height)

vectHeightWithProofs : VectPrettys n -> (height : Nat ** VectHeightProofs n height)
vectHeightWithProofs prettys = second tail $ maxNatsWithProofs DPair.fst ((0 ** 0 ** []) :: prettys)
    
vectVPadded : {height : Nat} -> VectHeightProofs n height -> Vect n (width' : Nat ** Vect height (Vect width' (Either LineDir Char)))
vectVPadded = map (\((height' ** width' ** lines) ** smaller) => (width' ** rPad {smaller} (replicate $ Left space) lines))
    
mutual
  vectPrettys
    :  Show t
    => {n : Nat}
    -> (0 as : Vect n Encodable)
    -> Maybe (k : Fin n ** Exists (PartialIndex (index k as)))
    -> HVect (map (Encoding $ BitType t) as)
    -> VectPrettys n
  vectPrettys {t} as Nothing xs = hVectToVect {xs = as} (pretty' {t} Nothing) xs
  vectPrettys {t} as (Just (k ** Evidence b i)) xs =
    hVectToVect {xs = as} (uncurry $ pretty' {t}) $
    rewrite__impl HVect (sym $ zipMaps as) $
    zip
      (hVectOneElement (\a => Exists (PartialIndex a)) (Evidence b i))
      xs
    
  prettyVect
    :  Show t
    => (n : Nat)
    -> (0 as : Vect n Encodable)
    -> Maybe (k : Fin n ** Exists (PartialIndex (index k as)))
    -> HVect (map (Encoding $ BitType t) as)
    -> (height : Nat ** width : Nat ** Vect height (Vect width (Either LineDir Char)))
  prettyVect {t} n as i xs =
    let prettys = vectPrettys as i xs in
        let (height ** heightProofs) = vectHeightWithProofs prettys in
            let vPadded = vectVPadded heightProofs in
                (  S height
                ** bracketWidth $ map fst vPadded
                ** map Left (bracket (extractVectIndex i) $ map fst vPadded)
                :: zipUnequalVect {f = bracketWidth} bracketMerge vPadded
                )

  pretty'
    :  Show t
    => Maybe (Exists (PartialIndex a))
    -> Encoding (BitType t) a
    -> (height : Nat ** width : Nat ** Vect height (Vect width (Either LineDir Char)))
  pretty' {a = Bit} _ (BitEncoding (MkBitType x)) =
    (1 ** second ((::[]) . map Right) $ listToVect $ unpack $ show $ x)
  pretty' _ UnitEnc = (1 ** 2 ** [[Right '(', Right ')']])
  pretty' {a = a1 && a2} i x@(_ && _) =
    let (n ** Evidence as (i', xs)) = tupleToList (a1 && a2) i x in
        assert_total $ prettyVect {t} n as i' xs
  pretty' {a = EncVect _ a} i x@[] =
    assert_total $ prettyVect {t} Z (replicate a) Nothing []
  pretty' {a = EncVect _ a} i x@(_ :: _) =
    let (n ** (i', xs)) = extractVect a i x in
        assert_total $ prettyVect {t} n (replicate a) i' xs
  pretty' {a = NewEnc ident _} i (NewEncoding x) =
    let (width1 ** ident') = listToVect $ unpack $ ident in
        let (height ** width2 ** lines) = pretty' {t} (makeNewEncIndex i) x in
            (  S height
            ** maxNat width1 width2
            ** cPad {smaller=xSmallerThanMaxNatXY width1 width2} (Left space) (map Right ident')
            :: map (cPad {smaller=ySmallerThanMaxNatXY width1 width2} $ Left space) lines
            )

pretty : Show t => Maybe (Exists (PartialIndex a)) -> Encoding (BitType t) a -> String
pretty i x =
  let (height ** width ** ls) = pretty' i x in
      unlines $ toList $ map (pack . toList . map (either lineDrawingChar id)) $ ls

prettyInvert : Show t => Maybe (Exists (PartialIndex a)) -> Encoding (BitType t) a -> String
prettyInvert i x =
  let (_ ** _ ** lines) = pretty' i x in
      unlines $ toList $ map (pack . toList . map (either (lineDrawingChar . flipV) id)) $ reverse $ lines

mutual
  covering export
  tuiSimulate
    :  {input : Encodable}
    -> Producing BinarySimPrim input a
    -> Encoding (BitType Bit) input
    -> {b : Encodable}
    -> PartialIndex input b
    -> IO ()
  tuiSimulate x inputs i = do
    putStr $ prettyInvert {t = Bit} Nothing (simulate x inputs)
    putStr $ pretty {t = Bit} (Just (Evidence b i)) inputs
    getLine >>= executeUserInput x inputs i
  
  covering
  executeUserInput
    :  {input : Encodable}
    -> Producing BinarySimPrim input a
    -> Encoding (BitType Bit) input
    -> {b : Encodable}
    -> PartialIndex input b
    -> String
    -> IO ()
  executeUserInput {b = Bit} x inputs i " " = tuiSimulate x (mapBitAt (relax bitNot) i inputs) i
  executeUserInput x inputs i "u" = tuiSimulate x inputs $ snd $ moveUp i
  executeUserInput x inputs i "d" = tuiSimulate x inputs $ snd $ moveDown i
  executeUserInput x inputs i "l" = tuiSimulate x inputs $ snd $ moveLeft i
  executeUserInput x inputs i "r" = tuiSimulate x inputs $ snd $ moveRight i
  executeUserInput x inputs i s =
    if s == (pack $ the (List Char) [chr 27, '[', 'A'])
       then tuiSimulate x inputs $ snd $ moveUp i
       else if s == (pack $ the (List Char) [chr 27, '[', 'B'])
       then tuiSimulate x inputs $ snd $ moveDown i
       else if s == (pack $ the (List Char) [chr 27, '[', 'C'])
       then tuiSimulate x inputs $ snd $ moveRight i
       else if s == (pack $ the (List Char) [chr 27, '[', 'D'])
       then tuiSimulate x inputs $ snd $ moveLeft i
       else tuiSimulate x inputs i

