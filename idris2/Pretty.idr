module Pretty

import Circuit
import Data.DPair.Extra
import Data.HVect
import Data.List
import Data.Nat
import Data.Strings
import Data.Vect
import LineDrawing
import NatProofs
import PartialIndex
import IndexType
import Utils
import VectProofs

%default total

half : (n : Nat) -> (m1 : Nat ** m2 : Nat ** m1 + m2 = n)
half Z =
  (Z ** Z ** Refl)
half (S Z) =
  (Z ** S Z ** Refl)
half (S (S n)) =
  let (m1 ** m2 ** pf) = half n in
      (S m1 ** S m2 ** rewrite sym $ plusSuccRightSucc m1 m2 in cong S . cong S $ pf)

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
  :  (a : Encodable)
  -> Maybe (b : Encodable ** PartialIndex a b)
  -> WithBitType t a
  -> (  n : Nat
     ** as : Vect n Encodable
     ** ( Maybe (k : Fin n ** b : Encodable ** PartialIndex (index k as) b)
        , HVect (map (WithBitType t) as)
        )
     )
tupleToList (a1 && a2) Nothing (x1, x2) =
  let (n ** as ** (_, xs)) = tupleToList a2 Nothing x2 in
      (S n ** a1 :: as ** (Nothing, x1 :: xs))
tupleToList (a1 && a2) (Just (b ** i)) (x1, x2) =
  case i of
       EmptyIndex => let (n ** as ** (_, xs)) = tupleToList a2 Nothing x2 in
                         (S n ** a1 :: as ** (Nothing, x1 :: xs))
       LeftIndex i' => let (n ** as ** (_, xs)) = tupleToList a2 Nothing x2 in
                           (S n ** a1 :: as ** (Just (0 ** b ** i'), x1 :: xs))
       RightIndex i' => case tupleToList a2 (Just (b ** i')) x2 of
                             (n ** as ** (Nothing, xs)) => (S n ** a1 :: as ** (Nothing, x1 :: xs))
                             (n ** as ** (Just (k ** b' ** i''), xs)) => (S n ** a1 :: as ** (Just (FS k ** b' ** i''), x1 :: xs))
tupleToList a Nothing x = (1 ** [a] ** (Nothing, [x]))
tupleToList a (Just (b ** i)) x = (1 ** [a] ** (Just (0 ** b ** i), [x]))

makeVectIndex
  :  Maybe (b : Encodable ** PartialIndex (EncVect n a) b)
  -> Maybe (k : Fin n ** b : Encodable ** PartialIndex (index k $ replicate a) b)
makeVectIndex Nothing = Nothing
makeVectIndex (Just (_ ** EmptyIndex)) = Nothing
makeVectIndex (Just (b ** (VectIndex k i))) = Just (k ** b ** rewrite indexReplicate k a in i)

makeNewEncIndex
  :  Maybe (b : Encodable ** PartialIndex (NewEnc ident a) b)
  -> Maybe (b : Encodable ** PartialIndex a b)
makeNewEncIndex Nothing = Nothing
makeNewEncIndex (Just (_ ** EmptyIndex)) = Nothing
makeNewEncIndex (Just (b ** NewEncIndex i)) = Just (b ** i)

extractVectIndex : Maybe (k : Fin n ** b : Encodable ** PartialIndex (index k as) b) -> Maybe (Fin n)
extractVectIndex Nothing = Nothing
extractVectIndex (Just (k ** _ ** i)) =
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
    => (as : Vect n Encodable)
    -> Maybe (k : Fin n ** b : Encodable ** PartialIndex (index k as) b)
    -> HVect (map (WithBitType t) as)
    -> VectPrettys n
  vectPrettys {t} as Nothing xs = hVectToVect {xs = as} (pretty' {t} Nothing) xs
  vectPrettys {t} as (Just (k ** b ** i)) xs =
    hVectToVect {xs = as} (uncurry $ pretty' {t}) $
    rewrite__impl HVect (sym $ zipMaps as) $
    zip
      (hVectOneElement (\a => (b : Encodable ** PartialIndex a b)) (b ** i))
      xs
    
  prettyVect
    :  Show t
    => (n : Nat)
    -> (as : Vect n Encodable)
    -> Maybe (k : Fin n ** b : Encodable ** PartialIndex (index k as) b)
    -> HVect (map (WithBitType t) as)
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
    => {a : Encodable}
    -> Maybe (b : Encodable ** PartialIndex a b)
    -> WithBitType t a
    -> (height : Nat ** width : Nat ** Vect height (Vect width (Either LineDir Char)))
  pretty' @{showT} {a = Bit} i x =
    (1 ** second ((::[]) . map Right) $ listToVect $ unpack $ show $ x)
  pretty' {t} {a = a1 && a2} i x =
    let (n ** as ** (i', xs)) = tupleToList (a1 && a2) i x in
        assert_total $ prettyVect {t} n as i' xs
  pretty' {t} {a = EncVect n a} i xs =
    assert_total $ prettyVect {t} n (replicate a) (makeVectIndex i) $ rewrite mapReplicate (WithBitType t) n a in vectToHVect xs
  pretty' {t} {a = NewEnc ident _} i (MkNewType x) =
    let (width1 ** ident') = listToVect $ unpack $ ident in
        let (height ** width2 ** lines) = pretty' {t} (makeNewEncIndex i) x in
            (  S height
            ** maxNat width1 width2
            ** cPad {smaller=xSmallerThanMaxNatXY width1 width2} (Left space) (map Right ident')
            :: map (cPad {smaller=ySmallerThanMaxNatXY width1 width2} $ Left space) lines
            )

pretty : Show t => {a : Encodable} -> Maybe (b : Encodable ** PartialIndex a b) -> WithBitType t a -> String
pretty i x =
  let (height ** width ** ls) = pretty' i x in
      unlines $ toList $ map (pack . toList . map (either lineDrawingChar id)) $ ls

prettyInvert : Show t => {a : Encodable} -> Maybe (b : Encodable ** PartialIndex a b) -> WithBitType t a -> String
prettyInvert i x =
  let (_ ** _ ** lines) = pretty' i x in
      unlines $ toList $ map (pack . toList . map (either (lineDrawingChar . flipV) id)) $ reverse $ lines

mutual
  covering export
  prettySimulate : {a : Encodable} -> {b : Encodable} -> {c : Encodable} -> (a ~> b) -> PartialIndex a c -> PrimType a -> IO ()
  prettySimulate {a} {b} {c} f i x = do
    putStrLn $ prettyInvert {t = BitT} {a = b} Nothing $ simulate f x
    putStrLn $ pretty {t = BitT} {a} (Just (c ** i)) x
    getLine >>= executeUserInput f i x
  
  covering
  executeUserInput : {a : Encodable} -> {b : Encodable} -> {c : Encodable} -> (a ~> b) -> PartialIndex a c -> PrimType a -> String -> IO ()
  executeUserInput {c = Bit} f i x " " = prettySimulate f i $ mapBitAt bitNot (indexFromPartial i) x
  executeUserInput f i x "u" = prettySimulate f (snd $ moveUp i) x
  executeUserInput f i x "d" = prettySimulate f (snd $ moveDown i) x
  executeUserInput f i x "l" = prettySimulate f (snd $ moveLeft i) x
  executeUserInput f i x "r" = prettySimulate f (snd $ moveRight i) x
  executeUserInput f i x s =
    if s == (pack $ the (List Char) [chr 27, '[', 'A'])
       then prettySimulate f (snd $ moveUp i) x
       else if s == (pack $ the (List Char) [chr 27, '[', 'B'])
       then prettySimulate f (snd $ moveDown i) x
       else if s == (pack $ the (List Char) [chr 27, '[', 'C'])
       then prettySimulate f (snd $ moveRight i) x
       else if s == (pack $ the (List Char) [chr 27, '[', 'D'])
       then prettySimulate f (snd $ moveLeft i) x
       else prettySimulate f i x

