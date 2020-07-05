module Language.Lefty.Pretty

import Data.Vect
import Language.Lefty.AST
import Utils

%default total

implicit
nonEmpty : (xs : List a) -> {auto p : NonEmpty xs} -> (xs : List a ** NonEmpty xs)
nonEmpty xs {p} = (xs ** p)

(++) : (xs : List a ** NonEmpty xs) -> (xs : List a ** NonEmpty xs) -> (xs : List a ** NonEmpty xs)
(x :: xs ** IsNonEmpty) ++ (ys ** _) = (x :: xs ++ ys ** IsNonEmpty)

map : (a -> b) -> (xs : List a ** NonEmpty xs) -> (xs : List b ** NonEmpty xs)
map f (x :: xs ** IsNonEmpty) = (f x :: map f xs ** IsNonEmpty)

concatMap : (a -> (xs : List b ** NonEmpty xs)) -> (xs : List a ** NonEmpty xs) -> (xs : List b ** NonEmpty xs)
concatMap f (x :: xs ** IsNonEmpty) with (f x)
  | (y :: ys ** IsNonEmpty) = (y :: ys ++ concatMap (DPair.fst . f) xs ** IsNonEmpty)

mapHeadTail : (a -> b) -> (a -> b) -> (xs : List a ** NonEmpty xs) -> (xs : List b ** NonEmpty xs)
mapHeadTail f g (x :: xs ** IsNonEmpty) = (f x :: map g xs ** IsNonEmpty)

mapInitLast : (a -> b) -> (a -> b) -> (xs : List a ** NonEmpty xs) -> (xs : List b ** NonEmpty xs)
mapInitLast f g ([x] ** IsNonEmpty) = ([g x] ** IsNonEmpty)
mapInitLast f g (x1 :: x2 :: xs ** IsNonEmpty) = assert_total (f x1 :: (fst $ mapInitLast f g (x2 :: xs ** IsNonEmpty)) ** IsNonEmpty)

joinLastHead : (a -> a -> a) -> (xs : List a ** NonEmpty xs) -> (xs : List a ** NonEmpty xs) -> (xs : List a ** NonEmpty xs)
joinLastHead f ([x] ** IsNonEmpty) (y :: ys ** IsNonEmpty) = (f x y :: ys ** IsNonEmpty)
joinLastHead f (x1 :: x2 :: xs ** IsNonEmpty) y = assert_total $ (x1 :: (fst $ joinLastHead f (x2 :: xs ** IsNonEmpty) y) ** IsNonEmpty)

interface Pretty a where
  pretty : a -> (xs : List String ** NonEmpty xs)

indent : Nat -> String -> String
indent n = ((pack $ List.replicate n ' ') ++)

prettyBinOp : (Pretty a, Pretty b) => a -> (op : String) -> b -> (xs : List String ** NonEmpty xs)
prettyBinOp x' op y' with (pretty x', pretty y')
  prettyBinOp _ op _ | (([x] ** IsNonEmpty), ([y] ** IsNonEmpty)) = (["(" ++ x ++ " " ++ op ++ " " ++ y ++ ")"] ** IsNonEmpty)
  prettyBinOp _ op _ | (xs, ys) =
    mapHeadTail (("(" ++ (pack $ List.replicate (length op) ' ')) ++) (indent $ length op + 1) xs
    ++ mapHeadTail ((op ++ " ") ++) (indent $ length op + 1) ys
    ++ [")"]

prettyAssign : (Pretty a, Pretty b) => a -> b -> (xs : List String ** NonEmpty xs)
prettyAssign x' y' with (pretty x', pretty y')
  prettyAssign _ _ | (([x] ** IsNonEmpty), ([y] ** IsNonEmpty)) = (["(" ++ x ++ " = " ++ y ++ ")"] ** IsNonEmpty)
  prettyAssign _ _ | (xs, ys) = mapInitLast id (++ " =") xs ++ map (indent 2) ys

mutual
  Pretty Expression where
    pretty (NumberConstant x) = [show x]
    pretty (StringConstant x) = [show x]
    pretty (Assign x y) = assert_total $ prettyAssign x y
    pretty (x || y) = assert_total $ prettyBinOp x "|" y
    pretty (x && y) = assert_total $ prettyBinOp x "&" y
    pretty (x == y) = assert_total $ prettyBinOp x "==" y
    pretty (x ~= y) = assert_total $ prettyBinOp x "~=" y
    pretty (x < y) = assert_total $ prettyBinOp x "<" y
    pretty (x <= y) = assert_total $ prettyBinOp x "<=" y
    pretty (x > y) = assert_total $ prettyBinOp x ">" y
    pretty (x >= y) = assert_total $ prettyBinOp x ">=" y
    pretty (x + y) = assert_total $ prettyBinOp x "+" y
    pretty (x - y) = assert_total $ prettyBinOp x "-" y
    pretty (x * y) = assert_total $ prettyBinOp x "*" y
    pretty (x / y) = assert_total $ prettyBinOp x "/" y
    pretty (Mod x y) = assert_total $ prettyBinOp x "%" y
    pretty (FunctionDecl x) = pretty x
    pretty (Table []) = ["[]"]
    pretty (Table xs@(_ :: _)) =
      assert_total $
      (mapHeadTail ("[ " ++) (indent 2) $ concatMap (mapInitLast id (++ ";") . uncurry prettyAssign) (xs ** IsNonEmpty))
      ++ ["]"]

  Pretty FunctionDeclaration where
    pretty x =
      [ "function " ++ funcIdent x ++ "(" ++ (concat $ intersperse ", " $ args x) ++ ") {"
      , "  local " ++ (concat $ intersperse ", " $ locals x) ++ ";"
      ]
      ++ (case body x of
         [] => ["}"]
         xs@(_ :: _) => (map (indent 2) $ concatMap pretty $ (xs ** IsNonEmpty)) ++ ["}"]
         )

  Pretty Variable where
    pretty (Identifier x) = [x]
    pretty (Subscript x y) = addVar index
      where
        addVar : (xs : List String ** NonEmpty xs) -> (xs : List String ** NonEmpty xs)
        addVar ys with (pretty x)
          | ([x'] ** IsNonEmpty) = mapHeadTail (x' ++) id ys
          | x' = x' ++ ys
        index : (xs : List String ** NonEmpty xs)
        index with (pretty y)
          | ([y'] ** IsNonEmpty) = ["[" ++ y' ++ "]"]
          | y' = mapHeadTail ("[ " ++) (indent 2) y' ++ ["]"]

  Pretty Statement where
    pretty (TopLevel x) = assert_total $ mapInitLast id (++ ";") $ pretty x
    pretty [] = ["{}"]
    pretty (x :: xs) = assert_total $ (["{"] ++ (map (indent 2) $ concatMap (fst . pretty) $ getSeq $ x :: xs) ++ ["}"] ** IsNonEmpty)
      where
        getSeq : Statement -> List Statement
        getSeq [] = []
        getSeq (x :: xs) = x :: getSeq xs
        getSeq x = [x]
    pretty (If c t e) = assert_total $ addCond $ addElse $ pretty t
      where
        addCond : (xs : List String ** NonEmpty xs) -> (xs : List String ** NonEmpty xs)
        addCond xs with (pretty c)
          | ([c'] ** IsNonEmpty) = mapHeadTail (("if (" ++ c' ++ ") ") ++) id xs
          | c' = joinLastHead (\x, y => x ++ ") " ++ y) (mapHeadTail ("if (" ++) (indent 4) c') xs
        addElse : (xs : List String ** NonEmpty xs) -> (xs : List String ** NonEmpty xs)
        addElse xs with (e)
          | Nothing = xs
          | Just e' = joinLastHead (\x, y => x ++ " else " ++ y) xs $ pretty e'
    pretty (While c x) = assert_total $ case pretty c of
      ([c'] ** IsNonEmpty) => mapHeadTail (("while (" ++ c' ++ ") ") ++) id $ pretty x
      c' => joinLastHead (\x, y => x ++ ") " ++ y) (mapHeadTail ("while (" ++) (indent 7) c') $ pretty x
    pretty (CFor init test update x) = assert_total $ case (pretty init, pretty test, pretty update) of
      (([init'] ** IsNonEmpty), ([test'] ** IsNonEmpty), ([update'] ** IsNonEmpty)) =>
        mapHeadTail (("for (" ++ init' ++ "; " ++ test' ++ "; " ++ update' ++ ") ") ++) id $ pretty x
      (init', test', update') =>
        mapHeadTail ("for ( " ++) (indent 6) init'
        ++ mapHeadTail ("    ; " ++) (indent 6) test'
        ++ mapHeadTail ("    ; " ++) (indent 6) update'
        ++ mapHeadTail ("    ) " ++) id (pretty x)
    pretty (ForIn v e x) = assert_total $ case (pretty v, pretty e) of
      (([v'] ** IsNonEmpty), ([e'] ** IsNonEmpty)) =>
        mapHeadTail (("for (" ++ e' ++ " in " ++ e' ++ ") ") ++) id $ pretty x
      (v', e') =>
        mapHeadTail ("for (  " ++) (indent 7) v'
        ++ mapHeadTail ("    in " ++) (indent 7) e'
        ++ mapHeadTail ("    ) " ++) id (pretty x)
    pretty Break = ["break;"]
    pretty Continue = ["continue;"]
    pretty (Return x) = assert_total $ mapHeadTail ("return " ++) (indent 2) $ mapInitLast id (++ ";") $ pretty x

