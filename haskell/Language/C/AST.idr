module Language.C.AST

import Data.HVect

Identifier : Type
Identifier = String

data CType : Type where
  Const : CType -> CType

  Array : CType -> CType
  Pointer : CType -> CType

  Struct : List (Identifier, CType) -> CType
  Union : List (Identifier, CType) -> CType

  Enum : List Identifier -> CType

  Function : Vect n CType -> CType -> CType

  Void : CType

  C_Char : CType
  C_SChar : CType
  C_UChar : CType
  C_Short : CType
  C_UShort : CType
  C_Int : CType
  C_UInt : CType
  C_Long : CType
  C_ULong : CType
  C_LongLong : CType
  C_ULongLong : CType
  C_Float : CType
  C_Double : CType
  C_LongDouble : CType

data IsArray : CType -> CType -> Type where
  ArrayIsArray : IsArray (Array t) t
  PointerIsArray : IsArray (Pointer t) t

data HasMember : CType -> Identifier -> CType -> Type where
  StructHasMemberHere : HasMember (Struct ((i, t) :: ms)) i t
  StructHasMemberThere : HasMember (Struct ms) i t -> HasMember (Struct (m::ms)) i t
  UnionHasMemberHere : HasMember (Union ((i, t) :: ms)) i t
  UnionHasMemberThere : HasMember (Union ms) i t -> HasMember (Union (m::ms)) i t

data IsIntegral : CType -> Type where
  C_CharIsIntegral : IsIntegral C_Char
  C_SCharIsIntegral : IsIntegral C_SChar
  C_UCharIsIntegral : IsIntegral C_UChar
  C_ShortIsIntegral : IsIntegral C_Short
  C_UShortIsIntegral : IsIntegral C_UShort
  C_IntIsIntegral : IsIntegral C_Int
  C_UIntIsIntegral : IsIntegral C_UInt
  C_LongIsIntegral : IsIntegral C_Long
  C_ULongIsIntegral : IsIntegral C_ULong
  C_LongLongIsIntegral : IsIntegral C_LongLong
  C_ULongLongIsIntegral : IsIntegral C_ULongLong

data IsNumeric : CType -> Type where
  IntegralIsNumeric : IsIntegral t -> IsNumeric t
  C_FloatIsNumeric : IsNumeric C_Float
  C_DoubleIsNumeric : IsNumeric C_Double
  C_LongDoubleIsNumeric : IsNumeric C_LongDouble

data Constant : CType -> Type

data InScope : Identifier -> CType -> Type

mutual
  infixl 9 -|>
  infixl 9 %%
  infixl 6 !=
  infixl 9 &
  infixl 9 ^
  infixl 9 |-
  infixl 9 :=
  infixl 9 *=
  infixl 9 %=
  infixl 9 +=
  infixl 9 -=
  infixl 9 <<=
  infixl 9 &=
  infixl 9 ^=
  infixl 9 |=

  data Expression : CType -> Type where
    Ident : (i : Identifier) -> {auto inScope : InScope i t} -> Expression t
    ConstantExpr : Constant t -> Expression t
    StringLiteral : String -> Expression (Array (Const C_Char))
    Subscript : {auto isArray : IsArray arr elem} -> {auto isIntegral : IsIntegral index} -> Expression arr -> Expression index -> Expression elem
    Call : Expression (Function args ret) -> HVect (map Expression args) -> Expression ret
    (.) : Expression t1 -> (i : Identifier) -> {auto hasMember : HasMember t1 i t2} -> Expression t2
    (-|>) : Expression (Pointer t1) -> (i : Identifier) -> {auto hasMember : HasMember t1 i t2} -> Expression t2
    PostInc : {auto isNumeric : IsNumeric t} -> (e : Expression t) -> {auto isLValue : IsLValue e} -> Expression t
    PostDec : {auto isNumeric : IsNumeric t} -> (e : Expression t) -> {auto isLValue : IsLValue e} -> Expression t
    PreInc : {auto isNumeric : IsNumeric t} -> (e : Expression t) -> {auto isLValue : IsLValue e} -> Expression t
    PreDec : {auto isNumeric : IsNumeric t} -> (e : Expression t) -> {auto isLValue : IsLValue e} -> Expression t
    AddressOf : Expression t -> Expression (Pointer t)
    Deref : Expression (Pointer t) -> Expression t
    Positive : {auto isNumeric : IsNumeric t} -> Expression t -> Expression t
    Negation : {auto isNumeric : IsNumeric t} -> Expression t -> Expression t
    BitwiseNot : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t
    LogicalNot : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t
    SizeOfExpr : {auto isIntegral : IsIntegral t2} -> Expression t1 -> Expression t2
    SizeOfType : {auto isIntegral : IsIntegral t} -> CType -> Expression t
    Cast : (t : CType) -> Expression t' -> Expression t
    (*) : {auto isNumeric : IsNumeric t} -> Expression t -> Expression t -> Expression t
    (/) : {auto isNumeric : IsNumeric t} -> Expression t -> Expression t -> Expression t
    (%%) : {auto isNumeric : IsNumeric t} -> Expression t -> Expression t -> Expression t
    (+) : {auto isNumeric : IsNumeric t} -> Expression t -> Expression t -> Expression t
    (-) : {auto isNumeric : IsNumeric t} -> Expression t -> Expression t -> Expression t
    (<<) : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t -> Expression t
    (>>) : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t -> Expression t
    (<) : {auto isNumeric : IsNumeric t1} -> {auto isIntegral : IsIntegral t2} -> Expression t1 -> Expression t1 -> Expression t2
    (>) : {auto isNumeric : IsNumeric t1} -> {auto isIntegral : IsIntegral t2} -> Expression t1 -> Expression t1 -> Expression t2
    (>=) : {auto isNumeric : IsNumeric t1} -> {auto isIntegral : IsIntegral t2} -> Expression t1 -> Expression t1 -> Expression t2
    (<=) : {auto isNumeric : IsNumeric t1} -> {auto isIntegral : IsIntegral t2} -> Expression t1 -> Expression t1 -> Expression t2
    (==) : {auto isIntegral : IsIntegral t2} -> Expression t1 -> Expression t1 -> Expression t2
    (!=) : {auto isIntegral : IsIntegral t2} -> Expression t1 -> Expression t1 -> Expression t2
    (&) : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t -> Expression t
    (^) : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t -> Expression t
    (|-) : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t -> Expression t
    (&&) : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t -> Expression t
    (||) : {auto isIntegral : IsIntegral t} -> Expression t -> Expression t -> Expression t
    Ternary : {auto isIntegral : IsIntegral t1} -> Expression t1 -> Expression t2 -> Expression t2 -> Expression t2
    (:=) : (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t -> Expression t
    (*=) : {auto isNumeric : IsNumeric t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (/=) : {auto isNumeric : IsNumeric t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (%=) : {auto isNumeric : IsNumeric t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (+=) : {auto isNumeric : IsNumeric t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (-=) : {auto isNumeric : IsNumeric t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (<<=) : {auto isIntegral : IsIntegral t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (>>=) : {auto isIntegral : IsIntegral t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (&=) : {auto isIntegral : IsIntegral t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (^=) : {auto isIntegral : IsIntegral t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    (|=) : {auto isIntegral : IsIntegral t} -> (l : Expression t) -> {auto isLValue : IsLValue l} -> Expression t
    Comma : Expression t1 -> Expression t2 -> Expression t2

  data IsLValue : Expression t -> Type where
    IdentIsLValue : {auto inScope : InScope i t} -> IsLValue (Ident i)
    SubscriptIsLValue : IsLValue (Subscript xs i) --Shouldn't be array
    DerefIsLValue : IsLValue (Deref x) --Shouldn't be array
    

