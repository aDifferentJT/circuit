module Language.Lefty.AST

%default total

mutual
  infix 6 ~=

  public export
  data Expression
    = NumberConstant Double
    | StringConstant String
    | Assign Variable Expression
    | (||) Expression Expression
    | (&&) Expression Expression
    | (==) Expression Expression
    | (~=) Expression Expression
    | (<) Expression Expression
    | (<=) Expression Expression
    | (>) Expression Expression
    | (>=) Expression Expression
    | (+) Expression Expression
    | (-) Expression Expression
    | (*) Expression Expression
    | (/) Expression Expression
    | Mod Expression Expression
    | FunctionDecl FunctionDeclaration
    | Table (List (Expression, Expression))

  public export
  data Variable
    = Identifier String
    | Subscript Variable Expression

  public export
  record FunctionDeclaration where
    constructor Function
    funcIdent : String
    args : List String
    locals : List String
    body : List Statement

  public export
  data Statement
    = TopLevel Expression
    | Nil
    | (::) Statement Statement
    | If Expression Statement (Maybe Statement)
    | While Expression Statement
    | CFor Expression Expression Expression Statement
    | ForIn Variable Expression Statement
    | Break
    | Continue
    | Return Expression

public export
fromInteger : Integer -> Expression
fromInteger = NumberConstant . fromInteger

syntax "if" "(" [cond] ")" [t] noelse = If cond t Nothing
syntax "if" "(" [cond] ")" [t] "else" [e] = If cond t (Just e)
syntax while "(" [cond] ")" [s] = While cond s
syntax for "(" [init] ";" [test] ";" [update] ")" [s] = CFor init test update s
syntax for "(" [v] "in" [e] ")" [s] = ForIn v e s

public export
break : Statement
break = Break

public export
continue : Statement
continue = Continue

public export
return : Expression -> Statement
return = Return

