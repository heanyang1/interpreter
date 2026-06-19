module AST where

data Variable
  = VName String
  | VDeBruijn Int
  deriving (Eq, Ord)

instance Show Variable where
  show (VName n) = n
  show (VDeBruijn n) = "<" ++ show n ++ ">"

data Type
  = TNum
  | TBool
  | TUnit
  | TVar Variable
  | TFn Type Type
  | TProduct Type Type
  | TSum Type Type
  | TForall Variable Type
  | TMu Variable Type
  deriving (Eq)

instance Show Type where
  show TNum = "num"
  show TBool = "bool"
  show TUnit = "()"
  show (TVar v) = show v
  show (TFn arg ret) = "(" ++ show arg ++ " → " ++ show ret ++ ")"
  show (TProduct left right) = show left ++ " * " ++ show right
  show (TSum left right) = show left ++ " + " ++ show right
  show (TForall a tau) = "∀ " ++ show a ++ " . " ++ show tau
  show (TMu a body) = "(μ " ++ show a ++ " . " ++ show body ++ ")"

data AddOp = Add | Sub
  deriving (Eq)

instance Show AddOp where
  show Add = "+"
  show Sub = "-"

data MulOp = Mul | Div
  deriving (Eq)

instance Show MulOp where
  show Mul = "*"
  show Div = "/"

data RelOp = Lt | Gt | Eq
  deriving (Eq)

instance Show RelOp where
  show Lt = "<"
  show Gt = ">"
  show Eq = "="

data Direction = L | R
  deriving (Eq, Show)

data Expr
  = ENum Int
  | EAddop AddOp Expr Expr
  | EMulop MulOp Expr Expr
  | ETrue
  | EFalse
  | EIf Expr Expr Expr
  | ERelop RelOp Expr Expr
  | EAnd Expr Expr
  | EOr Expr Expr
  | EVar Variable
  | ELam Variable (Maybe Type) Expr
  | EApp Expr Expr
  | EUnit
  | EPair Expr Expr
  | EProject Expr Direction
  | EInject Expr Direction (Maybe Type)
  | ECase
      { e :: Expr,
        xleft :: Variable,
        eleft :: Expr,
        xright :: Variable,
        eright :: Expr
      }
  | EFix Variable Expr
  | ELet Variable (Maybe Type) Expr Expr
  deriving (Eq)

instance Show Expr where
  show (EVar v) = show v
  show (ENum n) = show n
  show ETrue = "true"
  show EFalse = "false"
  show EUnit = "()"
  show (EAddop op left right) = "(" ++ show left ++ " " ++ show op ++ " " ++ show right ++ ")"
  show (EMulop op left right) = "(" ++ show left ++ " " ++ show op ++ " " ++ show right ++ ")"
  show (EIf cond then_ else_) = "(if " ++ show cond ++ " then " ++ show then_ ++ " else " ++ show else_ ++ ")"
  show (ERelop op left right) = "(" ++ show left ++ " " ++ show op ++ " " ++ show right ++ ")"
  show (EAnd left right) = "(" ++ show left ++ " && " ++ show right ++ ")"
  show (EOr left right) = "(" ++ show left ++ " || " ++ show right ++ ")"
  show (EPair left right) = "(" ++ show left ++ " , " ++ show right ++ ")"
  show (EProject e d) = case (e, d) of
    (EPair left _, L) -> show left
    (EPair _ right, R) -> show right
    _ -> show e ++ "." ++ show d
  show (EInject e d Nothing) = show e
  show (EInject e d (Just t)) = "(inj " ++ show e ++ " = " ++ show d ++ " as " ++ show t ++ ")"
  show (ECase e xleft eleft xright eright) =
    "(case " ++ show e ++ " of L(" ++ show xleft ++ ") -> " ++ show eleft ++ " | R(" ++ show xright ++ ") -> " ++ show eright ++ ")"
  show (EApp lam arg) = "(" ++ show lam ++ " " ++ show arg ++ ")"
  show (ELam x Nothing e) = "(λ " ++ show x ++ " -> " ++ show e ++ ")"
  show (ELam x (Just t) e) = "(λ " ++ show x ++ " : " ++ show t ++ " -> " ++ show e ++ ")"
  show (ELet x Nothing e_x e_in) = "(let " ++ show x ++ " = " ++ show e_x ++ " in " ++ show e_in ++ ")"
  show (ELet x (Just t) e_x e_in) = "(let " ++ show x ++ " : " ++ show t ++ " = " ++ show e_x ++ " in " ++ show e_in ++ ")"
  show (EFix x e) = "(fix " ++ show x ++ " -> " ++ show e ++ ")"

showSimplified :: Expr -> String
showSimplified (EVar v) = show v
showSimplified (ENum n) = show n
showSimplified ETrue = "true"
showSimplified EFalse = "false"
showSimplified EUnit = "()"
showSimplified (EAddop op left right) = "(" ++ showSimplified left ++ " " ++ show op ++ " " ++ showSimplified right ++ ")"
showSimplified (EMulop op left right) = "(" ++ showSimplified left ++ " " ++ show op ++ " " ++ showSimplified right ++ ")"
showSimplified (EIf cond then_ else_) = "(if " ++ showSimplified cond ++ " then " ++ showSimplified then_ ++ " else " ++ showSimplified else_ ++ ")"
showSimplified (ERelop op left right) = "(" ++ showSimplified left ++ " " ++ show op ++ " " ++ showSimplified right ++ ")"
showSimplified (EAnd left right) = "(" ++ showSimplified left ++ " && " ++ showSimplified right ++ ")"
showSimplified (EOr left right) = "(" ++ showSimplified left ++ " || " ++ showSimplified right ++ ")"
showSimplified (EPair left right) = "(" ++ showSimplified left ++ " , " ++ showSimplified right ++ ")"
showSimplified (EProject e d) = case (e, d) of
  (EPair left _, L) -> showSimplified left
  (EPair _ right, R) -> showSimplified right
  _ -> showSimplified e ++ "." ++ show d
showSimplified (EInject e _ _) = showSimplified e
showSimplified (ECase e xleft eleft xright eright) =
  "(case " ++ showSimplified e ++ " of L(" ++ show xleft ++ ") -> " ++ showSimplified eleft ++ " | R(" ++ show xright ++ ") -> " ++ showSimplified eright ++ ")"
showSimplified (EApp lam arg) = "(" ++ showSimplified lam ++ " " ++ showSimplified arg ++ ")"
showSimplified (ELam x _ e) = "(λ " ++ show x ++ " -> " ++ showSimplified e ++ ")"
showSimplified (ELet x _ e_x e_in) = "(let " ++ show x ++ " = " ++ showSimplified e_x ++ " in " ++ showSimplified e_in ++ ")"
showSimplified (EFix x e) = "(fix " ++ show x ++ " -> " ++ showSimplified e ++ ")"