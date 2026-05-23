module Evaluate where

import AST
import ASTUtil (Symbol (..))

data Outcome = Val | Step Expr

tryStep :: Expr -> Outcome
tryStep e = case e of
  ENum _ -> Val
  ETrue -> Val
  EFalse -> Val
  EUnit -> Val
  ELam _ _ -> Val
  EPair _ _ -> Val
  EInject _ _ -> Val
  EVar x -> error $ "Free variable " ++ show x ++ " should be caught by type checking"
  EDeBruijn _ -> error "DeBruijn index should not appear in evaluation"
  EAddop op left right ->
    (left, \left' -> EAddop op left' right) |-> \() ->
      (right, EAddop op left) |-> \() ->
        case (left, right, op) of
          (ENum l, ENum r, Add) -> Step (ENum (l + r))
          (ENum l, ENum r, Sub) -> Step (ENum (l - r))
          _ -> error $ "unreachable state: left=" ++ show left ++ "right=" ++ show right ++ "op=" ++ show op
  EMulop op left right ->
    (left, \left' -> EMulop op left' right) |-> \() ->
      (right, EMulop op left) |-> \() ->
        case (left, right, op) of
          (ENum l, ENum r, Mul) -> Step (ENum (l * r))
          (ENum l, ENum r, Div) -> Step (ENum (l `div` r))
          _ -> error $ "unreachable state: left=" ++ show left ++ "right=" ++ show right ++ "op=" ++ show op
  ERelop op left right ->
    (left, \left' -> ERelop op left' right) |-> \() ->
      (right, ERelop op left) |-> \() ->
        case (left, right, op) of
          (ENum l, ENum r, Lt) -> Step (if l < r then ETrue else EFalse)
          (ENum l, ENum r, Gt) -> Step (if l > r then ETrue else EFalse)
          (ENum l, ENum r, Eq) -> Step (if l == r then ETrue else EFalse)
          _ -> error $ "unreachable state: left=" ++ show left ++ "right=" ++ show right ++ "op=" ++ show op
  EIf cond then_ else_ ->
    (cond, \cond' -> EIf cond' then_ else_) |-> \() ->
      case cond of
        ETrue -> Step then_
        EFalse -> Step else_
        _ -> error $ "unreachable state: cond=" ++ show cond
  EAnd left right ->
    (left, (`EAnd` right)) |-> \() ->
      case left of
        ETrue -> Step right
        EFalse -> Step EFalse
        _ -> error $ "unreachable state: left=" ++ show left
  EOr left right ->
    (left, (`EOr` right)) |-> \() ->
      case left of
        ETrue -> Step ETrue
        EFalse -> Step right
        _ -> error $ "unreachable state: left=" ++ show left
  EApp lam arg ->
    (lam, (`EApp` arg)) |-> \() ->
      (arg, EApp lam) |-> \() ->
        case lam of
          ELam x body -> Step (substitute x arg body)
          _ -> error $ "unreachable state: lam=" ++ show lam
  EProject e d ->
    (e, (`EProject` d)) |-> \() ->
      case e of
        EPair l _ | d == L -> Step l
        EPair _ r | d == R -> Step r
        _ -> error $ "unreachable state: e=" ++ show e
  ECase e xleft eleft xright eright ->
    (e, \e' -> ECase e' xleft eleft xright eright) |-> \() ->
      case e of
        EInject e' L -> Step (substitute xleft e' eleft)
        EInject e' R -> Step (substitute xright e' eright)
        _ -> error $ "unreachable state: e=" ++ show e
  EFix x body -> Step (substitute x (EFix x body) body)
  ELet x e_x e_in ->
    (e_x, \e_x' -> ELet x e_x' e_in) |-> \() ->
      Step (substitute x e_x e_in)

(|->) :: (Expr, Expr -> Expr) -> (() -> Outcome) -> Outcome
(e, hole) |-> next = case tryStep e of
  Step e -> Step (hole e)
  Val -> next ()

eval :: Expr -> Expr
eval e = case tryStep e of
  Val -> e
  Step e' -> eval e'
