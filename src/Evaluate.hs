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
  ELam {} -> Val
  EPair left right ->
    (left, (`EPair` right)) |-> \() ->
      (right, EPair left) |-> \() ->
        Val
  EInject e d mt ->
    (e, \e' -> EInject e' d mt) |-> \() ->
      Val
  EAddop op left right ->
    (left, \left' -> EAddop op left' right) |-> \() ->
      (right, EAddop op left) |-> \() ->
        case (left, right, op) of
          (ENum l, ENum r, Add) -> Step (ENum (l + r))
          (ENum l, ENum r, Sub) -> Step (ENum (l - r))
  EMulop op left right ->
    (left, \left' -> EMulop op left' right) |-> \() ->
      (right, EMulop op left) |-> \() ->
        case (left, right, op) of
          (ENum l, ENum r, Mul) -> Step (ENum (l * r))
          (ENum l, ENum r, Div) -> Step (ENum (l `div` r))
  ERelop op left right ->
    (left, \left' -> ERelop op left' right) |-> \() ->
      (right, ERelop op left) |-> \() ->
        case (left, right, op) of
          (ENum l, ENum r, Lt) -> Step (if l < r then ETrue else EFalse)
          (ENum l, ENum r, Gt) -> Step (if l > r then ETrue else EFalse)
          (ENum l, ENum r, Eq) -> Step (if l == r then ETrue else EFalse)
  EIf cond then_ else_ ->
    (cond, \cond' -> EIf cond' then_ else_) |-> \() ->
      case cond of
        ETrue -> Step then_
        EFalse -> Step else_
  EAnd left right ->
    (left, (`EAnd` right)) |-> \() ->
      case left of
        ETrue -> Step right
        EFalse -> Step EFalse
  EOr left right ->
    (left, (`EOr` right)) |-> \() ->
      case left of
        ETrue -> Step ETrue
        EFalse -> Step right
  EApp lam arg ->
    (lam, (`EApp` arg)) |-> \() ->
      (arg, EApp lam) |-> \() ->
        case lam of
          ELam _ _ body -> Step (deBruijnSubst 0 arg body)
  EProject e d ->
    (e, (`EProject` d)) |-> \() ->
      case e of
        EPair l _ | d == L -> Step l
        EPair _ r | d == R -> Step r
  ECase e _ eleft _ eright ->
    (e, \e' -> ECase e' (VName "_") eleft (VName "_") eright) |-> \() ->
      case e of
        EInject e' L _ -> Step (deBruijnSubst 0 e' eleft)
        EInject e' R _ -> Step (deBruijnSubst 0 e' eright)
  EFix _ body -> Step (deBruijnSubst 0 (EFix (VName "_") body) body)
  ELet _ _ e_x e_in ->
    (e_x, \e_x' -> ELet (VName "_") Nothing e_x' e_in) |-> \() ->
      Step (deBruijnSubst 0 e_x e_in)

(|->) :: (Expr, Expr -> Expr) -> (() -> Outcome) -> Outcome
(e, hole) |-> next = case tryStep e of
  Step e -> Step (hole e)
  Val -> next ()

deBruijnSubst :: Int -> Expr -> Expr -> Expr
deBruijnSubst k s (EVar (VDeBruijn i))
  | i == k = s
  | otherwise = EVar (VDeBruijn i)
deBruijnSubst k s (ELam x mt body) = ELam x mt (deBruijnSubst (k + 1) s body)
deBruijnSubst k s (EApp f a) = EApp (deBruijnSubst k s f) (deBruijnSubst k s a)
deBruijnSubst k s (EAddop op l r) = EAddop op (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EMulop op l r) = EMulop op (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (ERelop op l r) = ERelop op (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EIf c t f) = EIf (deBruijnSubst k s c) (deBruijnSubst k s t) (deBruijnSubst k s f)
deBruijnSubst k s (EAnd l r) = EAnd (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EOr l r) = EOr (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EPair l r) = EPair (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EProject e d) = EProject (deBruijnSubst k s e) d
deBruijnSubst k s (EInject e d mt) = EInject (deBruijnSubst k s e) d mt
deBruijnSubst k s (ECase e _ el _ er) =
  ECase (deBruijnSubst k s e) (VName "_") (deBruijnSubst (k + 1) s el) (VName "_") (deBruijnSubst (k + 1) s er)
deBruijnSubst k s (EFix _ body) = EFix (VName "_") (deBruijnSubst (k + 1) s body)
deBruijnSubst k s (ELet _ mt x e_in) = ELet (VName "_") mt (deBruijnSubst k s x) (deBruijnSubst (k + 1) s e_in)
deBruijnSubst _ _ e = e

eval :: Expr -> Expr
eval e = case tryStep e of
  Val -> e
  Step e' -> eval e'
