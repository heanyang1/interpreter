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
  EDeBruijn _ -> Val
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
          ELam _ body -> Step (deBruijnSubst 0 arg body)
          _ -> error $ "unreachable state: lam=" ++ show lam
  EProject e d ->
    (e, (`EProject` d)) |-> \() ->
      case e of
        EPair l _ | d == L -> Step l
        EPair _ r | d == R -> Step r
        _ -> error $ "unreachable state: e=" ++ show e
  ECase e _ eleft _ eright ->
    (e, \e' -> ECase e' (Variable "_") eleft (Variable "_") eright) |-> \() ->
      case e of
        EInject e' L -> Step (deBruijnSubst 0 e' eleft)
        EInject e' R -> Step (deBruijnSubst 0 e' eright)
        _ -> error $ "unreachable state: e=" ++ show e
  EFix _ body -> Step (deBruijnSubst 0 (EFix (Variable "_") body) body)
  ELet _ e_x e_in ->
    (e_x, \e_x' -> ELet (Variable "_") e_x' e_in) |-> \() ->
      Step (deBruijnSubst 0 e_x e_in)

(|->) :: (Expr, Expr -> Expr) -> (() -> Outcome) -> Outcome
(e, hole) |-> next = case tryStep e of
  Step e -> Step (hole e)
  Val -> next ()

deBruijnSubst :: Int -> Expr -> Expr -> Expr
deBruijnSubst k s (EDeBruijn i)
    | i == k = deBruijnShift k s
    | i > k  = EDeBruijn (i - 1)
    | otherwise = EDeBruijn i
deBruijnSubst k s (ELam x body) = ELam x (deBruijnSubst (k + 1) s body)
deBruijnSubst k s (EApp f a) = EApp (deBruijnSubst k s f) (deBruijnSubst k s a)
deBruijnSubst k s (EAddop op l r) = EAddop op (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EMulop op l r) = EMulop op (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (ERelop op l r) = ERelop op (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EIf c t f) = EIf (deBruijnSubst k s c) (deBruijnSubst k s t) (deBruijnSubst k s f)
deBruijnSubst k s (EAnd l r) = EAnd (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EOr l r) = EOr (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EPair l r) = EPair (deBruijnSubst k s l) (deBruijnSubst k s r)
deBruijnSubst k s (EProject e d) = EProject (deBruijnSubst k s e) d
deBruijnSubst k s (EInject e d) = EInject (deBruijnSubst k s e) d
deBruijnSubst k s (ECase e _ el _ er) =
    ECase (deBruijnSubst k s e) (Variable "_") (deBruijnSubst (k + 1) s el) (Variable "_") (deBruijnSubst (k + 1) s er)
deBruijnSubst k s (EFix _ body) = EFix (Variable "_") (deBruijnSubst (k + 1) s body)
deBruijnSubst k s (ELet _ x e_in) = ELet (Variable "_") (deBruijnSubst k s x) (deBruijnSubst (k + 1) s e_in)
deBruijnSubst _ _ e = e

deBruijnShift :: Int -> Expr -> Expr
deBruijnShift c (EDeBruijn i)
    | i >= c = EDeBruijn (i + 1)
    | otherwise = EDeBruijn i
deBruijnShift c (ELam x body) = ELam x (deBruijnShift (c + 1) body)
deBruijnShift c (EApp f a) = EApp (deBruijnShift c f) (deBruijnShift c a)
deBruijnShift c (EAddop op l r) = EAddop op (deBruijnShift c l) (deBruijnShift c r)
deBruijnShift c (EMulop op l r) = EMulop op (deBruijnShift c l) (deBruijnShift c r)
deBruijnShift c (ERelop op l r) = ERelop op (deBruijnShift c l) (deBruijnShift c r)
deBruijnShift c (EIf cond t f) = EIf (deBruijnShift c cond) (deBruijnShift c t) (deBruijnShift c f)
deBruijnShift c (EAnd l r) = EAnd (deBruijnShift c l) (deBruijnShift c r)
deBruijnShift c (EOr l r) = EOr (deBruijnShift c l) (deBruijnShift c r)
deBruijnShift c (EPair l r) = EPair (deBruijnShift c l) (deBruijnShift c r)
deBruijnShift c (EProject e d) = EProject (deBruijnShift c e) d
deBruijnShift c (EInject e d) = EInject (deBruijnShift c e) d
deBruijnShift c (ECase e _ el _ er) =
    ECase (deBruijnShift c e) (Variable "_") (deBruijnShift (c + 1) el) (Variable "_") (deBruijnShift (c + 1) er)
deBruijnShift c (EFix _ body) = EFix (Variable "_") (deBruijnShift (c + 1) body)
deBruijnShift c (ELet _ x e_in) = ELet (Variable "_") (deBruijnShift c x) (deBruijnShift (c + 1) e_in)
deBruijnShift _ e = e

eval :: Expr -> Expr
eval e = case tryStep e of
    Val -> e
    Step e' -> eval e'
