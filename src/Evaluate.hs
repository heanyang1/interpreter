module Evaluate where

import AST
import ASTUtil (Symbol(..))

eval :: Expr -> Expr
eval e = case e of
    EDeBruijn _ -> error "DeBruijn index should not appear in evaluation"
    EVar x -> error $ "Free variable " ++ show x ++ " should be caught by type checking"
    ENum _ -> e
    ETrue -> e
    EFalse -> e
    EUnit -> e
    ELam _ _ -> e
    EPair _ _ -> e
    EInject _ _ -> e

    EAddop op left right ->
        case (eval left, eval right, op) of
            (ENum l, ENum r, Add) -> ENum (l + r)
            (ENum l, ENum r, Sub) -> ENum (l - r)
            _ -> error "type error in addition"

    EMulop op left right ->
        case (eval left, eval right, op) of
            (ENum l, ENum r, Mul) -> ENum (l * r)
            (ENum l, ENum r, Div) -> ENum (l `div` r)
            _ -> error "type error in multiplication"

    ERelop op left right ->
        case (eval left, eval right, op) of
            (ENum l, ENum r, Lt) -> if l < r then ETrue else EFalse
            (ENum l, ENum r, Gt) -> if l > r then ETrue else EFalse
            (ENum l, ENum r, Eq) -> if l == r then ETrue else EFalse
            _ -> error "type error in relation"

    EIf cond then_ else_ ->
        case eval cond of
            ETrue -> eval then_
            EFalse -> eval else_
            _ -> error "type error in if"

    EAnd left right ->
        case eval left of
            ETrue -> case eval right of
                ETrue -> ETrue
                _ -> EFalse
            EFalse -> EFalse
            _ -> error "type error in &&"

    EOr left right ->
        case eval left of
            ETrue -> ETrue
            EFalse -> case eval right of
                EFalse -> EFalse
                _ -> ETrue
            _ -> error "type error in ||"

    EApp lam arg ->
        case eval lam of
            ELam x body -> eval (substitute x (eval arg) body)
            _ -> error "type error in application"

    EProject e d ->
        case eval e of
            EPair l _ | d == L -> eval l
            EPair _ r | d == R -> eval r
            _ -> error "type error in projection"

    ECase e xleft eleft xright eright ->
        case eval e of
            EInject e' L -> eval (substitute xleft e' eleft)
            EInject e' R -> eval (substitute xright e' eright)
            _ -> error "type error in case"

    EFix x body -> eval (substitute x (EFix x body) body)

    ELet x e_x e_in -> eval (EApp (ELam x e_in) e_x)
