module ASTUtil where

import AST
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List ((\\), union, foldl')
import Data.Maybe (fromMaybe)

class Symbol a where
    toDebruijn :: a -> a
    toDebruijnMap :: Map Variable Int -> a -> a
    toDebruijn = toDebruijnMap Map.empty
    containsVar :: Variable -> a -> Bool

addDepth :: Map Variable Int -> [Variable] -> Map Variable Int
addDepth = foldl (\ m v -> Map.insertWith (+) v 1 m)

instance Symbol Type where
    containsVar s t = case t of
        TNum -> False
        TBool -> False
        TUnit -> False
        TVar x -> x == s
        TProduct left right -> containsVar s left || containsVar s right
        TSum left right -> containsVar s left || containsVar s right
        TFn arg ret -> containsVar s arg || containsVar s ret
        TForall a tau -> a /= s && containsVar s tau

    toDebruijnMap depth t = case t of
        TNum -> t
        TBool -> t
        TUnit -> t
        TVar v -> case Map.lookup v depth of
            Nothing -> TVar v
            Just n -> TVar (Variable (show n))
        TProduct left right -> TProduct (toDebruijnMap depth left) (toDebruijnMap depth right)
        TSum left right -> TSum (toDebruijnMap depth left) (toDebruijnMap depth right)
        TFn arg ret -> TFn (toDebruijnMap depth arg) (toDebruijnMap depth ret)
        TForall a tau ->
            let newDepth = Map.insert a 0 (fmap (+1) depth)
            in TForall (Variable "_") (toDebruijnMap newDepth tau)

instance Symbol Expr where
    containsVar s e = case e of
        ENum _ -> False
        ETrue -> False
        EFalse -> False
        EUnit -> False
        EDeBruijn _ -> False
        EAddop _ left right -> containsVar s left || containsVar s right
        EMulop _ left right -> containsVar s left || containsVar s right
        EIf cond then_ else_ -> containsVar s cond || containsVar s then_ || containsVar s else_
        ERelop _ left right -> containsVar s left || containsVar s right
        EAnd left right -> containsVar s left || containsVar s right
        EOr left right -> containsVar s left || containsVar s right
        EVar v -> v == s
        ELam x e -> x /= s && containsVar s e
        EApp lam arg -> containsVar s lam || containsVar s arg
        EPair left right -> containsVar s left || containsVar s right
        EProject e _ -> containsVar s e
        EInject e _ -> containsVar s e
        ECase e xleft eleft xright eright ->
            containsVar s e || (xleft /= s && containsVar s eleft) || (xright /= s && containsVar s eright)
        EFix x e -> x /= s && containsVar s e
        ELet x e_x e_in -> containsVar s e_x || (x /= s && containsVar s e_in)

    toDebruijnMap depth e = case e of
        ENum _ -> e
        ETrue -> e
        EFalse -> e
        EUnit -> e
        EDeBruijn _ -> error "Should not have de Bruijn in input"
        EVar v -> case Map.lookup v depth of
            Nothing -> EVar v
            Just n -> EDeBruijn n
        ELam x e' ->
            let newDepth = Map.insert x 0 (fmap (+1) depth)
            in ELam (Variable "_") (toDebruijnMap newDepth e')
        EApp lam arg -> EApp (toDebruijnMap depth lam) (toDebruijnMap depth arg)
        EAddop op left right -> EAddop op (toDebruijnMap depth left) (toDebruijnMap depth right)
        EMulop op left right -> EMulop op (toDebruijnMap depth left) (toDebruijnMap depth right)
        ERelop op left right -> ERelop op (toDebruijnMap depth left) (toDebruijnMap depth right)
        EIf cond then_ else_ -> EIf (toDebruijnMap depth cond) (toDebruijnMap depth then_) (toDebruijnMap depth else_)
        EAnd left right -> EAnd (toDebruijnMap depth left) (toDebruijnMap depth right)
        EOr left right -> EOr (toDebruijnMap depth left) (toDebruijnMap depth right)
        EPair left right -> EPair (toDebruijnMap depth left) (toDebruijnMap depth right)
        EProject e d -> EProject (toDebruijnMap depth e) d
        EInject e d -> EInject (toDebruijnMap depth e) d
        ECase e' xleft eleft xright eright ->
            let depthLeft = Map.insert xleft 0 (fmap (+1) depth)
                depthRight = Map.insert xright 0 (fmap (+1) depth)
            in ECase (toDebruijnMap depth e')
                     (Variable "_")
                     (toDebruijnMap depthLeft eleft)
                     (Variable "_")
                     (toDebruijnMap depthRight eright)
        EFix x e' ->
            let newDepth = Map.insert x 0 (fmap (+1) depth)
            in EFix (Variable "_") (toDebruijnMap newDepth e')
        ELet x e_x e_in ->
            let depthX = Map.insert x 0 (fmap (+1) depth)
            in ELet (Variable "_") (toDebruijnMap depth e_x) (toDebruijnMap depthX e_in)

getAllVars :: Type -> [Variable]
getAllVars t = case t of
    TNum -> []
    TBool -> []
    TUnit -> []
    TVar v -> [v]
    TProduct left right -> getAllVars left ++ getAllVars right
    TSum left right -> getAllVars left ++ getAllVars right
    TFn arg ret -> getAllVars arg ++ getAllVars ret
    TForall a tau -> a : getAllVars tau

getScopedVars :: Type -> [Variable]
getScopedVars t = case t of
    TNum -> []
    TBool -> []
    TUnit -> []
    TVar _ -> []
    TProduct left right -> getScopedVars left ++ getScopedVars right
    TSum left right -> getScopedVars left ++ getScopedVars right
    TFn arg ret -> getScopedVars arg ++ getScopedVars ret
    TForall a tau -> a : getScopedVars tau

getFreeVars :: Type -> [Variable]
getFreeVars t = filter (`notElem` getScopedVars t) (getAllVars t)

addOneQuantifier :: Type -> Variable -> Type
addOneQuantifier t a = TForall a t

