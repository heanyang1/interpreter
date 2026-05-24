module ASTUtil where

import AST
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

class Symbol a where
    toDebruijn :: a -> a
    toDebruijnMap :: Map Variable Int -> a -> a
    toDebruijn = toDebruijnMap Map.empty

instance Symbol Type where
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

