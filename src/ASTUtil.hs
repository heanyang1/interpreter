module ASTUtil where

import AST
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

class Symbol a where
  toDebruijn :: a -> a
  toDebruijnMap :: Map String Int -> a -> a
  toDebruijn = toDebruijnMap Map.empty

instance Symbol Type where
  toDebruijnMap depth t = case t of
    TNum -> t
    TBool -> t
    TUnit -> t
    TVar (VName v) -> case Map.lookup v depth of
      Nothing -> TVar (VName v)
      Just n -> TVar (VDeBruijn n)
    TVar n@(VDeBruijn _) -> TVar n
    TProduct left right -> TProduct (toDebruijnMap depth left) (toDebruijnMap depth right)
    TSum left right -> TSum (toDebruijnMap depth left) (toDebruijnMap depth right)
    TFn arg ret -> TFn (toDebruijnMap depth arg) (toDebruijnMap depth ret)
    TForall (VName a) tau ->
      let newDepth = Map.insert a 0 (fmap (+ 1) depth)
       in TForall (VName "_") (toDebruijnMap newDepth tau)
    TMu (VName a) body ->
      let newDepth = Map.insert a 0 (fmap (+ 1) depth)
       in TMu (VName "_") (toDebruijnMap newDepth body)

instance Symbol Expr where
  toDebruijnMap depth e = case e of
    ENum _ -> e
    ETrue -> e
    EFalse -> e
    EUnit -> e
    EVar (VName v) -> case Map.lookup v depth of
      Nothing -> EVar (VName v)
      Just n -> EVar (VDeBruijn n)
    EVar n -> EVar n
    ELam (VName x) mt e' ->
      let newDepth = Map.insert x 0 (fmap (+ 1) depth)
       in ELam (VName "_") (fmap toDebruijn mt) (toDebruijnMap newDepth e')
    EApp lam arg -> EApp (toDebruijnMap depth lam) (toDebruijnMap depth arg)
    EAddop op left right -> EAddop op (toDebruijnMap depth left) (toDebruijnMap depth right)
    EMulop op left right -> EMulop op (toDebruijnMap depth left) (toDebruijnMap depth right)
    ERelop op left right -> ERelop op (toDebruijnMap depth left) (toDebruijnMap depth right)
    EIf cond then_ else_ -> EIf (toDebruijnMap depth cond) (toDebruijnMap depth then_) (toDebruijnMap depth else_)
    EAnd left right -> EAnd (toDebruijnMap depth left) (toDebruijnMap depth right)
    EOr left right -> EOr (toDebruijnMap depth left) (toDebruijnMap depth right)
    EPair left right -> EPair (toDebruijnMap depth left) (toDebruijnMap depth right)
    EProject e d -> EProject (toDebruijnMap depth e) d
    EInject e d mt -> EInject (toDebruijnMap depth e) d (fmap toDebruijn mt)
    ECase e' (VName xleft) eleft (VName xright) eright ->
      let depthLeft = Map.insert xleft 0 (fmap (+ 1) depth)
          depthRight = Map.insert xright 0 (fmap (+ 1) depth)
       in ECase
            (toDebruijnMap depth e')
            (VName "_")
            (toDebruijnMap depthLeft eleft)
            (VName "_")
            (toDebruijnMap depthRight eright)
    EFix (VName x) e' ->
      let newDepth = Map.insert x 0 (fmap (+ 1) depth)
       in EFix (VName "_") (toDebruijnMap newDepth e')
    ELet (VName x) mt e_x e_in ->
      let depthX = Map.insert x 0 (fmap (+ 1) depth)
       in ELet (VName "_") (fmap toDebruijn mt) (toDebruijnMap depth e_x) (toDebruijnMap depthX e_in)

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
  TMu a body -> a : getAllVars body

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
  TMu a body -> a : getScopedVars body

getFreeVars :: Type -> [Variable]
getFreeVars t = filter (`notElem` getScopedVars t) (getAllVars t)
