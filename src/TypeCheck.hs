module TypeCheck where

import AST
import ASTUtil
import Control.Monad (unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict hiding (put)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)
import Flags (Mode (..))
import UnionFind

data Constraint = Constraint
  { typeL :: Type,
    typeR :: Type
  }
  deriving (Eq)

instance Show Constraint where
  show c = show (typeL c) ++ " = " ++ show (typeR c)

formatConstraints :: [Constraint] -> String
formatConstraints [] = "No constraints."
formatConstraints cs =
  "Constraints:\n"
    ++ unlines ["  " ++ show c | c <- cs]

type VarId = Int

type TCM a = StateT VarId (Either String) a

freshTypeVar :: TCM Type
freshTypeVar = do
  n <- get
  modify (+ 1)
  return $ TVar (VName ("type_" ++ show n))

instantiate :: Type -> TCM Type
instantiate t = case t of
  TNum -> return t
  TBool -> return t
  TUnit -> return t
  TVar _ -> return t
  TFn a r -> TFn <$> instantiate a <*> instantiate r
  TProduct l r -> TProduct <$> instantiate l <*> instantiate r
  TSum l r -> TSum <$> instantiate l <*> instantiate r
  TForall a tau -> do
    newVar <- freshTypeVar
    subst <- instantiate tau
    return (substituteMapVar (Map.singleton a newVar) subst)
  TMu a body -> TMu a <$> instantiate body

typeCheck :: Mode -> Expr -> Either String Type
typeCheck mode expr = do
  let result0 = runStateT (getConstraints expr []) 0
  case result0 of
    Left err -> Left err
    Right ((curType, constraints), _) -> do
      () <- if mode == VeryVerbose then trace (formatConstraints constraints) (Right ()) else Right ()
      (uf, mp) <- unification constraints
      let result = getType curType uf mp
      unless (null (getFreeVars result)) $
        Left "Free variables remain in type"
      return result

getConstraints :: Expr -> [Type] -> TCM (Type, [Constraint])
getConstraints expr ctx = case expr of
  ENum _ -> return (TNum, [])
  ETrue -> return (TBool, [])
  EFalse -> return (TBool, [])
  EAddop _ left right -> do
    (tauLeft, cLeft) <- getConstraints left ctx
    (tauRight, cRight) <- getConstraints right ctx
    let constraints =
          cLeft
            ++ cRight
            ++ [ Constraint tauLeft TNum,
                 Constraint tauRight TNum
               ]
    return (TNum, constraints)
  EMulop _ left right -> do
    (tauLeft, cLeft) <- getConstraints left ctx
    (tauRight, cRight) <- getConstraints right ctx
    let constraints =
          cLeft
            ++ cRight
            ++ [ Constraint tauLeft TNum,
                 Constraint tauRight TNum
               ]
    return (TNum, constraints)
  ERelop _ left right -> do
    (tauLeft, cLeft) <- getConstraints left ctx
    (tauRight, cRight) <- getConstraints right ctx
    let constraints =
          cLeft
            ++ cRight
            ++ [ Constraint tauLeft TNum,
                 Constraint tauRight TNum
               ]
    return (TBool, constraints)
  EIf cond then_ else_ -> do
    (tauCond, cCond) <- getConstraints cond ctx
    (tauThen, cThen) <- getConstraints then_ ctx
    (tauElse, cElse) <- getConstraints else_ ctx
    let constraints =
          cCond
            ++ cThen
            ++ cElse
            ++ [ Constraint tauCond TBool,
                 Constraint tauThen tauElse
               ]
    return (tauThen, constraints)
  EAnd left right -> do
    (tauLeft, cLeft) <- getConstraints left ctx
    (tauRight, cRight) <- getConstraints right ctx
    let constraints =
          cLeft
            ++ cRight
            ++ [ Constraint tauLeft TBool,
                 Constraint tauRight TBool
               ]
    return (TBool, constraints)
  EOr left right -> do
    (tauLeft, cLeft) <- getConstraints left ctx
    (tauRight, cRight) <- getConstraints right ctx
    let constraints =
          cLeft
            ++ cRight
            ++ [ Constraint tauLeft TBool,
                 Constraint tauRight TBool
               ]
    return (TBool, constraints)
  EVar (VName x) -> lift $ Left $ "Free variable: " ++ show x
  EVar (VDeBruijn depth) -> do
    let ctxLen = length ctx
    if depth >= ctxLen
      then lift $ Left "DeBruijn index out of bounds"
      else do
        let ty = ctx !! (ctxLen - 1 - depth)
        instTy <- instantiate ty
        return (instTy, [])
  ELam _ mt e -> do
    tauX <- maybe freshTypeVar return mt
    let ctx' = ctx ++ [tauX]
    (tauRet, cRet) <- getConstraints e ctx'
    return (TFn tauX tauRet, cRet)
  EApp lam arg -> do
    (tauLam, cLam) <- getConstraints lam ctx
    (tauArg, cArg) <- getConstraints arg ctx
    tauRet <- freshTypeVar
    let constraints =
          cLam
            ++ cArg
            ++ [Constraint tauLam (TFn tauArg tauRet)]
    return (tauRet, constraints)
  EPair left right -> do
    (tauL, cL) <- getConstraints left ctx
    (tauR, cR) <- getConstraints right ctx
    return (TProduct tauL tauR, cL ++ cR)
  EProject e d -> do
    (tauE, cE) <- getConstraints e ctx
    tauL <- freshTypeVar
    tauR <- freshTypeVar
    let constraints =
          cE
            ++ [Constraint tauE (TProduct tauL tauR)]
    return (case d of L -> tauL; R -> tauR, constraints)
  EUnit -> return (TUnit, [])
  EInject e d mt -> do
    (tauE, cE) <- getConstraints e ctx
    case mt of
      Just (TSum tauL tauR) -> do
        let tauFull = case d of
              L -> TSum tauE tauR
              R -> TSum tauL tauE
        let extra = Constraint tauE (case d of L -> tauL; R -> tauR)
        return (tauFull, cE ++ [extra])
      Just _ -> lift $ Left "Injection annotation must be a sum type"
      Nothing -> do
        tauOther <- freshTypeVar
        let tauFull = case d of
              L -> TSum tauE tauOther
              R -> TSum tauOther tauE
        return (tauFull, cE)
  ECase e xleft eleft xright eright -> do
    (tauSum, cSum) <- getConstraints e ctx
    tauL <- freshTypeVar
    tauR <- freshTypeVar

    let ctxL = ctx ++ [tauL]
    (tauLAfter, cL) <- getConstraints eleft ctxL
    let ctxR = ctx ++ [tauR]
    (tauRAfter, cR) <- getConstraints eright ctxR

    let constraints =
          cSum
            ++ cL
            ++ cR
            ++ [ Constraint tauSum (TSum tauL tauR),
                 Constraint tauLAfter tauRAfter
               ]
    return (tauLAfter, constraints)
  EFix _ e -> do
    tauX <- freshTypeVar
    let ctx' = ctx ++ [tauX]
    (tauE, cE) <- getConstraints e ctx'
    let constraints = cE ++ [Constraint tauX tauE]
    return (tauX, constraints)
  ELet x mt e_x e_in -> do
    (tauX, cX) <- getConstraints e_x ctx
    (tauXGen, cX') <- case mt of
      Just (TForall v body) -> do
        newVar <- freshTypeVar
        let body' = substituteMapVar (Map.singleton v newVar) body
        let cX' = cX ++ [Constraint tauX body']
        tauXGen <- lift $ generalize tauX cX'
        return (tauXGen, cX')
      Just t -> lift $ do
        tauXGen <- generalize tauX (cX ++ [Constraint tauX t])
        return (tauXGen, cX ++ [Constraint tauX t])
      Nothing -> lift $ do
        tauXGen <- generalize tauX cX
        return (tauXGen, cX)
    let ctx' = ctx ++ [tauXGen]
    (tauIn, cIn) <- getConstraints e_in ctx'
    return (tauIn, cIn ++ cX')

generalize :: Type -> [Constraint] -> Either String Type
generalize tau constraints = do
  (uf, mp) <- unification constraints
  let tauX = getType tau uf mp
  if not (null (getFreeVars tauX))
    then Left "Cannot generalize: free variables remain"
    else return tauX

unification :: [Constraint] -> Either String (UnionFind Variable, Map Variable Type)
unification constraints = do
  let allVars = nub $ concatMap (\c -> getAllVars (typeL c) ++ getAllVars (typeR c)) constraints
  let uf = mkUnionFind allVars
  let mp = Map.empty
  unification' uf mp constraints

unification' ::
  UnionFind Variable ->
  Map Variable Type ->
  [Constraint] ->
  Either String (UnionFind Variable, Map Variable Type)
unification' uf mp [] = return (uf, mp)
unification' uf mp (c : cs) = case (typeL c, typeR c) of
  (TNum, TNum) -> unification' uf mp cs
  (TBool, TBool) -> unification' uf mp cs
  (TUnit, TUnit) -> unification' uf mp cs
  (TVar l, TVar r) -> do
    let lRootBefore = case find uf l of Right x -> x; Left _ -> l
    let rRootBefore = case find uf r of Right x -> x; Left _ -> r
    let lVal = Map.lookup lRootBefore mp
    let rVal = Map.lookup rRootBefore mp
    (uf', root) <- union uf l r
    case (lVal, rVal) of
      (Nothing, Nothing) -> unification' uf' mp cs
      (Just lv, Nothing) -> do
        let mp' = Map.insert root lv mp
        unification' uf' mp' cs
      (Nothing, Just rv) -> do
        let mp' = Map.insert root rv mp
        unification' uf' mp' cs
      (Just lv, Just rv) ->
        let newC = Constraint lv rv
         in unification' uf' mp (newC : cs)
  (TVar v, t) -> do
    let vRoot = case find uf v of Right x -> x; Left _ -> v
    if not (containsVar v t)
      then case Map.lookup vRoot mp of
        Nothing -> do
          let mp' = Map.insert vRoot t mp
          unification' uf mp' cs
        Just oldT -> do
          let newC = Constraint oldT t
          unification' uf mp (newC : cs)
      else Left $ "Unification failed: " ++ show (typeL c) ++ " and " ++ show (typeR c)
  (t, TVar v) -> unification' uf mp (Constraint (typeR c) (typeL c) : cs)
  (TFn a1 r1, TFn a2 r2) ->
    let newCs = [Constraint a1 a2, Constraint r1 r2]
     in unification' uf mp (newCs ++ cs)
  (TProduct l1 r1, TProduct l2 r2) ->
    let newCs = [Constraint l1 l2, Constraint r1 r2]
     in unification' uf mp (newCs ++ cs)
  (TSum l1 r1, TSum l2 r2) ->
    let newCs = [Constraint l1 l2, Constraint r1 r2]
     in unification' uf mp (newCs ++ cs)
  (TMu _ body, TMu _ body') ->
    if body == body'
      then unification' uf mp cs
      else
        Left $ "Unification failed: " ++ show (typeL c) ++ " = " ++ show (typeR c)
  (TMu _ body, t) ->
    unification' uf mp (Constraint t (substituteVar (VDeBruijn 0) (typeL c) body) : cs)
  (t, TMu _ body) ->
    unification' uf mp (Constraint t (substituteVar (VDeBruijn 0) (typeR c) body) : cs)
  _ -> Left $ "Unification failed: " ++ show (typeL c) ++ " = " ++ show (typeR c)

getType :: Type -> UnionFind Variable -> Map Variable Type -> Type
getType tau uf mp =
  let fvs = getFreeVars tau
   in if null fvs
        then substituteVars tau
        else
          let x = head fvs
           in case find uf x of
                Left _ -> getType (addOneQuantifier tau x) uf mp
                Right r ->
                  if r /= x
                    then getType (substituteVar x (TVar r) tau) uf mp
                    else case Map.lookup r mp of
                      Just t -> getType (substituteVar x t tau) uf mp
                      Nothing -> getType (addOneQuantifier tau x) uf mp
  where
    substituteVars t = case t of
      TVar v -> maybe t substituteVars (Map.lookup v mp)
      TFn a r -> TFn (substituteVars a) (substituteVars r)
      TProduct l r -> TProduct (substituteVars l) (substituteVars r)
      TSum l r -> TSum (substituteVars l) (substituteVars r)
      TForall a tau' -> TForall a (substituteVars tau')
      TMu a body -> TMu a (substituteVars body)
      _ -> t

containsVar :: Variable -> Type -> Bool
containsVar v = go
  where
    go TNum = False
    go TBool = False
    go TUnit = False
    go (TVar v') = v == v'
    go (TFn a r) = go a || go r
    go (TProduct l r) = go l || go r
    go (TSum l r) = go l || go r
    go (TForall a tau') = a /= v && go tau'
    go (TMu a body) = a /= v && go body

substituteVar :: Variable -> Type -> Type -> Type
substituteVar v t = substituteMapVar (Map.singleton v t)

substituteMapVar :: Map Variable Type -> Type -> Type
substituteMapVar mp t = case t of
  TVar v -> fromMaybe t (Map.lookup v mp)
  TFn a r -> TFn (substituteMapVar mp a) (substituteMapVar mp r)
  TProduct l r -> TProduct (substituteMapVar mp l) (substituteMapVar mp r)
  TSum l r -> TSum (substituteMapVar mp l) (substituteMapVar mp r)
  TForall a tau' ->
    if a `Map.member` mp
      then substituteMapVar mp tau'
      else TForall a (substituteMapVar mp tau')
  TMu a body ->
    if a `Map.member` mp
      then substituteMapVar mp body
      else TMu a (substituteMapVar mp body)
  _ -> t