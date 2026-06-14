module DotGen where

import AST
import ASTUtil (Symbol(..))

data NodeIndex = NodeIndex
    { name :: Maybe String
    , idx :: Int
    }

newNodeIndex :: Maybe String -> Int -> NodeIndex
newNodeIndex n i = NodeIndex {name = n, idx = i}

data Writer a = Writer
    { value :: a
    , output :: String
    }

instance Functor Writer where
    fmap f (Writer v o) = Writer (f v) o

instance Applicative Writer where
    pure a = Writer a ""
    Writer f o1 <*> Writer v o2 = Writer (f v) (o1 ++ o2)

instance Monad Writer where
    return = pure
    (Writer v o1) >>= f = let Writer v' o2 = f v in Writer v' (o1 ++ o2)

tell :: String -> Writer ()
tell = Writer ()

newNode :: Show a => a -> NodeIndex -> Int -> String -> Writer (NodeIndex, Int)
newNode v parent nextIdx color = do
    let cur = newNodeIndex (name parent) nextIdx
    tell $ "\t" ++ show (idx cur) ++ " [shape=point, width=0.1, color=\"" ++ color ++ "\"];\n" ++
           "\t" ++ show (idx parent) ++ " -> " ++ show (idx cur) ++
           " [label=" ++ show v ++ ", arrowhead=none, color=\"" ++
           color ++ "\", fontcolor=\"" ++ color ++ "\"];\n"
    return (cur, nextIdx + 1)

class ToGraph a where
    toGraph :: a -> NodeIndex -> Int -> Writer Int

instance ToGraph Variable where
    toGraph v parent counter = do
        (_, next) <- newNode (show v) parent counter "black"
        return next

instance ToGraph Expr where
    toGraph e parent counter = case e of
        EVar _ -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        EDeBruijn _ -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        ENum _ -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        ETrue -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        EFalse -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        EUnit -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next

        EAddop op left right -> do
            (cur, next1) <- newNode (show op) parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        EMulop op left right -> do
            (cur, next1) <- newNode (show op) parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        EIf cond then_ else_ -> do
            (cur, next1) <- newNode "if" parent counter "red"
            next2 <- toGraph cond cur next1
            next3 <- toGraph then_ cur next2
            toGraph else_ cur next3

        ERelop op left right -> do
            (cur, next1) <- newNode (show op) parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        EAnd left right -> do
            (cur, next1) <- newNode "&&" parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        EOr left right -> do
            (cur, next1) <- newNode "||" parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        EPair left right -> do
            (cur, next1) <- newNode "pair" parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        EApp lam arg -> do
            (cur, next1) <- newNode "app" parent counter "red"
            next2 <- toGraph lam cur next1
            toGraph arg cur next2

        ELam x _ e -> do
            (cur, next1) <- newNode "λ" parent counter "red"
            next2 <- toGraph x cur next1
            toGraph e cur next2

        EFix x e -> do
            (cur, next1) <- newNode "fix" parent counter "red"
            next2 <- toGraph x cur next1
            toGraph e cur next2

        EProject e d -> do
            (cur, next1) <- newNode (case d of L -> "P_left"; R -> "P_right") parent counter "red"
            toGraph e cur next1

        EInject e d -> do
            (cur, next1) <- newNode (case d of L -> "I_left"; R -> "I_right") parent counter "red"
            toGraph e cur next1

        ECase e xleft eleft xright eright -> do
            (cur, next1) <- newNode "case" parent counter "red"
            next2 <- toGraph e cur next1
            next3 <- toGraph xleft cur next2
            next4 <- toGraph eleft cur next3
            next5 <- toGraph xright cur next4
            toGraph eright cur next5

        ELet x _ e_x e_in -> do
            (cur, next1) <- newNode "let" parent counter "red"
            next2 <- toGraph x cur next1
            next3 <- toGraph e_x cur next2
            toGraph e_in cur next3

instance ToGraph Type where
    toGraph t parent counter = case t of
        TNum -> do
            (_, next) <- newNode (show t) parent counter "blue"
            return next
        TBool -> do
            (_, next) <- newNode (show t) parent counter "blue"
            return next
        TUnit -> do
            (_, next) <- newNode (show t) parent counter "blue"
            return next
        TVar _ -> do
            (_, next) <- newNode (show t) parent counter "blue"
            return next

        TProduct left right -> do
            (cur, next1) <- newNode "*" parent counter "blue"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        TSum left right -> do
            (cur, next1) <- newNode "+" parent counter "blue"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        TFn arg ret -> do
            (cur, next1) <- newNode "→" parent counter "blue"
            next2 <- toGraph arg cur next1
            toGraph ret cur next2

        TForall a tau -> do
            (cur, next1) <- newNode "∀" parent counter "blue"
            next2 <- toGraph a cur next1
            toGraph tau cur next2

toDot :: Expr -> Maybe String -> String
toDot ast name = case name of
    Just n ->
        let root = newNodeIndex (Just n) 0
            result = toGraph (toDebruijn ast) root 1
        in "subgraph " ++ n ++ " {\n\t" ++ show (idx root) ++
           " [shape=point, width=0.1];\n" ++ output result ++ "}"
    Nothing ->
        let root = newNodeIndex Nothing 0
            result = toGraph (toDebruijn ast) root 1
        in "digraph {\n\t" ++ show (idx root) ++
           " [shape=point, width=0.1];\n" ++ output result ++ "}"
