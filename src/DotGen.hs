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

newNode :: Show a => a -> NodeIndex -> String -> Writer NodeIndex
newNode v parent color = do
    let cur = newNodeIndex (name parent) (idx parent + 1)
    tell $ "\t" ++ show (idx cur) ++ " [shape=point, width=0.1, color=\"" ++ color ++ "\"];\n" ++
           "\t" ++ show (idx parent) ++ " -> " ++ show (idx cur) ++
           " [label=" ++ show v ++ ", arrowhead=none, color=\"" ++
           color ++ "\", fontcolor=\"" ++ color ++ "\"];\n"
    return cur

class ToGraph a where
    toGraph :: a -> NodeIndex -> Writer ()

instance ToGraph Variable where
    toGraph v parent = do
        _ <- newNode (show v) parent "black"
        return ()

instance ToGraph Expr where
    toGraph e parent = case e of
        EVar _ -> do
            _ <- newNode (show e) parent "red"
            return ()
        EDeBruijn _ -> do
            _ <- newNode (show e) parent "red"
            return ()
        ENum _ -> do
            _ <- newNode (show e) parent "red"
            return ()
        ETrue -> do
            _ <- newNode (show e) parent "red"
            return ()
        EFalse -> do
            _ <- newNode (show e) parent "red"
            return ()
        EUnit -> do
            _ <- newNode (show e) parent "red"
            return ()

        EAddop op left right -> do
            cur <- newNode (show op) parent "red"
            toGraph left cur
            toGraph right cur

        EMulop op left right -> do
            cur <- newNode (show op) parent "red"
            toGraph left cur
            toGraph right cur

        EIf cond then_ else_ -> do
            cur <- newNode "if" parent "red"
            toGraph cond cur
            toGraph then_ cur
            toGraph else_ cur

        ERelop op left right -> do
            cur <- newNode (show op) parent "red"
            toGraph left cur
            toGraph right cur

        EAnd left right -> do
            cur <- newNode "&&" parent "red"
            toGraph left cur
            toGraph right cur

        EOr left right -> do
            cur <- newNode "||" parent "red"
            toGraph left cur
            toGraph right cur

        EPair left right -> do
            cur <- newNode "pair" parent "red"
            toGraph left cur
            toGraph right cur

        EApp lam arg -> do
            cur <- newNode "app" parent "red"
            toGraph lam cur
            toGraph arg cur

        ELam x e -> do
            cur <- newNode "λ" parent "red"
            toGraph x cur
            toGraph e cur

        EFix x e -> do
            cur <- newNode "fix" parent "red"
            toGraph x cur
            toGraph e cur

        EProject e d -> do
            cur <- newNode (case d of L -> "P_left"; R -> "P_right") parent "red"
            toGraph e cur

        EInject e d -> do
            cur <- newNode (case d of L -> "I_left"; R -> "I_right") parent "red"
            toGraph e cur

        ECase e xleft eleft xright eright -> do
            cur <- newNode "case" parent "red"
            toGraph e cur
            toGraph xleft cur
            toGraph eleft cur
            toGraph xright cur
            toGraph eright cur

        ELet x e_x e_in -> do
            cur <- newNode "let" parent "red"
            toGraph x cur
            toGraph e_x cur
            toGraph e_in cur

instance ToGraph Type where
    toGraph t parent = case t of
        TNum -> do
            _ <- newNode (show t) parent "blue"
            return ()
        TBool -> do
            _ <- newNode (show t) parent "blue"
            return ()
        TUnit -> do
            _ <- newNode (show t) parent "blue"
            return ()
        TVar _ -> do
            _ <- newNode (show t) parent "blue"
            return ()

        TProduct left right -> do
            cur <- newNode "*" parent "blue"
            toGraph left cur
            toGraph right cur

        TSum left right -> do
            cur <- newNode "+" parent "blue"
            toGraph left cur
            toGraph right cur

        TFn arg ret -> do
            cur <- newNode "→" parent "blue"
            toGraph arg cur
            toGraph ret cur

        TForall a tau -> do
            cur <- newNode "∀" parent "blue"
            toGraph a cur
            toGraph tau cur

toDot :: Expr -> Maybe String -> String
toDot ast name = case name of
    Just n ->
        let root = newNodeIndex (Just n) 0
            result = toGraph (toDebruijn ast) root
        in "subgraph " ++ n ++ " {\n\t" ++ show (idx root) ++
           " [shape=point, width=0.1];\n" ++ output result ++ "}"
    Nothing ->
        let root = newNodeIndex Nothing 0
            result = toGraph (toDebruijn ast) root
        in "digraph {\n\t" ++ show (idx root) ++
           " [shape=point, width=0.1];\n" ++ output result ++ "}"