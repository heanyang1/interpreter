{-# OPTIONS_GHC -w #-}
module Parser (parse) where

import Prelude hiding (parse)
import AST
import Text.Parsec hiding (parse)
import qualified Text.Parsec as P
import Text.Parsec.String
import Control.Monad (when)

type P = Parsec String ()

keywords :: [String]
keywords = ["let", "letrec", "fun", "fix", "if", "then", "else",
            "case", "inj", "true", "false", "in"]

kw :: String -> P ()
kw s = try $ do
    string s
    notFollowedBy alphaNum
    spaces

op :: String -> P ()
op s = try $ do
    string s
    spaces

var :: P Variable
var = try $ do
    c <- letter
    rest <- many (alphaNum <|> char '_')
    let name = c : rest
    when (name `elem` keywords) $ fail "keyword"
    spaces
    return (Variable name)

dir :: P Direction
dir = (kw "L" >> return L) <|> (kw "R" >> return R)

parseType :: P Type
parseType = parseForall
  where
    parseForall :: P Type
    parseForall =
        try (do
            char '\x2200'
            spaces
            v <- var
            op "."
            t <- parseForall
            return (TForall v t))
        <|> parseArrow
    parseArrow :: P Type
    parseArrow = do
        t1 <- parseSum
        rest <- (try (op "->" >> fmap Just parseArrow)) <|> return Nothing
        case rest of
            Nothing -> return t1
            Just t2 -> return (TFn t1 t2)
    parseSum :: P Type
    parseSum = do
        t1 <- parseProduct
        rest <- many (try (op "+" *> parseProduct))
        return $ foldl1 (\acc r -> TSum acc r) (t1 : rest)
    parseProduct :: P Type
    parseProduct = do
        t1 <- parseAtom
        rest <- many (try (op "*" *> parseAtom))
        return $ foldl1 (\acc r -> TProduct acc r) (t1 : rest)
    parseAtom :: P Type
    parseAtom =
            (kw "num" >> return TNum)
        <|> (kw "bool" >> return TBool)
        <|> (try (op "(" >> op ")" >> return TUnit))
        <|> (try (op "(" >> parseType >>= \t -> op ")" >> return t))
        <|> (TVar <$> var)

parse :: String -> Either String Expr
parse input = case P.parse (spaces *> expr <* eof) "" input of
    Left err -> Left (show err)
    Right e -> Right e

expr :: P Expr
expr = spaces *> letrecExpr

letrecExpr :: P Expr
letrecExpr =
    try (do
        kw "letrec"
        x <- var
        op "="
        e1 <- letrecExpr
        kw "in"
        e2 <- letrecExpr
        return (EApp (ELam x Nothing e2) (EFix x e1)))
    <|> letExpr

letExpr :: P Expr
letExpr =
    try (do
        kw "let"
        (x, mt) <- try (do { v <- var; op ":"; t <- parseType; return (v, Just t) })
               <|> (fmap (\v -> (v, Nothing)) var)
        op "="
        e1 <- letExpr
        kw "in"
        ELet x mt e1 <$> letExpr)
    <|> funExpr

funExpr :: P Expr
funExpr =
    try (do
        kw "fun"
        (x, mt) <- try (do { op "("; v <- var; op ":"; t <- parseType; op ")"; return (v, Just t) })
               <|> (fmap (\v -> (v, Nothing)) var)
        op "->"
        ELam x mt <$> funExpr)
    <|> fixExpr

fixExpr :: P Expr
fixExpr =
    try (do
        kw "fix"
        x <- var
        op "->"
        EFix x <$> fixExpr)
    <|> appExpr

appExpr :: P Expr
appExpr = do
    e <- ifExpr
    appRest e
  where
    appRest e =
        try (do { e2 <- ifExpr; appRest (EApp e e2) })
        <|> return e

ifExpr :: P Expr
ifExpr =
    try (do
        kw "if"
        c <- caseExpr
        kw "then"
        t <- caseExpr
        kw "else"
        EIf c t <$> caseExpr)
    <|> caseExpr

caseExpr :: P Expr
caseExpr =
    try (do
        kw "case"
        e <- caseExpr
        op "{"
        kw "L"
        char '('
        xl <- var
        char ')'
        spaces
        op "->"
        el <- caseExpr
        op "|"
        kw "R"
        char '('
        xr <- var
        char ')'
        spaces
        op "->"
        er <- caseExpr
        op "}"
        return (ECase e xl el xr er))
    <|> injectExpr

injectExpr :: P Expr
injectExpr =
    try (do
        kw "inj"
        e <- projectExpr
        op "="
        EInject e <$> dir)
    <|> projectExpr

projectExpr :: P Expr
projectExpr = do
    e <- orExpr
    projectRest e
  where
    projectRest e =
        try (do { char '.'; d <- dir; projectRest (EProject e d) })
        <|> return e

orExpr :: P Expr
orExpr = do
    e <- andExpr
    orRest e
  where
    orRest e =
        try (do { op "||"; right <- andExpr; orRest (EOr e right) })
        <|> return e

andExpr :: P Expr
andExpr = do
    e <- relExpr
    andRest e
  where
    andRest e =
        try (do { op "&&"; right <- relExpr; andRest (EAnd e right) })
        <|> return e

relExpr :: P Expr
relExpr = do
    e <- addExpr
    relRest e
  where
    relRest e =
        try (do
            relop <- (op "==" >> return Eq)
                  <|> (op "<" >> return Lt)
                  <|> (op ">" >> return Gt)
            right <- addExpr
            relRest (ERelop relop e right))
        <|> return e

addExpr :: P Expr
addExpr = do
    e <- mulExpr
    addRest e
  where
    addRest e =
        try (do
            addop <- (op "+" >> return Add) <|> (op "-" >> return Sub)
            right <- mulExpr
            addRest (EAddop addop e right))
        <|> return e

mulExpr :: P Expr
mulExpr = do
    e <- primaryExpr
    mulRest e
  where
    mulRest e =
        try (do
            mulop <- (op "*" >> return Mul) <|> (op "/" >> return Div)
            right <- primaryExpr
            mulRest (EMulop mulop e right))
        <|> return e

primaryExpr :: P Expr
primaryExpr =
    try pairExpr
    <|> try parenExpr
    <|> try (kw "true" >> return ETrue)
    <|> try (kw "false" >> return EFalse)
    <|> try unitExpr
    <|> try numExpr
    <|> try varExpr
  where
    pairExpr = do
        char '('
        e1 <- expr
        char ','
        e2 <- expr
        char ')'
        spaces
        return (EPair e1 e2)
    parenExpr = do
        char '('
        e <- expr
        char ')'
        spaces
        return e
    unitExpr = do
        char '('
        char ')'
        spaces
        return EUnit
    numExpr = do
        n <- many1 digit
        spaces
        return (ENum (read n))
    varExpr = do EVar <$> var