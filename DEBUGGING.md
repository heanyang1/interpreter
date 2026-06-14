# Debugging with GHCi

## Quick Start

```sh
cabal repl
```

This loads all library modules. Import what you need:

```haskell
:m + AST Parser Evaluate TypeCheck ASTUtil
```

## Parse an Expression

```haskell
let Right e = parse "fun x -> x + 1"
e                        -- print the AST
```

## Convert to de Bruijn indices (required before eval/typecheck)

```haskell
let d = toDebruijn e
d                        -- see the de Bruijn form
```

## Step Through Evaluation

Try an application (lambdas are already values and won't step):

```haskell
let Right e = parse "(fun x -> x + 1) 5"
let d = toDebruijn e

tryStep d                -- one step: (λx. x + 1) 5  →  5 + 1
let Step s1 = tryStep d
tryStep s1               -- next step: 5 + 1 → 6
```

Collect all intermediate steps:

```haskell
let steps e = case tryStep e of { Val -> [e]; Step e' -> e : steps e' }
steps d                  -- every expression in the reduction chain
```

And `eval` gives the final result:

```haskell
eval d                   -- final value: 6
```

## Type Check

```haskell
typeCheck d              -- Right Type  or  Left error message
```

## Inspect Intermediate Results

Build compound expressions by hand to test specific code paths:

```haskell
let e = EApp (ELam (Variable "x") (EAddop Add (EDeBruijn 0) (ENum 1))) (ENum 5)
tryStep e
```

## Breakpoints

```haskell
:break tryStep
:break deBruijnSubst
:break eval
eval d                   -- evaluate, will stop at tryStep
:step                    -- step into
:continue                -- resume
:list                    -- show current line
```

## Use `trace` for Ad-Hoc Debugging

Import `Debug.Trace` and temporarily insert traces into `tryStep`:

```haskell
import Debug.Trace

tryStep e = trace ("trying: " ++ show e) $ case e of ...
```

Then `:reload`. This works without restarting the repl session.

## Multi-line Input for Complex Programs

Use GHCi's `:{` / `:}` block syntax:

```haskell
:{
let Right prog = parse "letrec fact = fun n -> if n == 0 then 1 else n * fact (n - 1) in fact 5"
prog
:}
```

## Compose Operations into One Pipeline

Define helpers using `>>=` to combine everything on a single line:

```haskell
let parseAndCheck s = parse s >>= \e -> let d = toDebruijn e in typeCheck d >>= \t -> pure (d, t)
let Right (d, ty) = parseAndCheck "fun x -> x + 1"
d
ty
```

Combine parsing, de Bruijn, and evaluation:

```haskell
let parseAndEval s = parse s >>= \e -> let d = toDebruijn e in pure (d, eval d)
let Right (d, result) = parseAndEval "(fun x -> x + 1) 5"
d
result
```

Or a single-shot `run` that returns all three:

```haskell
let run s = parse s >>= \e -> let d = toDebruijn e in typeCheck d >>= \t -> pure (d, t, eval d)
let Right (d, ty, result) = run "(fun x -> x) 5"
d
ty
result
```

All three helpers avoid the repetitive `let`-per-step workflow and keep intermediate values accessible for inspection.

## Key Functions at a Glance

| Function | Signature | Purpose |
|---|---|---|
| `parse` | `String -> Either String Expr` | Parse source text |
| `toDebruijn` | `Expr -> Expr` | Named → de Bruijn indices |
| `tryStep` | `Expr -> Outcome` | One small-step reduction |
| `eval` | `Expr -> Expr` | Reduce to normal form |
| `typeCheck` | `Expr -> Either String Type` | Constraint-based type inference |
| `deBruijnSubst` | `Int -> Expr -> Expr -> Expr` | Capture-avoiding substitution |
| `formatAst` | `Expr -> OutputMode -> Maybe String -> String` | Pretty-print AST |
