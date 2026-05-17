# AGENTS.md

## Build & Run

```sh
cabal build          # compiles all Haskell sources
cabal run interpreter -- eval simplified code.lam  # run interpreter
cabal run interpreter -- parse simplified  # read from stdin
```

## Tests

```sh
cabal test           # run all tests (96 test cases)
```

## CLI

```
Usage: interpreter <mode> <output> [input_path]
  mode:   parse | eval | verbose | very-verbose
  output: full | simplified | debruijn | graphviz
```

Reads from stdin if no input_path given.

## Examples

Python scripts in `examples/` generate `.lam` source. Run via pipe:
```sh
python examples/queue.py | cabal run interpreter -- eval simplified
```

## Notes

- Uses Haskell (GHC 9.6.7), cabal build system
- Output formats match Rust original: `full`, `simplified`, `debruijn`, `graphviz`
