# AGENTS.md

## Build & Run

```sh
cabal build          # compiles all Haskell sources
cabal run interpreter -- eval simplified code.lam  # run interpreter
cabal run interpreter -- parse simplified  # read from stdin
```

## Tests

```sh
cabal test           # run all tests (207 test cases)
cabal test --enable-coverage  # run tests with HPC coverage
# View coverage report (open hpc_index.html in browser or run below):
hpc report dist-newstyle/build/x86_64-linux/ghc-9.6.7/interpreter-0.1.0/t/tests/hpc/vanilla/tix/tests.tix \
  --hpcdir=dist-newstyle/build/x86_64-linux/ghc-9.6.7/interpreter-0.1.0/build/extra-compilation-artifacts/hpc/vanilla/mix \
  --hpcdir=dist-newstyle/build/x86_64-linux/ghc-9.6.7/interpreter-0.1.0/t/tests/build/tests/tests-tmp/extra-compilation-artifacts/hpc/vanilla/mix \
  --reset-hpcdirs
# Per-module breakdown:
hpc report dist-newstyle/build/x86_64-linux/ghc-9.6.7/interpreter-0.1.0/t/tests/hpc/vanilla/tix/tests.tix \
  --hpcdir=dist-newstyle/build/x86_64-linux/ghc-9.6.7/interpreter-0.1.0/build/extra-compilation-artifacts/hpc/vanilla/mix \
  --hpcdir=dist-newstyle/build/x86_64-linux/ghc-9.6.7/interpreter-0.1.0/t/tests/build/tests/tests-tmp/extra-compilation-artifacts/hpc/vanilla/mix \
  --reset-hpcdirs --per-module
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

## Formal Proof (Lean 4)

Progress and preservation theorems mechanized in `proof/Proof/Basic.lean`:
```sh
source ~/.elan/env && cd proof && lake build
```

## Notes

- Uses Haskell (GHC 9.6.7), cabal build system
- Lean 4 toolchain at `~/.elan`
