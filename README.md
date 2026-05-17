# Interpreter

An interpreter for Lam, a simplified version of the language introduced in [Stanford CS 242: Programming Languages, Fall 2019](https://stanford-cs242.github.io/f19/assignments/assign4/).

Features:
- All features of Lam except recursive types and existential types
- Hindley-Milner type inference system
- Generating [graphviz](https://graphviz.org/) code of AST

For those who are learning CS242 (fall 2019 version): You can use this project as skeleton code for assignment 4. It's written in Rust so you don't need to learn a new language or using the official skeleton code that no longer compiles with newer versions of OCaml. See the [wiki](https://github.com/heanyang1/interpreter/wiki#notes-for-assignment-takers) for detailed instructions.

## Compile and Run

Compile the interpreter:
```sh
cabal build
```

The binary can be found at `dist-newstyle/.../interpreter`:
```sh
find dist-newstyle -name "interpreter" -type f
```

Alternatively, use `cabal run`:

```sh
# evaluate and print the result
cabal run interpreter -- eval simplified code.lam
# evaluate and print result as full AST
cabal run interpreter -- eval full code.lam
# parse and print the AST
cabal run interpreter -- parse full code.lam
# verbose: also print the type
cabal run interpreter -- verbose simplified code.lam
# generate graphviz output
cabal run interpreter -- parse graphviz code.lam | dot -Tsvg > output.svg
# read from stdin
cat code.lam | cabal run interpreter -- eval simplified
```

## Example programs

The examples are Python scripts that generate `.lam` source files. The interpreter can read from stdin:

```sh
python examples/queue.py | cabal run interpreter -- eval simplified
```

## Tests

```sh
cabal test    # runs all 96 test cases
```

## License

GPLv3
