# Interpreter

Rust implementation of [Stanford CS242 assignment 4 (fall 2019)](https://stanford-cs242.github.io/f19/assignments/assign4/)

## Compile and Run

Run the interpreter:
```sh
cargo run -- path/to/your/code.lam [-v | -vv]
```
where the meaning of `-v` and `-vv` is the same as the original assignment's code.

Parse your code and generate a nice picture of AST (if [Graphviz](https://graphviz.org/) is installed):
```sh
cargo run -- path/to/your/code.lam -a | dot -Tsvg > output.svg
```

## Examples

The examples are Python scripts that generates lambda calculus source file. You can use the interpreter's `-` flag (which means reading from standard input instead of a file) to see the result without generating a `.lam` file. For example:
```sh
python examples/linkedlst.py | cargo run -- - -v
```
