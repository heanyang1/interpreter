# Interpreter

Rust implementation of [Stanford CS242 assignment 4 (fall 2019)](https://stanford-cs242.github.io/f19/assignments/assign4/)

## Compile and Run

Compile the interpreter:
```sh
cargo build
```

The binary can be found at `project_dir/target/debug/interpreter`.

Alternatively, you can run `cargo run -- args` to run the interpreter with arguments `args`.

Usage:
```
interpreter <input> [-ab | -ae | -v | -vv | -va]

-ab: print graphviz code of the AST before evaluation
-ae: print graphviz code of the AST after evaluation
-v: print evaluation result
-vv: print evaluation process
-va: print evaluation process as graphviz code of AST

Output will be printed to stdout

Read input from stdin if <input> is -
```

You can use `dot` to generate a nice picture of AST (if [Graphviz](https://graphviz.org/) is installed):
```sh
cargo run -- path/to/your/code.lam -a | dot -Tsvg > output.svg
```

## Examples

The examples are Python scripts that generates `.lam` source file. You can use the interpreter's `-` flag (which means reading from standard input instead of a file) to see the result without generating a `.lam` file. For example:
```sh
python examples/linkedlst.py | cargo run -- - -v
```
