# Interpreter

Rust implementation of [Stanford CS242 assignment 4 (fall 2019)](https://stanford-cs242.github.io/f19/assignments/assign4/)

For those who are learning CS242 (fall 2019 version): you'd better NOT see my solution. Instead, use this project as skeleton code and reference solution. I have tried my best to make the experience similar to (but less painful than) using the original OCaml skeleton code. See the [wiki](https://github.com/heanyang1/interpreter/wiki#notes-for-assignment-takers) for detailed instructions.

## Compile and Run

Compile the interpreter:
```sh
cargo build
```

The binary can be found at `project_dir/target/debug/interpreter`.

Alternatively, you can run `cargo run -- args` to run the interpreter with arguments `args`.

Some examples:
```sh
# show usage
cargo run -- --help
# evaluate code.lam and print the whole AST
cargo run -- eval full code.lam
# print the result as human-readable format (some types are ignored and unreachable nodes are pruned)
cargo run -- eval simplified code.lam
# print the evaluation steps as de Bruijn indices
cargo run -- very-verbose de-bruijn code.lam
# parse the expression and print its AST
cargo run -- parse full code.lam
# generate a nice picture of AST (requires graphviz)
cargo run -- parse graphviz code.lam | dot -Tsvg > output.svg
```

## Example programs

The examples are Python scripts that generates `.lam` source file. The interpreter can read from stdin so you can use pipe to see the result without generating a `.lam` file:
```sh
python examples/queue.py | cargo run -- eval simplified
```

Some results are very large (the largest AST has ~5k nodes) so it may take a very long time to generate picture or print step-by-step solution.

## License

GPLv3
