mod ast;
mod ast_util;
mod dotgen;
mod evaluate;
mod flags;
mod monad;
mod parser;
mod typecheck;

use clap::Parser;
use evaluate::eval;
use flags::{format_ast, format_type, Mode, OutputMode};
use monad::Monad;
use parser::parse;
use std::{
    fmt,
    fs::read_to_string,
    io::{self, Read},
    process::exit,
};
use typecheck::type_check;

#[derive(Debug)]
enum Error {
    Parse(String),
    TypeCheck(String),
    Io(io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Parse(s) => write!(f, "Parse error: {s}"),
            Self::TypeCheck(s) => write!(f, "Type error: {s}"),
            Self::Io(err) => write!(f, "I/O error: {err}"),
        }
    }
}

fn read_from_stdin() -> Result<String, std::io::Error> {
    let mut buf = String::new();
    io::stdin().read_to_string(&mut buf)?;
    Ok(buf)
}

#[derive(Parser)]
struct Cli {
    /// Program mode
    #[arg(value_enum)]
    mode: Mode,

    /// Output format
    #[arg(value_enum)]
    output: OutputMode,

    /// Input file. Read input from stdin if not specified.
    input_path: Option<String>,
}

fn main() {
    let cli = Cli::parse();
    if let Err(err) = do_!(
        // read program
        match cli.input_path {
            None => read_from_stdin().map_err(Error::Io),
            Some(path) => read_to_string(path).map_err(Error::Io),
        } => input,
        // parse program
        parse(&input).map_err(Error::Parse) => ast,
        match cli.mode {
            Mode::Parse => Ok(println!("{}", format_ast(&ast, cli.output, None))),
            _ => do_!(
                // type check
                type_check(&ast).map_err(Error::TypeCheck) => t,
                // print type
                match cli.mode {
                    Mode::Verbose | Mode::VeryVerbose => Ok(println!("{}", format_type(&t, cli.output))),
                    _ => Ok(()),
                },
                match cli.output {
                    OutputMode::Graphviz => Ok(println!("digraph Program {{")),
                    _ => Ok(()),
                },
                // evaluate
                Ok(eval(&ast, cli.mode, cli.output)) => result,
                // print result
                Ok(println!("{}", format_ast(&result, cli.output, Some(String::from("last"))))),
                match cli.output {
                    OutputMode::Graphviz => Ok(println!("}}")),
                    _ => Ok(()),
                }
            )
        }
    ) {
        eprintln!("{err}");
        exit(-1);
    }
}
