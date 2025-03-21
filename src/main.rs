mod ast;
mod ast_util;
mod dotgen;
mod evaluate;
mod flags;
mod monad;
mod parser;
mod typecheck;

use dotgen::to_dot;
use evaluate::eval;
use flags::Verbosity;
use monad::bind;
use parser::parse;
use std::{env::args, fmt, fs::read_to_string, io, process::exit};
use typecheck::type_check;

#[derive(Debug)]
enum Error {
    InvalidArgs,
    Parse(String),
    TypeCheck(String),
    Io(io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidArgs => write!(
                f,
                r#"
                Usage: interpreter <input> [-a | -v | -vv | -va]
                
                -a: print graphviz code of AST only
                -v: print evaluation result
                -vv: print evaluation process
                -va: print evaluation process as graphviz code of AST

                Output will be printed to stdout
                "#
            ),
            Self::Parse(s) => write!(f, "Parse error: {s}"),
            Self::TypeCheck(s) => write!(f, "Type error: {s}"),
            Self::Io(err) => write!(f, "I/O error: {err}"),
        }
    }
}

enum Mode {
    Ast,
    Interp(Verbosity),
}

fn parse_args() -> Result<(String, Mode), Error> {
    let mut args = args();
    args.next();

    if let Some(input_path) = args.next() {
        let mode = match args.next() {
            Some(mode_str) => match mode_str.as_str() {
                "-a" => Mode::Ast,
                "-v" => Mode::Interp(Verbosity::Verbose),
                "-vv" => Mode::Interp(Verbosity::VeryVerbose),
                "-va" => Mode::Interp(Verbosity::VerboseAST),
                _ => return Err(Error::InvalidArgs),
            },
            None => Mode::Interp(Verbosity::Normal),
        };
        Ok((input_path, mode))
    } else {
        Err(Error::InvalidArgs)
    }
}

fn main() {
    if let Err(err) = do_!(
        parse_args() => (input_path, mode),
        // read program from file
        read_to_string(input_path).map_err(Error::Io) => input,
        // parse program
        parse(&input).map_err(Error::Parse) => ast,
        match mode {
            Mode::Ast => Ok(println!("{}", to_dot(&ast, None))),
            Mode::Interp(verbose) => do_!(
                // type check
                type_check(&ast).map_err(Error::TypeCheck) => t,
                match verbose {
                    Verbosity::Normal => Ok(()),
                    Verbosity::Verbose | Verbosity::VeryVerbose => Ok(println!("Type: {t:?}")),
                    Verbosity::VerboseAST => Ok(println!("digraph Program {{")),
                },
                // evaluate
                Ok(eval(&ast, verbose)) => result,
                if verbose == Verbosity::VerboseAST {
                    Ok(println!("}}"))
                } else {
                    Ok(println!("{:?}", result))
                }
            ),
        }
    ) {
        eprintln!("{err}");
        exit(-1);
    }
}
