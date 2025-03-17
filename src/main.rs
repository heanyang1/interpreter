mod ast;
mod dotgen;
mod flags;
mod evaluate;
mod monad;
mod parser;
mod typecheck;
mod ast_util;

use dotgen::to_dot;
use flags::Verbosity;
use evaluate::eval;
use monad::bind;
use parser::parse;
use std::{env::args, fmt, fs::read_to_string, io, process::exit};
use typecheck::type_check;

#[derive(Debug)]
enum Error {
    InvalidArgs,
    Parse(String),
    TypeCheck(String),
    Eval(String),
    Io(io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidArgs => write!(f, "Usage: interpreter <input> [-a | -v | -vv]"),
            Self::Parse(s) => write!(f, "Parse error: {s}"),
            Self::TypeCheck(s) => write!(f, "Type error: {s}"),
            Self::Eval(s) => write!(f, "Value error: {s}"),
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
            Mode::Ast => Ok(println!("{}", to_dot(&ast))),
            Mode::Interp(verbose) => do_!(
                // type check
                type_check(&ast).map_err(Error::TypeCheck) => t,
                {
                    if verbose != Verbosity::Normal {
                        println!("Type: {t:?}")
                    };
                    Ok(())
                },
                // evaluate
                eval(&ast, verbose).map_err(Error::Eval) => expr,
                Ok(println!("{expr:?}"))
            ),
        }
    ) {
        eprintln!("{err}");
        exit(-1);
    }
}
