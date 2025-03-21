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
use monad::Monad;
use parser::parse;
use std::{
    env::args,
    fmt,
    fs::read_to_string,
    io::{self, Read},
    process::exit,
};
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
Usage: interpreter <input> [-ab | -ae | -v | -vv | -va]

-ab: print graphviz code of the AST before evaluation
-ae: print graphviz code of the AST after evaluation
-v: print evaluation result
-vv: print evaluation process
-va: print evaluation process as graphviz code of AST

Output will be printed to stdout

Read input from stdin if <input> is -
"#
            ),
            Self::Parse(s) => write!(f, "Parse error: {s}"),
            Self::TypeCheck(s) => write!(f, "Type error: {s}"),
            Self::Io(err) => write!(f, "I/O error: {err}"),
        }
    }
}

enum Mode {
    Ast(AstMode),
    Interp(Verbosity),
}

enum AstMode {
    Before,
    After,
}

enum InputMode {
    Stdin,
    File(String),
}

fn parse_args() -> Result<(InputMode, Mode), Error> {
    let mut args = args();
    args.next();

    if let Some(input_path) = args.next() {
        let input = if input_path == "-" {
            InputMode::Stdin
        } else {
            InputMode::File(input_path)
        };
        let mode = match args.next() {
            Some(mode_str) => match mode_str.as_str() {
                "-ab" => Mode::Ast(AstMode::Before),
                "-ae" => Mode::Ast(AstMode::After),
                "-v" => Mode::Interp(Verbosity::Verbose),
                "-vv" => Mode::Interp(Verbosity::VeryVerbose),
                "-va" => Mode::Interp(Verbosity::VerboseAST),
                _ => return Err(Error::InvalidArgs),
            },
            None => Mode::Interp(Verbosity::Normal),
        };
        Ok((input, mode))
    } else {
        Err(Error::InvalidArgs)
    }
}

fn read_from_stdin() -> Result<String, std::io::Error> {
    let mut buf = String::new();
    io::stdin().read_to_string(&mut buf)?;
    Ok(buf)
}

fn main() {
    if let Err(err) = do_!(
        parse_args() => (input_path, mode),
        // read program
        match input_path {
            InputMode::Stdin => read_from_stdin().map_err(Error::Io),
            InputMode::File(path) => read_to_string(path).map_err(Error::Io),
        } => input,
        // parse program
        parse(&input).map_err(Error::Parse) => ast,
        match mode {
            Mode::Ast(AstMode::Before) => Ok(println!("{}", to_dot(&ast, None))),
            Mode::Ast(AstMode::After) => do_!(
                type_check(&ast).map_err(Error::TypeCheck),
                Ok(eval(&ast, Verbosity::Normal)) => result,
                Ok(println!("{}", to_dot(&result, None)))
            ),
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
                    Ok(println!("{} }}", to_dot(&result, Some(String::from("last")))))
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
