use dotgen::to_dot;
use lalrpop_util::lalrpop_mod;
use std::{env::args, fmt, fs::read_to_string, io, process::exit};

mod ast;
mod dotgen;

lalrpop_mod!(parser);

#[derive(Debug)]
enum Error {
    InvalidArgs,
    Parse(String),
    Io(io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidArgs => write!(f, "Usage: interpreter <input> [--ast | --interp]"),
            Self::Parse(s) => write!(f, "Parse error: {s}"),
            Self::Io(err) => write!(f, "I/O error: {err}"),
        }
    }
}

enum Mode {
    Ast,
    Interp,
}

fn parse_args() -> Result<(String, Mode), Error> {
    let mut args = args();
    args.next();
    if let (Some(input_path), Some(mode_str)) = (args.next(), args.next()) {
        let mode = match mode_str.as_str() {
            "--ast" => Mode::Ast,
            "--interp" => Mode::Interp,
            _ => return Err(Error::InvalidArgs),
        };
        Ok((input_path, mode))
    } else {
        Err(Error::InvalidArgs)
    }
}

fn main() {
    if let Err(err) = try_main() {
        eprintln!("{err}");
        exit(-1);
    }
}

fn try_main() -> Result<(), Error> {
    let (input_path, mode) = parse_args()?;
    let input = read_to_string(input_path).map_err(Error::Io)?;

    let binding = parser::ExprParser::new();
    let ast = binding
        .parse(&input)
        .map_err(|e| Error::Parse(e.to_string()))?;

    match mode {
        Mode::Ast => println!("{}", to_dot(&ast)),
        Mode::Interp => todo!(),
    }

    Ok(())
}
