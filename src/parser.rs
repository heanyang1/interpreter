use crate::ast::{Expr, Type};

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(grammar);

pub fn parse(input: &str) -> Result<Box<Expr>, String> {
    grammar::ExprParser::new()
        .parse(input)
        .map_err(|e| e.to_string())
}

#[allow(unused)]
pub fn parse_type(input: &str) -> Result<Box<Type>, String> {
    grammar::TypeParser::new()
        .parse(input)
        .map_err(|e| e.to_string())
}
