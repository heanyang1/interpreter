use clap::ValueEnum;

use crate::{ast::{Expr, Type}, ast_util::Symbol, dotgen::to_dot};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Mode {
    /// Parse and print the input expression
    Parse,

    /// Evaluate and print the result
    Eval,

    /// Print the type as well as evaluation result
    Verbose,

    /// Print step-by-step evaluation process
    VeryVerbose,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum OutputMode {
    /// Full expression
    Full,

    /// Simplified human-readable expression
    Simplified,

    /// Full expression with de Bruijn indices
    DeBruijn,

    /// Graphviz code
    Graphviz,
}

pub fn format_ast(ast: &Expr, output_mode: OutputMode, name: Option<String>) -> String {
    match output_mode {
        OutputMode::Full => format!("{:?}", ast),
        OutputMode::Simplified => format!("{}", ast),
        OutputMode::DeBruijn => format!("{:?}", ast.clone().to_debruijn()),
        OutputMode::Graphviz => to_dot(ast, name),
    }
}

pub fn format_type(ty: &Type, output_mode: OutputMode) -> String {
    match output_mode {
        OutputMode::Full => format!("{:?}", ty),
        OutputMode::Simplified => format!("{}", ty),
        OutputMode::DeBruijn => format!("{:?}", ty.clone().to_debruijn()),
        OutputMode::Graphviz => String::new(),
    }
}