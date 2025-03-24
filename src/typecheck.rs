use std::collections::HashMap;

use crate::{ast::*, do_, monad::Monad};

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    type_check_expr(ast, HashMap::new())
}

macro_rules! type_mismatch {
    ($left:expr, $right:expr, $name:expr) => {
        Err(format!(
            r#"
Type mismatch in {}:
    {:?}
and
    {:?}"#,
            $name, $left, $right
        ))
    };
}

fn type_check_expr(ast: &Expr, ctx: HashMap<Variable, Type>) -> Result<Type, String> {
    match ast {
        // 1. arithmetic
        Expr::Num(_) => Ok(Type::Num),
        Expr::Addop { binop, left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Num),
                _ => type_mismatch!(tau_left, tau_right, binop),
            }
        ),
        Expr::Mulop { binop, left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Num),
                _ => type_mismatch!(tau_left, tau_right, binop),
            }
        ),
        _ => todo!()
    }
}
