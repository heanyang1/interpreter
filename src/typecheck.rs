use std::collections::HashMap;

use crate::{ast::*, do_, monad::bind};

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    let ctx = HashMap::new();
    type_check_expr(ast, &ctx)
}

fn type_check_expr(ast: &Expr, ctx: &HashMap<Type, String>) -> Result<Type, String> {
    match ast {
        Expr::Num(_) => Ok(Type::Num),
        Expr::Addop { binop, left, right } => do_!(
            type_check_expr(left, ctx) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Num),
                _ => Err(format!("Addition operands have incompatible types: {:?} {} {:?}", tau_left, binop, tau_right)),
            }
        ),
        Expr::Mulop { binop, left, right } => do_!(
            type_check_expr(left, ctx) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Num),
                _ => Err(format!("Multiplication operands have incompatible types: {:?} {} {:?}", tau_left, binop, tau_right)),
            }
        ),
        _ => todo!(),
    }
}
