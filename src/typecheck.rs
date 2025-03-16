use std::collections::HashMap;

use crate::{ast::*, do_, monad::bind};

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    let ctx = HashMap::new();
    type_check_expr(ast, &ctx)
}

fn type_check_expr(ast: &Expr, ctx: &HashMap<Type, String>) -> Result<Type, String> {
    match ast {
        // 1. arithmetic
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
        // 2. conditionals
        Expr::True | Expr::False => Ok(Type::Bool),
        Expr::Relop { relop, left, right } => do_!(
            type_check_expr(left, ctx) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Bool),
                _ => Err(format!("Relational operands have incompatible types: {:?} {} {:?}", tau_left, relop, tau_right)),
            }
        ),
        Expr::If { cond, then_, else_ } => do_!(
            type_check_expr(cond, ctx) => tau_cond,
            type_check_expr(then_, ctx) => tau_then,
            type_check_expr(else_, ctx) => tau_else,
            match (tau_cond.clone(), tau_then.clone(), tau_else.clone()) {
                (Type::Bool, tau_then, tau_else) if tau_then == tau_else => Ok(tau_then),
                _ => Err(format!("If branches have incompatible types: if {:?} then {:?} else {:?}", tau_cond, tau_then, tau_else)),
            }
        ),
        Expr::And { left, right } => do_!(
            type_check_expr(left, ctx) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                _ => Err(format!("And operands have incompatible types: {:?} && {:?}", tau_left, tau_right)),
            }
        ),
        Expr::Or { left, right } => do_!(
            type_check_expr(left, ctx) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                _ => Err(format!("Or operands have incompatible types: {:?} || {:?}", tau_left, tau_right)),
            }
        ),
        _ => todo!(),
    }
}
