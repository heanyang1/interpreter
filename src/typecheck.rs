use std::collections::HashMap;

use crate::{ast::*, do_, monad::bind};

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    type_check_expr(ast, HashMap::new())
}

fn type_check_expr(ast: &Expr, ctx: HashMap<String, Type>) -> Result<Type, String> {
    match ast {
        // 1. arithmetic
        Expr::Num(_) => Ok(Type::Num),
        Expr::Addop { binop, left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Num),
                _ => Err(format!("Addition operands have incompatible types: {:?} {} {:?}", tau_left, binop, tau_right)),
            }
        ),
        Expr::Mulop { binop, left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Num),
                _ => Err(format!("Multiplication operands have incompatible types: {:?} {} {:?}", tau_left, binop, tau_right)),
            }
        ),
        // 2. conditionals
        Expr::True | Expr::False => Ok(Type::Bool),
        Expr::Relop { relop, left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Bool),
                _ => Err(format!("Relational operands have incompatible types: {:?} {} {:?}", tau_left, relop, tau_right)),
            }
        ),
        Expr::If { cond, then_, else_ } => do_!(
            type_check_expr(cond, ctx.clone()) => tau_cond,
            type_check_expr(then_, ctx.clone()) => tau_then,
            type_check_expr(else_, ctx) => tau_else,
            match (tau_cond.clone(), tau_then.clone(), tau_else.clone()) {
                (Type::Bool, tau_then, tau_else) if tau_then == tau_else => Ok(tau_then),
                _ => Err(format!("If branches have incompatible types: if {:?} then {:?} else {:?}", tau_cond, tau_then, tau_else)),
            }
        ),
        Expr::And { left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                _ => Err(format!("And operands have incompatible types: {:?} && {:?}", tau_left, tau_right)),
            }
        ),
        Expr::Or { left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                _ => Err(format!("Or operands have incompatible types: {:?} || {:?}", tau_left, tau_right)),
            }
        ),
        // 3. Functions
        Expr::Var(x) => match ctx.get(&x.0) {
            Some(tau) => Ok(tau.clone()),
            None => Err(format!("Free variable: {}", x.0)),
        },
        Expr::Lam { x, tau, e } => do_!(
            {
                let mut ctx = ctx;
                ctx.insert(x.0.clone(), *tau.clone());
                type_check_expr(e, ctx.clone())
            } => tau_e,
            Ok(Type::Fn { arg: tau.clone(), ret:  Box::new(tau_e) })
        ),
        Expr::App { lam, arg } => do_!(
            type_check_expr(lam, ctx.clone()) => tau_lam,
            type_check_expr(arg, ctx) => tau_arg,
            match tau_lam.clone() {
                Type::Fn { arg, ret } if tau_arg == *arg => Ok(*ret),
                _ => Err(format!("Function application has incompatible argument types: {:?} {:?}", tau_lam, tau_arg)),
            }
        ),
        _ => todo!(),
    }
}
