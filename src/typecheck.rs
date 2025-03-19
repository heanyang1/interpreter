use std::collections::HashMap;

use crate::{ast::*, ast_util::Symbol, do_, monad::bind};

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    type_check_expr(ast, HashMap::new())
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
        // 3. functions
        Expr::Var(x) => match ctx.get(x) {
            Some(tau) => Ok(tau.clone()),
            None => Err(format!("Free variable: {}", x.0)),
        },
        Expr::Lam { x, tau, e } => do_!(
            {
                let mut ctx = ctx;
                ctx.insert(x.clone(), *tau.clone());
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
        // 4. product types
        Expr::Pair { left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            Ok(Type::Product { left: Box::new(tau_left), right: Box::new(tau_right) })
        ),
        Expr::Project { e, d } => do_!(
            type_check_expr(e, ctx) => tau_e,
            match (tau_e.clone(), d) {
                (Type::Product { left, .. }, Direction::Left) => Ok(*left),
                (Type::Product { right, .. }, Direction::Right) => Ok(*right),
                _ => Err(format!("Project has incompatible types: {:?}.{:?}", tau_e, d)),
            }
        ),
        Expr::Unit => Ok(Type::Unit),
        // 5. sum types
        Expr::Inject { e, d, tau } => do_!(
            type_check_expr(e, ctx) => tau_e,
            match (d, tau.as_ref()) {
                (Direction::Left, Type::Sum { left, .. }) if tau_e == **left => Ok(*tau.clone()),
                (Direction::Right, Type::Sum { right, .. }) if tau_e == **right => Ok(*tau.clone()),
                _ => Err(format!("Inject has incompatible types: inj {:?} = {:?} as {:?}", tau_e, d, tau)),
            }
        ),
        Expr::Case {
            e,
            xleft,
            eleft,
            xright,
            eright,
        } => do_!(
            type_check_expr(e, ctx.clone()) => tau_e,
            match tau_e {
                Type::Sum { left, right } => Ok((*left, *right)),
                _ => Err(format!("Case expression should be a sum type; found {:?}", tau_e)),
            } => (tau_xleft, tau_xright),
            {
                let mut ctx = ctx.clone();
                ctx.insert(xleft.clone(), tau_xleft);
                type_check_expr(eleft, ctx)
            } => tau_eleft,
            {
                let mut ctx = ctx;
                ctx.insert(xright.clone(), tau_xright);
                type_check_expr(eright, ctx)
            } => tau_eright,
            if tau_eleft == tau_eright {
                Ok(tau_eleft)
            } else {
                Err(format!("Case branches have incompatible types: {:?} and {:?}", tau_eleft, tau_eright))
            }
        ),
        // 6. fixpoints
        Expr::Fix { x, tau, e } => do_!(
            {
                let mut ctx = ctx;
                ctx.insert(x.clone(), *tau.clone());
                type_check_expr(e, ctx)
            } => tau_e,
            if tau_e == **tau {
                Ok(tau_e)
            } else {
                Err(format!("Fixpoint type mismatch: {:?} and {:?}", tau_e, tau))
            }
        ),
        // 7. polymorphism
        Expr::TyLam { a, e } => do_!(
            type_check_expr(e, ctx) => tau_e,
            Ok(Type::Forall { a: a.clone(), tau: Box::new(tau_e) })
        ),
        Expr::TyApp { e, tau: tau_arg } => do_!(
            type_check_expr(e, ctx) => tau_e,
            match tau_e {
                Type::Forall { a, tau: tau_body } => Ok(tau_body.substitute(a, *tau_arg.clone())),
                _ => Err(format!("Type application has incompatible types: {:?} [{:?}]", tau_e, tau_arg)),
            }
        ),
        _ => todo!("type_check_expr({:?})", ast),
    }
}
