use std::collections::HashMap;

use crate::{ast::*, ast_util::Symbol, do_, monad::Monad};

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
        // 2. conditionals
        Expr::True | Expr::False => Ok(Type::Bool),
        Expr::Relop { relop, left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Num, Type::Num) => Ok(Type::Bool),
                _ => type_mismatch!(tau_left, tau_right, relop),
            }
        ),
        Expr::If { cond, then_, else_ } => do_!(
            type_check_expr(cond, ctx.clone()) => tau_cond,
            type_check_expr(then_, ctx.clone()) => tau_then,
            type_check_expr(else_, ctx) => tau_else,
            match (tau_cond.clone(), tau_then.clone(), tau_else.clone()) {
                (Type::Bool, tau_then, tau_else) if Type::alpha_equiv(tau_then.clone(), tau_else.clone()) => Ok(tau_then),
                _ => Err(format!(r"If branches have incompatible types: if {:?} then {:?} else {:?}", tau_cond, tau_then, tau_else)),
            }
        ),
        Expr::And { left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                _ => type_mismatch!(tau_left, tau_right, "&&"),
            }
        ),
        Expr::Or { left, right } => do_!(
            type_check_expr(left, ctx.clone()) => tau_left,
            type_check_expr(right, ctx) => tau_right,
            match (tau_left.clone(), tau_right.clone()) {
                (Type::Bool, Type::Bool) => Ok(Type::Bool),
                _ => type_mismatch!(tau_left, tau_right, "||"),
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
            Ok(Type::Fn { arg: tau.clone(), ret: Box::new(tau_e) })
        ),
        Expr::App { lam, arg } => do_!(
            type_check_expr(lam, ctx.clone()) => tau_lam,
            type_check_expr(arg, ctx) => tau_arg,
            match tau_lam.clone() {
                Type::Fn { arg, ret } if Type::alpha_equiv(*arg.clone(), tau_arg.clone()) => Ok(*ret),
                _ => type_mismatch!(tau_lam, tau_arg, "function application"),
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
                _ => Err(format!("Projection has incompatible type: {:?}", tau_e)),
            }
        ),
        Expr::Unit => Ok(Type::Unit),
        // 5. sum types
        Expr::Inject { e, d, tau } => do_!(
            type_check_expr(e, ctx) => tau_e,
            match (d, tau.as_ref()) {
                (Direction::Left, Type::Sum { left, .. }) if Type::alpha_equiv(tau_e.clone(), *left.clone()) => Ok(*tau.clone()),
                (Direction::Right, Type::Sum { right, .. }) if Type::alpha_equiv(tau_e.clone(), *right.clone()) => Ok(*tau.clone()),
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
            if Type::alpha_equiv(tau_eleft.clone(), tau_eright.clone()) {
                Ok(tau_eleft)
            } else {
                type_mismatch!(tau_eleft, tau_eright, "case")
            }
        ),
        // 6. fixpoints
        Expr::Fix { x, tau, e } => do_!(
            {
                let mut ctx = ctx;
                ctx.insert(x.clone(), *tau.clone());
                type_check_expr(e, ctx)
            } => tau_e,
            if Type::alpha_equiv(*tau.clone(), tau_e.clone()) {
                Ok(tau_e)
            } else {
                type_mismatch!(tau, tau_e, "fixpoint")
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
                _ => type_mismatch!(tau_e, tau_arg, "type application"),
            }
        ),
        // 8. recursive types
        Expr::Fold { e, tau } => match tau.as_ref() {
            Type::Rec { a, tau: tau_body } => do_!(
                type_check_expr(e, ctx) => tau_e,
                if Type::alpha_equiv(tau_e.clone(), tau_body.clone().substitute(a.clone(), *tau.clone())) {
                    Ok(*tau.clone())
                } else {
                    type_mismatch!(tau_e, tau_body, "folding")
                }
            ),
            _ => Err(format!("Folding to type: {:?}", tau)),
        },
        Expr::Unfold(e) => do_!(
            type_check_expr(e, ctx) => tau_e,
            match tau_e.clone() {
                Type::Rec { a, tau: tau_body } => Ok(tau_body.substitute(a.clone(), tau_e)),
                _ => Err(format!("Unfolding from type: {:?}", tau_e)),
            }
        ),
        // 9. existential types
        Expr::Export {
            e,
            tau_adt,
            tau_mod,
        } => do_!(
            type_check_expr(e, ctx) => tau_e,
            if let Type::Exists { a, tau } = *tau_mod.clone() {
                if Type::alpha_equiv(tau_e.clone(), tau.clone().substitute(a.clone(), *tau_adt.clone())) {
                    Ok(*tau_mod.clone())
                } else {
                    type_mismatch!(tau_e, tau, "export")
                }
            } else {
                Err(format!("Type {:?} is not an existential type", tau_mod))
            }
        ),
        Expr::Import {
            x,
            a: b,
            e_mod,
            e_body,
        } => do_!(
            type_check_expr(e_mod, ctx.clone()) => tau_exist,
            if let Type::Exists { a, tau: tau_mod } = tau_exist {
                let mut ctx = ctx;
                ctx.insert(x.clone(), tau_mod.substitute(a, Type::Var(b.clone())));
                type_check_expr(e_body, ctx)
            } else {
                Err(format!("Type {:?} is not an existential type", tau_exist))
            }
        ),
    }
}
