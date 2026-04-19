use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicU32, Ordering};

static VAR_ID: AtomicU32 = AtomicU32::new(0);

use crate::ast_util::Symbol;
use crate::{ast::*, union_find::UnionFind};

type Constraint = Vec<(Type, Type)>;

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    let (cur_type, constraints) = type_check_expr(ast, HashMap::new())?;
    let (mut uf, map) = unification(constraints)?;
    get_type(cur_type, &mut uf, &map)
}

fn fresh_type_var() -> Type {
    let cur_id = VAR_ID.fetch_add(1, Ordering::Relaxed);
    Type::Var(Variable(format!("type_{cur_id}")))
}

macro_rules! flat {
    ($vec:expr) => {
        $vec.into_iter().flatten().collect()
    };
}

fn all_type_vars(tau: &Type) -> Vec<Variable> {
    match tau {
        Type::Bool | Type::Num | Type::Unit => vec![],
        Type::Var(x) => vec![x.clone()],
        Type::Fn { arg, ret } => flat!(vec![all_type_vars(arg), all_type_vars(ret)]),
        _ => todo!(),
    }
}

fn unification(
    constraint: Constraint,
) -> Result<(UnionFind<Variable>, HashMap<Variable, Type>), String> {
    let variables: Vec<Variable> = constraint
        .iter()
        .flat_map(|(x, y)| vec![x, y])
        .flat_map(all_type_vars)
        .collect();
    let mut uf = UnionFind::new(variables);
    let mut map = HashMap::new();
    let mut constraint = VecDeque::from(constraint);
    while !constraint.is_empty() {
        match constraint.pop_front().unwrap() {
            (Type::Bool, Type::Bool) | (Type::Num, Type::Num) | (Type::Unit, Type::Unit) => (),
            (Type::Var(l), Type::Var(r)) => {
                uf.union(&l, &r);
            }
            (Type::Var(var), val) | (val, Type::Var(var)) => match map.insert(var, val.clone()) {
                None => (),
                Some(old_val) => {
                    constraint.push_back((old_val, val));
                }
            },
            (
                Type::Fn {
                    arg: arg_l,
                    ret: ret_l,
                },
                Type::Fn {
                    arg: arg_r,
                    ret: ret_r,
                },
            ) => {
                constraint.extend(vec![(*arg_l, *arg_r), (*ret_l, *ret_r)].into_iter());
            }
            (lhs, rhs) => return Err(format!("Unification failed with type {lhs} and {rhs}")),
        }
    }
    let updated_map = map
        .into_iter()
        .map(|(x, y)| (uf.find(&x).clone(), y))
        .collect();
    Ok((uf, updated_map))
}

fn get_type_var(
    tau: Variable,
    uf: &mut UnionFind<Variable>,
    map: &HashMap<Variable, Type>,
) -> Result<Type, String> {
    let root = uf.find(&tau);
    let result = match map.get(root) {
        Some(r) => r,
        None => return Err(format!("Free variable {root}")),
    };
    let mut var_to_type = HashMap::new();
    for v in all_type_vars(result).iter() {
        let ty = get_type_var(v.clone(), uf, map)?;
        var_to_type.insert(v.clone(), ty);
    }
    Ok(result.clone().substitute_map(var_to_type))
}

fn get_type(
    tau: Type,
    uf: &mut UnionFind<Variable>,
    map: &HashMap<Variable, Type>,
) -> Result<Type, String> {
    match tau {
        Type::Bool | Type::Num | Type::Unit => Ok(tau),
        Type::Var(x) => get_type_var(x, uf, map),
        Type::Fn { arg, ret } => {
            let tau_arg = get_type(*arg, uf, map)?;
            let tau_ret = get_type(*ret, uf, map)?;
            Ok(Type::Fn {
                arg: Box::new(tau_arg),
                ret: Box::new(tau_ret),
            })
        }
        _ => todo!(),
    }
}

// TODO: Change its name to get_constraints after we have finish every cases
fn type_check_expr(ast: &Expr, ctx: HashMap<Variable, Type>) -> Result<(Type, Constraint), String> {
    match ast {
        // 1. arithmetic
        Expr::Num(_) => Ok((Type::Num, vec![])),
        Expr::Addop { left, right, .. } | Expr::Mulop { left, right, .. } => {
            let (tau_left, c_left) = type_check_expr(left, ctx.clone())?;
            let (tau_right, c_right) = type_check_expr(right, ctx.clone())?;
            let constraints = flat!(vec![
                c_left,
                c_right,
                vec![(tau_left, Type::Num), (tau_right, Type::Num)],
            ]);
            Ok((Type::Num, constraints))
        }
        // 2. conditionals
        Expr::True | Expr::False => Ok((Type::Bool, vec![])),
        Expr::Relop { left, right, .. } => {
            let (tau_left, c_left) = type_check_expr(left, ctx.clone())?;
            let (tau_right, c_right) = type_check_expr(right, ctx)?;
            let constraints = flat!(vec![
                c_left,
                c_right,
                vec![(tau_left, Type::Num), (tau_right, Type::Num)],
            ]);
            Ok((Type::Bool, constraints))
        }
        Expr::If { cond, then_, else_ } => {
            let (tau_cond, c_cond) = type_check_expr(cond, ctx.clone())?;
            let (tau_then, c_then) = type_check_expr(then_, ctx.clone())?;
            let (tau_else, c_else) = type_check_expr(else_, ctx)?;
            let constraints = flat!(vec![
                c_cond,
                c_then,
                c_else,
                vec![(tau_cond, Type::Bool), (tau_then.clone(), tau_else)],
            ]);
            Ok((tau_then, constraints))
        }
        Expr::And { left, right } | Expr::Or { left, right } => {
            let (tau_left, c_left) = type_check_expr(left, ctx.clone())?;
            let (tau_right, c_right) = type_check_expr(right, ctx)?;
            let constraints = flat!(vec![
                c_left,
                c_right,
                vec![(tau_left, Type::Bool), (tau_right, Type::Bool)],
            ]);
            Ok((Type::Bool, constraints))
        }
        // 3. functions
        Expr::Var(x) => match ctx.get(x) {
            Some(tau) => Ok((tau.clone(), vec![])),
            None => Err(format!("Free variable: {x}")),
        },
        Expr::Lam { x, e } => {
            let tau = fresh_type_var();
            let mut ctx_and_x = ctx.clone();
            ctx_and_x.insert(x.clone(), tau.clone());
            let (tau_ret, c_ret) = type_check_expr(e, ctx_and_x)?;
            Ok((
                Type::Fn {
                    arg: Box::new(tau),
                    ret: Box::new(tau_ret),
                },
                c_ret,
            ))
        }
        Expr::App { lam, arg } => {
            let (tau_lam, c_lam) = type_check_expr(lam, ctx.clone())?;
            let (tau_arg, c_arg) = type_check_expr(arg, ctx)?;
            let tau_ret = fresh_type_var();
            let constraints = flat!(vec![
                c_lam,
                c_arg,
                vec![(
                    tau_lam,
                    Type::Fn {
                        arg: Box::new(tau_arg),
                        ret: Box::new(tau_ret.clone()),
                    },
                )],
            ]);
            Ok((tau_ret, constraints))
        }
        // // 4. product types
        // Expr::Pair { left, right } => do_!(
        //     type_check_expr(left, ctx.clone()) => tau_left,
        //     type_check_expr(right, ctx) => tau_right,
        //     Ok(Type::Product { left: Box::new(tau_left), right: Box::new(tau_right) })
        // ),
        // Expr::Project { e, d } => do_!(
        //     type_check_expr(e, ctx) => tau_e,
        //     match (tau_e.clone(), d) {
        //         (Type::Product { left, .. }, Direction::Left) => Ok(*left),
        //         (Type::Product { right, .. }, Direction::Right) => Ok(*right),
        //         _ => Err(format!("Projection has incompatible type: {:?}", tau_e)),
        //     }
        // ),
        Expr::Unit => Ok((Type::Unit, vec![])),
        // // 5. sum types
        // Expr::Inject { e, d, tau } => do_!(
        //     type_check_expr(e, ctx) => tau_e,
        //     match (d, tau.as_ref()) {
        //         (Direction::Left, Type::Sum { left, .. }) if Type::alpha_equiv(tau_e.clone(), *left.clone()) => Ok(*tau.clone()),
        //         (Direction::Right, Type::Sum { right, .. }) if Type::alpha_equiv(tau_e.clone(), *right.clone()) => Ok(*tau.clone()),
        //         _ => Err(format!("Inject has incompatible types: inj {:?} = {:?} as {:?}", tau_e, d, tau)),
        //     }
        // ),
        // Expr::Case {
        //     e,
        //     xleft,
        //     eleft,
        //     xright,
        //     eright,
        // } => do_!(
        //     type_check_expr(e, ctx.clone()) => tau_e,
        //     match tau_e {
        //         Type::Sum { left, right } => Ok((*left, *right)),
        //         _ => Err(format!("Case expression should be a sum type; found {:?}", tau_e)),
        //     } => (tau_xleft, tau_xright),
        //     {
        //         let mut ctx = ctx.clone();
        //         ctx.insert(xleft.clone(), tau_xleft);
        //         type_check_expr(eleft, ctx)
        //     } => tau_eleft,
        //     {
        //         let mut ctx = ctx;
        //         ctx.insert(xright.clone(), tau_xright);
        //         type_check_expr(eright, ctx)
        //     } => tau_eright,
        //     if Type::alpha_equiv(tau_eleft.clone(), tau_eright.clone()) {
        //         Ok(tau_eleft)
        //     } else {
        //         type_mismatch!(tau_eleft, tau_eright, "case")
        //     }
        // ),
        // // 6. fixpoints
        // Expr::Fix { x, tau, e } => do_!(
        //     {
        //         let mut ctx = ctx;
        //         ctx.insert(x.clone(), *tau.clone());
        //         type_check_expr(e, ctx)
        //     } => tau_e,
        //     if Type::alpha_equiv(*tau.clone(), tau_e.clone()) {
        //         Ok(tau_e)
        //     } else {
        //         type_mismatch!(tau, tau_e, "fixpoint")
        //     }
        // ),
        // // 7. polymorphism
        // Expr::TyLam { a, e } => do_!(
        //     type_check_expr(e, ctx) => tau_e,
        //     Ok(Type::Forall { a: a.clone(), tau: Box::new(tau_e) })
        // ),
        // Expr::TyApp { e, tau: tau_arg } => do_!(
        //     type_check_expr(e, ctx) => tau_e,
        //     match tau_e {
        //         Type::Forall { a, tau: tau_body } => Ok(tau_body.substitute(a, *tau_arg.clone())),
        //         _ => type_mismatch!(tau_e, tau_arg, "type application"),
        //     }
        // ),
        // // 8. recursive types
        // Expr::Fold { e, tau } => match tau.as_ref() {
        //     Type::Rec { a, tau: tau_body } => do_!(
        //         type_check_expr(e, ctx) => tau_e,
        //         if Type::alpha_equiv(tau_e.clone(), tau_body.clone().substitute(a.clone(), *tau.clone())) {
        //             Ok(*tau.clone())
        //         } else {
        //             type_mismatch!(tau_e, tau_body, "folding")
        //         }
        //     ),
        //     _ => Err(format!("Folding to type: {:?}", tau)),
        // },
        // Expr::Unfold(e) => do_!(
        //     type_check_expr(e, ctx) => tau_e,
        //     match tau_e.clone() {
        //         Type::Rec { a, tau: tau_body } => Ok(tau_body.substitute(a.clone(), tau_e)),
        //         _ => Err(format!("Unfolding from type: {:?}", tau_e)),
        //     }
        // ),
        // // 9. existential types
        // Expr::Export {
        //     e,
        //     tau_adt,
        //     tau_mod,
        // } => do_!(
        //     type_check_expr(e, ctx) => tau_e,
        //     if let Type::Exists { a, tau } = *tau_mod.clone() {
        //         if Type::alpha_equiv(tau_e.clone(), tau.clone().substitute(a.clone(), *tau_adt.clone())) {
        //             Ok(*tau_mod.clone())
        //         } else {
        //             type_mismatch!(tau_e, tau, "export")
        //         }
        //     } else {
        //         Err(format!("Type {:?} is not an existential type", tau_mod))
        //     }
        // ),
        // Expr::Import {
        //     x,
        //     a: b,
        //     e_mod,
        //     e_body,
        // } => do_!(
        //     type_check_expr(e_mod, ctx.clone()) => tau_exist,
        //     if let Type::Exists { a, tau: tau_mod } = tau_exist {
        //         let mut ctx = ctx;
        //         ctx.insert(x.clone(), tau_mod.substitute(a, Type::Var(b.clone())));
        //         type_check_expr(e_body, ctx)
        //     } else {
        //         Err(format!("Type {:?} is not an existential type", tau_exist))
        //     }
        // ),
        _ => todo!(),
    }
}
