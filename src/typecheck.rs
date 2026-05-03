use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::sync::atomic::{AtomicU32, Ordering};

static VAR_ID: AtomicU32 = AtomicU32::new(0);

use crate::ast_util::{Printer, Symbol};
use crate::{ast::*, union_find::UnionFind};

struct Constraint {
    /// The type on the left.
    type_l: Type,
    /// The type on the right.
    type_r: Type,
    /// A string that represents the left type for debug purpose.
    expr_l: String,
    /// A string that represents the right type for debug purpose.
    expr_r: String,
}

impl Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} = {}: {}",
            self.expr_l, self.type_l, self.expr_r, self.type_r
        )
    }
}

macro_rules! flat {
    ($vec:expr) => {
        $vec.into_iter().flatten().collect()
    };
}

fn type_check_with_free_vars(ast: &Expr) -> Result<Type, String> {
    let mut ctx = vec![];
    let ast = ast.clone().to_debruijn();
    // println!("{ast}");
    let (cur_type, constraints) = type_check_expr(&ast, &mut ctx)?;
    // println!(
    //     "ty: {cur_type}, {}",
    //     Printer(" ").print_it(constraints.iter())
    // );
    // println!("-----------");
    assert!(ctx.is_empty());
    let (mut uf, map) = unification(constraints)?;
    Ok(get_type(cur_type, &mut uf, &map))
}

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    let ty = type_check_with_free_vars(ast)?;
    let all_vars_set = HashSet::<_>::from_iter(all_type_vars(&ty));
    let scoped_vars_set = HashSet::<_>::from_iter(scoped_type_vars(&ty));
    // println!("{}", Printer(", ").print_it(all_vars_set.iter()));
    // println!("{}", Printer(", ").print_it(scoped_vars_set.iter()));
    // println!("-----------");
    let free_vars: Vec<_> = all_vars_set.difference(&scoped_vars_set).collect();
    if free_vars.is_empty() {
        Ok(ty)
    } else {
        Err(format!(
            "Free variable: {}",
            Printer(", ").print_it(free_vars.iter())
        ))
    }
}

fn fresh_type_var() -> Type {
    let cur_id = VAR_ID.fetch_add(1, Ordering::Relaxed);
    Type::Var(Variable(format!("type_{cur_id}")))
}

fn scoped_type_vars(tau: &Type) -> Vec<Variable> {
    match tau {
        Type::Bool | Type::Num | Type::Unit | Type::Var(_) => vec![],
        Type::Fn { arg, ret } => flat!(vec![scoped_type_vars(arg), scoped_type_vars(ret)]),
        Type::Product { left, right } | Type::Sum { left, right } => {
            flat!(vec![scoped_type_vars(left), scoped_type_vars(right)])
        }
        Type::Forall { a, tau } => flat!(vec![vec![a.clone()], scoped_type_vars(tau)]),
        _ => todo!(),
    }
}

fn all_type_vars(tau: &Type) -> Vec<Variable> {
    match tau {
        Type::Bool | Type::Num | Type::Unit => vec![],
        Type::Var(x) => vec![x.clone()],
        Type::Fn { arg, ret } => flat!(vec![all_type_vars(arg), all_type_vars(ret)]),
        Type::Product { left, right } | Type::Sum { left, right } => {
            flat!(vec![all_type_vars(left), all_type_vars(right)])
        }
        _ => todo!(),
    }
}

fn unification(
    constraints: Vec<Constraint>,
) -> Result<(UnionFind<Variable>, HashMap<Variable, Type>), String> {
    let variables: Vec<Variable> = constraints
        .iter()
        .flat_map(|c| vec![&c.type_l, &c.type_r])
        .flat_map(all_type_vars)
        .collect();
    let mut uf = UnionFind::new(variables);
    let mut map: HashMap<Variable, Type> = HashMap::new();
    let mut constraints = VecDeque::from(constraints);
    while !constraints.is_empty() {
        let constraint = constraints.pop_front().unwrap();
        match (constraint.type_l, constraint.type_r) {
            (Type::Bool, Type::Bool) | (Type::Num, Type::Num) | (Type::Unit, Type::Unit) => (),
            (Type::Var(l), Type::Var(r)) => {
                uf.union(&l, &r).unwrap();
                match (map.get(&l), map.get(&r)) {
                    (Some(lval), Some(rval)) => {
                        constraints.push_back(Constraint {
                            type_l: lval.clone(),
                            type_r: rval.clone(),
                            expr_l: format!("val({})", l),
                            expr_r: format!("val({})", r),
                        });
                    }
                    _ => (),
                }
            }
            (Type::Var(var), val) | (val, Type::Var(var)) => match map.insert(var, val.clone()) {
                // TODO: check whether val contains var
                None => (),
                Some(old_val) => {
                    constraints.push_back(Constraint {
                        type_l: old_val,
                        type_r: val,
                        expr_l: constraint.expr_l,
                        expr_r: constraint.expr_r,
                    });
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
                constraints.extend(
                    vec![
                        Constraint {
                            type_l: *arg_l,
                            type_r: *arg_r,
                            expr_l: format!("arg({})", constraint.expr_l),
                            expr_r: format!("arg({})", constraint.expr_r),
                        },
                        Constraint {
                            type_l: *ret_l,
                            type_r: *ret_r,
                            expr_l: format!("ret({})", constraint.expr_l),
                            expr_r: format!("ret({})", constraint.expr_r),
                        },
                    ]
                    .into_iter(),
                );
            }
            (
                Type::Product {
                    left: l_1,
                    right: r_1,
                },
                Type::Product {
                    left: l_2,
                    right: r_2,
                },
            )
            | (
                Type::Sum {
                    left: l_1,
                    right: r_1,
                },
                Type::Sum {
                    left: l_2,
                    right: r_2,
                },
            ) => {
                constraints.extend(
                    vec![
                        Constraint {
                            type_l: *l_1,
                            type_r: *l_2,
                            expr_l: format!("({}).L", constraint.expr_l),
                            expr_r: format!("({}).L", constraint.expr_r),
                        },
                        Constraint {
                            type_l: *r_1,
                            type_r: *r_2,
                            expr_l: format!("({}).R", constraint.expr_l),
                            expr_r: format!("({}).R", constraint.expr_r),
                        },
                    ]
                    .into_iter(),
                );
            }
            (lhs, rhs) => return Err(format!("Unification failed with type {lhs} and {rhs}")),
        }
    }
    let updated_map = map
        .into_iter()
        .map(|(x, y)| (uf.find(&x).unwrap().clone(), y))
        .collect();
    Ok((uf, updated_map))
}

fn get_type_var(
    tau: Variable,
    uf: &mut UnionFind<Variable>,
    map: &HashMap<Variable, Type>,
) -> Type {
    let result = match uf.find(&tau).ok().and_then(|x| map.get(x)) {
        Some(r) => r,
        None => return Type::Var(tau),
    };
    let mut var_to_type = HashMap::new();
    for v in all_type_vars(result).iter() {
        let ty = get_type_var(v.clone(), uf, map);
        var_to_type.insert(v.clone(), ty);
    }
    result.clone().substitute_map(var_to_type)
}

macro_rules! trivial_get_type {
    ($arm:tt, $x:ident, $y:ident, $uf:ident, $map:ident) => {{
        let tx = get_type(*$x, $uf, $map);
        let ty = get_type(*$y, $uf, $map);
        Type::$arm {
            $x: Box::new(tx),
            $y: Box::new(ty),
        }
    }};
}

fn get_type(tau: Type, uf: &mut UnionFind<Variable>, map: &HashMap<Variable, Type>) -> Type {
    match tau {
        Type::Bool | Type::Num | Type::Unit => tau,
        Type::Var(x) => get_type_var(x, uf, map),
        Type::Fn { arg, ret } => trivial_get_type!(Fn, arg, ret, uf, map),
        Type::Product { left, right } => {
            trivial_get_type!(Product, left, right, uf, map)
        }
        Type::Sum { left, right } => {
            trivial_get_type!(Sum, left, right, uf, map)
        }
        _ => todo!(),
    }
}

// TODO: Change its name to get_constraints after we have finish every cases
fn type_check_expr(ast: &Expr, ctx: &mut Vec<Type>) -> Result<(Type, Vec<Constraint>), String> {
    match ast {
        // 1. arithmetic
        Expr::Num(_) => Ok((Type::Num, vec![])),
        Expr::Addop { left, right, .. } | Expr::Mulop { left, right, .. } => {
            let (tau_left, c_left) = type_check_expr(left, ctx)?;
            let (tau_right, c_right) = type_check_expr(right, ctx)?;
            let constraints = flat!(vec![
                c_left,
                c_right,
                vec![
                    Constraint {
                        type_l: tau_left,
                        type_r: Type::Num,
                        expr_l: left.to_string(),
                        expr_r: "Num".to_string()
                    },
                    Constraint {
                        type_l: tau_right,
                        type_r: Type::Num,
                        expr_l: right.to_string(),
                        expr_r: "Num".to_string()
                    },
                ]
            ]);
            Ok((Type::Num, constraints))
        }
        // 2. conditionals
        Expr::True | Expr::False => Ok((Type::Bool, vec![])),
        Expr::Relop { left, right, .. } => {
            let (tau_left, c_left) = type_check_expr(left, ctx)?;
            let (tau_right, c_right) = type_check_expr(right, ctx)?;
            let constraints = flat!(vec![
                c_left,
                c_right,
                vec![
                    Constraint {
                        type_l: tau_left,
                        type_r: Type::Num,
                        expr_l: left.to_string(),
                        expr_r: "Num".to_string()
                    },
                    Constraint {
                        type_l: tau_right,
                        type_r: Type::Num,
                        expr_l: right.to_string(),
                        expr_r: "Num".to_string()
                    },
                ]
            ]);
            Ok((Type::Bool, constraints))
        }
        Expr::If { cond, then_, else_ } => {
            let (tau_cond, c_cond) = type_check_expr(cond, ctx)?;
            let (tau_then, c_then) = type_check_expr(then_, ctx)?;
            let (tau_else, c_else) = type_check_expr(else_, ctx)?;
            let constraints = flat!(vec![
                c_cond,
                c_then,
                c_else,
                vec![
                    Constraint {
                        type_l: tau_cond,
                        type_r: Type::Bool,
                        expr_l: cond.to_string(),
                        expr_r: "Bool".to_string()
                    },
                    Constraint {
                        type_l: tau_then.clone(),
                        type_r: tau_else,
                        expr_l: then_.to_string(),
                        expr_r: else_.to_string()
                    },
                ]
            ]);
            Ok((tau_then, constraints))
        }
        Expr::And { left, right } | Expr::Or { left, right } => {
            let (tau_left, c_left) = type_check_expr(left, ctx)?;
            let (tau_right, c_right) = type_check_expr(right, ctx)?;
            let constraints = flat!(vec![
                c_left,
                c_right,
                vec![
                    Constraint {
                        type_l: tau_left,
                        type_r: Type::Bool,
                        expr_l: left.to_string(),
                        expr_r: "Bool".to_string()
                    },
                    Constraint {
                        type_l: tau_right,
                        type_r: Type::Bool,
                        expr_l: right.to_string(),
                        expr_r: "Bool".to_string()
                    },
                ]
            ]);
            Ok((Type::Bool, constraints))
        }
        // 3. functions
        Expr::Var(x) => Err(format!("Free variable: {x}")),
        Expr::DeBruijn(depth) => Ok((
            ctx.iter().rev().skip(*depth).next().unwrap().clone(),
            vec![],
        )),
        Expr::Lam { x: _, e } => {
            let tau = fresh_type_var();
            ctx.push(tau);
            let (tau_ret, c_ret) = type_check_expr(e, ctx)?;
            let tau = ctx.pop().unwrap();
            Ok((
                Type::Fn {
                    arg: Box::new(tau),
                    ret: Box::new(tau_ret),
                },
                c_ret,
            ))
        }
        Expr::App { lam, arg } => {
            let (tau_lam, c_lam) = type_check_expr(lam, ctx)?;
            let (tau_arg, c_arg) = type_check_expr(arg, ctx)?;
            let tau_ret = fresh_type_var();
            let constraints = flat!(vec![
                c_lam,
                c_arg,
                vec![Constraint {
                    type_l: tau_lam,
                    expr_r: format!("{} → {}", tau_arg, tau_ret),
                    type_r: Type::Fn {
                        arg: Box::new(tau_arg),
                        ret: Box::new(tau_ret.clone()),
                    },
                    expr_l: lam.to_string()
                }]
            ]);
            Ok((tau_ret, constraints))
        }
        // 4. product types
        Expr::Pair { left, right } => {
            let (tau_l, c_l) = type_check_expr(left, ctx)?;
            let (tau_r, c_r) = type_check_expr(right, ctx)?;
            let constraints = flat!(vec![c_l, c_r]);
            Ok((
                Type::Product {
                    left: Box::new(tau_l),
                    right: Box::new(tau_r),
                },
                constraints,
            ))
        }
        Expr::Project { e, d } => {
            let (tau_e, c_e) = type_check_expr(e, ctx)?;
            let tau_l = fresh_type_var();
            let tau_r = fresh_type_var();
            let constraints = flat!(vec![
                c_e,
                vec![Constraint {
                    type_l: tau_e,
                    expr_r: format!("({} * {})", tau_l, tau_r),
                    type_r: Type::Product {
                        left: Box::new(tau_l.clone()),
                        right: Box::new(tau_r.clone()),
                    },
                    expr_l: e.to_string()
                }]
            ]);
            let tau_ret = match d {
                Direction::Left => tau_l,
                Direction::Right => tau_r,
            };
            Ok((tau_ret, constraints))
        }
        Expr::Unit => Ok((Type::Unit, vec![])),
        // 5. sum types
        Expr::Inject { e, d } => {
            let (tau_e, c_e) = type_check_expr(e, ctx)?;
            let tau_other = fresh_type_var();
            let tau_full = match d {
                Direction::Left => Type::Sum {
                    left: Box::new(tau_e.clone()),
                    right: Box::new(tau_other.clone()),
                },
                Direction::Right => Type::Sum {
                    left: Box::new(tau_other.clone()),
                    right: Box::new(tau_e.clone()),
                },
            };
            Ok((tau_full, c_e))
        }
        Expr::Case {
            e,
            xleft: _,
            eleft,
            xright: _,
            eright,
        } => {
            let (tau_sum, c_sum) = type_check_expr(e, ctx)?;
            let tau_l = fresh_type_var();
            let tau_r = fresh_type_var();

            ctx.push(tau_l);
            let (tau_l_after, c_l) = type_check_expr(eleft, ctx)?;
            let tau_l = ctx.pop().unwrap();
            ctx.push(tau_r);
            let (tau_r_after, c_r) = type_check_expr(eright, ctx)?;
            let tau_r = ctx.pop().unwrap();

            let constraints = flat!(vec![
                c_sum,
                c_l,
                c_r,
                vec![
                    Constraint {
                        type_l: tau_sum,
                        expr_r: format!("({}+{})", tau_l, tau_r),
                        type_r: Type::Sum {
                            left: Box::new(tau_l.clone()),
                            right: Box::new(tau_r.clone()),
                        },
                        expr_l: e.to_string()
                    },
                    Constraint {
                        type_l: tau_l_after.clone(),
                        type_r: tau_r_after,
                        expr_l: eleft.to_string(),
                        expr_r: eright.to_string()
                    },
                ]
            ]);
            Ok((tau_l_after, constraints))
        }
        // 6. fixpoints
        Expr::Fix { x, e } => {
            let tau_x = fresh_type_var();
            ctx.push(tau_x);
            let (tau_e, c_e) = type_check_expr(e, ctx)?;
            let tau_x = ctx.pop().unwrap();
            let constraints = flat!(vec![
                c_e,
                vec![Constraint {
                    type_l: tau_x.clone(),
                    type_r: tau_e,
                    expr_l: x.to_string(),
                    expr_r: e.to_string()
                }]
            ]);
            Ok((tau_x, constraints))
        }
        // 7. polymorphism
        // Expr::Let { x, e_x, e_in } => {
        //     let tau_e = type_check_with_free_vars(e_x)?;

        //     todo!()
        // }
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
