use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::hash::Hash;
use std::sync::atomic::{AtomicU32, Ordering};

static VAR_ID: AtomicU32 = AtomicU32::new(0);

use crate::ast_util::{Printer, Symbol};
use crate::{ast::*, union_find::UnionFind};

#[derive(Clone)]
pub struct Constraint {
    /// The type on the left.
    type_l: Type,
    /// The type on the right.
    type_r: Type,
    /// A string that represents the left type for debug purpose.
    expr_l: String,
    /// A string that represents the right type for debug purpose.
    expr_r: String,
}

macro_rules! flat {
    ($vec:expr) => {
        $vec.into_iter().flatten().collect()
    };
}

fn vec_diff<T>(vec1: Vec<T>, vec2: Vec<T>) -> Vec<T>
where
    T: Hash + Eq + Clone,
{
    let vec1_set = HashSet::<_>::from_iter(vec1);
    let vec2_set = HashSet::<_>::from_iter(vec2);
    vec1_set.difference(&vec2_set).cloned().collect()
}

trait GetVars {
    fn get_all_vars(&self) -> Vec<Variable>;
    fn get_scoped_vars(&self) -> Vec<Variable>;
    fn get_free_vars(&self) -> Vec<Variable> {
        vec_diff(self.get_all_vars(), self.get_scoped_vars())
    }
}

impl<T> GetVars for Vec<T>
where
    T: GetVars,
{
    fn get_all_vars(&self) -> Vec<Variable> {
        self.iter().flat_map(|x| x.get_all_vars()).collect()
    }
    fn get_scoped_vars(&self) -> Vec<Variable> {
        self.iter().flat_map(|x| x.get_scoped_vars()).collect()
    }
}

impl GetVars for Type {
    fn get_scoped_vars(&self) -> Vec<Variable> {
        match self {
            Type::Bool | Type::Num | Type::Unit | Type::Var(_) => vec![],
            Type::Fn { arg, ret } => arg
                .get_scoped_vars()
                .into_iter()
                .chain(ret.get_scoped_vars())
                .collect(),
            Type::Product { left, right } | Type::Sum { left, right } => left
                .get_scoped_vars()
                .into_iter()
                .chain(right.get_scoped_vars())
                .collect(),
            Type::Forall { a, tau } => std::iter::once(a.clone())
                .chain(tau.get_scoped_vars())
                .collect(),
            _ => todo!(),
        }
    }

    fn get_all_vars(&self) -> Vec<Variable> {
        match self {
            Type::Bool | Type::Num | Type::Unit => vec![],
            Type::Var(x) => vec![x.clone()],
            Type::Fn { arg, ret } => arg
                .get_all_vars()
                .into_iter()
                .chain(ret.get_all_vars())
                .collect(),
            Type::Product { left, right } | Type::Sum { left, right } => left
                .get_all_vars()
                .into_iter()
                .chain(right.get_all_vars())
                .collect(),
            Type::Forall { a, tau } => std::iter::once(a.clone())
                .chain(tau.get_all_vars())
                .collect(),
            _ => todo!(),
        }
    }
}

impl Type {
    fn instantiate(self) -> Self {
        match self {
            Type::Bool | Type::Num | Type::Unit | Type::Var(_) => self,
            Type::Forall { a, tau } => tau.instantiate().substitute(a, fresh_type_var()),
            Type::Sum { left, right } => Type::Sum {
                left: left.instantiate().into(),
                right: right.instantiate().into(),
            },
            Type::Product { left, right } => Type::Product {
                left: left.instantiate().into(),
                right: right.instantiate().into(),
            },
            Type::Fn { arg, ret } => Type::Fn {
                arg: arg.instantiate().into(),
                ret: ret.instantiate().into(),
            },
            _ => todo!(),
        }
    }

    fn generalize(self, ctx: &Vec<Type>, constraints: Vec<Constraint>) -> Result<Type, String> {
        let (uf, map) = unification(constraints)?;
        let mut tau_x = get_type(self, uf, map);
        for a in vec_diff(tau_x.get_free_vars(), ctx.get_free_vars()) {
            tau_x = tau_x.add_one_quantifier(a);
        }
        Ok(tau_x)
    }

    fn add_one_quantifier(self, a: Variable) -> Self {
        Type::Forall {
            a,
            tau: self.into(),
        }
    }
}

impl Expr {
    pub fn get_constraints(&self, ctx: &mut Vec<Type>) -> Result<(Type, Vec<Constraint>), String> {
        match self {
            // 1. arithmetic
            Expr::Num(_) => Ok((Type::Num, vec![])),
            Expr::Addop { left, right, .. } | Expr::Mulop { left, right, .. } => {
                let (tau_left, c_left) = left.get_constraints(ctx)?;
                let (tau_right, c_right) = right.get_constraints(ctx)?;
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
                let (tau_left, c_left) = left.get_constraints(ctx)?;
                let (tau_right, c_right) = right.get_constraints(ctx)?;
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
                let (tau_cond, c_cond) = cond.get_constraints(ctx)?;
                let (tau_then, c_then) = then_.get_constraints(ctx)?;
                let (tau_else, c_else) = else_.get_constraints(ctx)?;
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
                let (tau_left, c_left) = left.get_constraints(ctx)?;
                let (tau_right, c_right) = right.get_constraints(ctx)?;
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
                ctx.iter()
                    .rev()
                    .skip(*depth)
                    .next()
                    .unwrap()
                    .clone()
                    .instantiate(),
                vec![],
            )),
            Expr::Lam { x: _, e } => {
                let tau = fresh_type_var();
                ctx.push(tau);
                let (tau_ret, c_ret) = e.get_constraints(ctx)?;
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
                let (tau_lam, c_lam) = lam.get_constraints(ctx)?;
                let (tau_arg, c_arg) = arg.get_constraints(ctx)?;
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
                let (tau_l, c_l) = left.get_constraints(ctx)?;
                let (tau_r, c_r) = right.get_constraints(ctx)?;
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
                let (tau_e, c_e) = e.get_constraints(ctx)?;
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
                let (tau_e, c_e) = e.get_constraints(ctx)?;
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
                e, eleft, eright, ..
            } => {
                let (tau_sum, c_sum) = e.get_constraints(ctx)?;
                let tau_l = fresh_type_var();
                let tau_r = fresh_type_var();

                ctx.push(tau_l);
                let (tau_l_after, c_l) = eleft.get_constraints(ctx)?;
                let tau_l = ctx.pop().unwrap();
                ctx.push(tau_r);
                let (tau_r_after, c_r) = eright.get_constraints(ctx)?;
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
                let (tau_e, c_e) = e.get_constraints(ctx)?;
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
            Expr::Let { e_x, e_in, .. } => {
                let (tau_x, c_x) = e_x.get_constraints(ctx)?;
                ctx.push(tau_x.generalize(ctx, c_x.clone())?);
                let (tau_in, c_in) = e_in.get_constraints(ctx)?;
                let _ = ctx.pop().unwrap();
                Ok((tau_in, flat!(vec![c_in, c_x])))
            }
            _ => todo!(),
        }
    }

    fn type_check(self) -> Result<Type, String> {
        let mut ctx = vec![];
        let (cur_type, constraints) = self.get_constraints(&mut ctx)?;
        assert!(ctx.is_empty());
        let (uf, map) = unification(constraints)?;
        Ok(get_type(cur_type, uf, map))
    }
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

pub fn type_check(ast: &Expr) -> Result<Type, String> {
    let ty = ast.clone().to_debruijn().type_check()?;
    assert!(ty.get_free_vars().is_empty());
    Ok(ty)
}

fn fresh_type_var() -> Type {
    let cur_id = VAR_ID.fetch_add(1, Ordering::Relaxed);
    Type::Var(Variable(format!("type_{cur_id}")))
}

fn unification(
    constraints: Vec<Constraint>,
) -> Result<(UnionFind<Variable>, HashMap<Variable, Type>), String> {
    let variables: Vec<Variable> = constraints
        .iter()
        .flat_map(|c| vec![&c.type_l, &c.type_r])
        .flat_map(|t| t.get_all_vars())
        .collect();
    let mut uf = UnionFind::new(variables);
    let mut map: HashMap<Variable, Type> = HashMap::new();
    let mut constraints = VecDeque::from(constraints);
    while !constraints.is_empty() {
        let constraint = constraints.pop_front().unwrap();
        match (constraint.type_l, constraint.type_r) {
            (Type::Bool, Type::Bool) | (Type::Num, Type::Num) | (Type::Unit, Type::Unit) => (),
            (Type::Var(l), Type::Var(r)) => {
                let l_root = uf.find(&l)?.clone();
                let r_root = uf.find(&r)?.clone();
                let root = uf.union(&l, &r).unwrap();
                match (map.remove(&l_root), map.remove(&r_root)) {
                    (Some(lval), Some(rval)) => {
                        constraints.push_back(Constraint {
                            type_l: lval.clone(),
                            type_r: rval,
                            expr_l: format!("val({})", l),
                            expr_r: format!("val({})", r),
                        });
                        Some(lval)
                    }
                    (Some(val), None) | (None, Some(val)) => Some(val),
                    (None, None) => None,
                }
                .and_then(|v| map.insert(root.clone(), v));
            }
            (Type::Var(var), val) | (val, Type::Var(var)) if !val.contains_var(&var) => {
                match map.insert(var, val.clone()) {
                    None => (),
                    Some(old_val) => {
                        constraints.push_back(Constraint {
                            type_l: old_val,
                            type_r: val,
                            expr_l: constraint.expr_l,
                            expr_r: constraint.expr_r,
                        });
                    }
                }
            }
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

fn get_type(mut tau: Type, mut uf: UnionFind<Variable>, mut map: HashMap<Variable, Type>) -> Type {
    loop {
        let vars = tau.get_free_vars();
        if vars.is_empty() {
            return tau;
        }
        let x = vars.first().unwrap();
        let r_opt = uf.find(x);
        if let Ok(r) = r_opt
            && x != r
        {
            tau = tau.substitute(x.clone(), Type::Var(r.clone()));
            continue;
        }
        match r_opt.ok().and_then(|r| map.remove(r)) {
            Some(t_x) => tau = tau.substitute(x.clone(), t_x),
            None => tau = tau.add_one_quantifier(x.clone()),
        }
    }
}
