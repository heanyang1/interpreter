use std::collections::HashMap;

use crate::ast::{Expr, Type, Variable};

fn fresh(v: &Variable) -> Variable {
    Variable::from(format!("{}_", v.0))
}

pub trait Symbol {
    fn to_debruijn(&self) -> Self;
    #[allow(unused)]
    fn alpha_equiv(e1: Self, e2: Self) -> bool;
    fn substitute(&self, s: Variable, e: Self) -> Self;
}

impl Symbol for Type {
    fn to_debruijn(&self) -> Self {
        fn aux(_depth: HashMap<String, u32>, t: Type) -> Type {
            match t {
                Type::Num | Type::Bool | Type::Unit | Type::Fn { .. } => t,
                _ => todo!(),
            }
        }
        aux(HashMap::new(), self.clone())
    }

    fn alpha_equiv(e1: Self, e2: Self) -> bool {
        fn aux(e1: Type, e2: Type) -> bool {
            match (e1, e2) {
                (Type::Num, Type::Num) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {
                    true
                }
                (Type::Fn { arg: a1, ret: r1 }, Type::Fn { arg: a2, ret: r2 }) => {
                    aux(*a1, *a2) && aux(*r1, *r2)
                }
                _ => false,
            }
        }
        aux(e1.to_debruijn(), e2.to_debruijn())
    }

    fn substitute(&self, _s: Variable, _e: Self) -> Self {
        fn aux(rename: HashMap<Variable, Type>, this: Type) -> Type {
            match this {
                Type::Num | Type::Bool | Type::Unit => this,
                Type::Fn { arg, ret } => Type::Fn {
                    arg: Box::new(aux(rename.clone(), *arg)),
                    ret: Box::new(aux(rename.clone(), *ret)),
                },
                _ => todo!(),
            }
        }
        aux(HashMap::new(), self.clone())
    }
}

macro_rules! binop_substitute {
    ($ty:tt, $binop:ident, $left:ident, $right:ident, $rename:ident) => {
        Expr::$ty {
            $binop,
            $left: Box::new(aux($rename.clone(), *$left)),
            $right: Box::new(aux($rename.clone(), *$right)),
        }
    };
}

impl Symbol for Expr {
    fn to_debruijn(&self) -> Self {
        fn aux(depth: HashMap<String, u32>, e: Expr) -> Expr {
            match e {
                Expr::Num(_) | Expr::True | Expr::False | Expr::Unit => e.clone(),
                Expr::Var(v) => Expr::Var(
                    if let Some(val) = depth.get(String::from(v.clone()).as_str()) {
                        Variable::from(val)
                    } else {
                        // v is a free variable
                        v
                    },
                ),
                Expr::Lam { x, tau, e } => {
                    let mut depth = depth;
                    for (_, v) in depth.iter_mut() {
                        *v += 1;
                    }
                    depth.insert(String::from(x.clone()).to_string(), 0);
                    Expr::Lam {
                        x: Variable::from("_"),
                        tau: Box::new(tau.to_debruijn()),
                        e: Box::new(aux(depth, *e)),
                    }
                }
                Expr::App { lam, arg } => Expr::App {
                    lam: Box::new(aux(depth.clone(), *lam)),
                    arg: Box::new(aux(depth.clone(), *arg)),
                },
                Expr::Addop { binop, left, right } => {
                    binop_substitute!(Addop, binop, left, right, depth)
                }
                Expr::Mulop { binop, left, right } => {
                    binop_substitute!(Mulop, binop, left, right, depth)
                }
                Expr::Relop { relop, left, right } => {
                    binop_substitute!(Relop, relop, left, right, depth)
                }
                Expr::If { cond, then_, else_ } => Expr::If {
                    cond: Box::new(aux(depth.clone(), *cond)),
                    then_: Box::new(aux(depth.clone(), *then_)),
                    else_: Box::new(aux(depth.clone(), *else_)),
                },
                Expr::And { left, right } => Expr::And {
                    left: Box::new(aux(depth.clone(), *left)),
                    right: Box::new(aux(depth.clone(), *right)),
                },
                Expr::Or { left, right } => Expr::Or {
                    left: Box::new(aux(depth.clone(), *left)),
                    right: Box::new(aux(depth.clone(), *right)),
                },
                _ => todo!("to_debruijn: {e:?}"),
            }
        }
        aux(HashMap::new(), self.clone())
    }

    fn alpha_equiv(e1: Self, e2: Self) -> bool {
        fn aux(e1: Expr, e2: Expr) -> bool {
            match (e1, e2) {
                (Expr::Num(n1), Expr::Num(n2)) => n1 == n2,
                (Expr::Var(v1), Expr::Var(v2)) => v1 == v2,
                (
                    Expr::Addop {
                        binop: b1,
                        left: l1,
                        right: r1,
                    },
                    Expr::Addop {
                        binop: b2,
                        left: l2,
                        right: r2,
                    },
                ) => b1 == b2 && aux(*l1, *l2) && aux(*r1, *r2),
                (
                    Expr::Mulop {
                        binop: b1,
                        left: l1,
                        right: r1,
                    },
                    Expr::Mulop {
                        binop: b2,
                        left: l2,
                        right: r2,
                    },
                ) => b1 == b2 && aux(*l1, *l2) && aux(*r1, *r2),
                (
                    Expr::If {
                        cond: c1,
                        then_: t1,
                        else_: e1,
                    },
                    Expr::If {
                        cond: c2,
                        then_: t2,
                        else_: e2,
                    },
                ) => aux(*c1, *c2) && aux(*t1, *t2) && aux(*e1, *e2),
                (
                    Expr::Relop {
                        relop: b1,
                        left: l1,
                        right: r1,
                    },
                    Expr::Relop {
                        relop: b2,
                        left: l2,
                        right: r2,
                    },
                ) => b1 == b2 && aux(*l1, *l2) && aux(*r1, *r2),
                (
                    Expr::And {
                        left: l1,
                        right: r1,
                    },
                    Expr::And {
                        left: l2,
                        right: r2,
                    },
                ) => aux(*l1, *l2) && aux(*r1, *r2),
                (
                    Expr::Or {
                        left: l1,
                        right: r1,
                    },
                    Expr::Or {
                        left: l2,
                        right: r2,
                    },
                ) => aux(*l1, *l2) && aux(*r1, *r2),
                (Expr::Lam { e: e1, .. }, Expr::Lam { e: e2, .. }) => aux(*e1, *e2),
                (Expr::App { lam: l1, arg: a1 }, Expr::App { lam: l2, arg: a2 }) => {
                    aux(*l1, *l2) && aux(*a1, *a2)
                }
                (Expr::True, Expr::True)
                | (Expr::False, Expr::False)
                | (Expr::Unit, Expr::Unit) => true,
                _ => false,
            }
        }
        aux(e1.to_debruijn(), e2.to_debruijn())
    }
    fn substitute(&self, s: Variable, e: Self) -> Self {
        fn aux(rename: HashMap<Variable, Expr>, this: Expr) -> Expr {
            match this {
                Expr::Num(_) | Expr::True | Expr::False | Expr::Unit => this.clone(),
                Expr::Addop { binop, left, right } => {
                    binop_substitute!(Addop, binop, left, right, rename)
                }
                Expr::Mulop { binop, left, right } => {
                    binop_substitute!(Mulop, binop, left, right, rename)
                }
                Expr::If { cond, then_, else_ } => Expr::If {
                    cond: Box::new(aux(rename.clone(), *cond)),
                    then_: Box::new(aux(rename.clone(), *then_)),
                    else_: Box::new(aux(rename.clone(), *else_)),
                },
                Expr::Relop { relop, left, right } => {
                    binop_substitute!(Relop, relop, left, right, rename)
                }
                Expr::And { left, right } => Expr::And {
                    left: Box::new(aux(rename.clone(), *left)),
                    right: Box::new(aux(rename.clone(), *right)),
                },
                Expr::Or { left, right } => Expr::Or {
                    left: Box::new(aux(rename.clone(), *left)),
                    right: Box::new(aux(rename.clone(), *right)),
                },
                Expr::Lam { x, tau, e } => {
                    let mut rename = rename;
                    let new_x = fresh(&x);
                    rename.insert(x, Expr::Var(new_x.clone()));
                    Expr::Lam {
                        x: new_x,
                        tau,
                        e: Box::new(aux(rename, *e)),
                    }
                }
                Expr::App { lam, arg } => Expr::App {
                    lam: Box::new(aux(rename.clone(), *lam)),
                    arg: Box::new(aux(rename.clone(), *arg)),
                },
                Expr::Var(v) => {
                    if let Some(val) = rename.get(&v.clone()) {
                        val.clone()
                    } else {
                        Expr::Var(v)
                    }
                }
                _ => todo!(),
            }
        }
        let mut rename = HashMap::new();
        rename.insert(s, e);
        aux(rename, self.clone())
    }
}
