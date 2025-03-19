use std::collections::HashMap;

use crate::ast::{Expr, Type, Variable};

fn fresh(v: &Variable) -> Variable {
    Variable::from(format!("{}_", v.0))
}

/// Trivial cases: iterate through or check the equality of an expression's children
macro_rules! trivial {
    ($namespace:tt, $ty:tt, $rename:ident; $($prefix:ident),*; $($i:ident),+; $($suffix:ident),*) => {
        $namespace::$ty {
            $($prefix,)*
            // TODO: remove the extra clone for the last element
            $($i: Box::new(aux($rename.clone(), *$i)),)+
            $($suffix,)*
        }
    };

    ($($term1:ident == $term2:ident),*; $($nonterm1:ident == $nonterm2:ident),*) => {
        $($term1 == $term2 &&)*
        $(aux(*$nonterm1, *$nonterm2) &&)*
        true
    }
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
                Type::Num
                | Type::Bool
                | Type::Unit
                | Type::Fn { .. }
                | Type::Product { .. }
                | Type::Sum { .. } => t,
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
                (Type::Fn { arg: l1, ret: r1 }, Type::Fn { arg: l2, ret: r2 })
                | (
                    Type::Product {
                        left: l1,
                        right: r1,
                    },
                    Type::Product {
                        left: l2,
                        right: r2,
                    },
                )
                | (
                    Type::Sum {
                        left: l1,
                        right: r1,
                    },
                    Type::Sum {
                        left: l2,
                        right: r2,
                    },
                ) => trivial!(; l1==l2, r1==r2),
                _ => false,
            }
        }
        aux(e1.to_debruijn(), e2.to_debruijn())
    }

    fn substitute(&self, _s: Variable, _e: Self) -> Self {
        fn aux(rename: HashMap<Variable, Type>, this: Type) -> Type {
            match this {
                Type::Num | Type::Bool | Type::Unit => this,
                Type::Fn { arg, ret } => trivial!(Type, Fn, rename;; arg, ret;),
                Type::Product { left, right } => trivial!(Type, Product, rename;; left, right;),
                Type::Sum { left, right } => trivial!(Type, Sum, rename;; left, right;),
                _ => todo!(),
            }
        }
        aux(HashMap::new(), self.clone())
    }
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
                Expr::App { lam, arg } => trivial!(Expr, App, depth;; lam, arg;),
                Expr::Addop { binop, left, right } => {
                    trivial!(Expr, Addop, depth; binop; left, right;)
                }
                Expr::Mulop { binop, left, right } => {
                    trivial!(Expr, Mulop, depth; binop; left, right;)
                }
                Expr::Relop { relop, left, right } => {
                    trivial!(Expr, Relop, depth; relop; left, right;)
                }
                Expr::If { cond, then_, else_ } => trivial!(Expr, If, depth;; cond, then_, else_;),
                Expr::And { left, right } => trivial!(Expr, And, depth;; left, right;),
                Expr::Or { left, right } => trivial!(Expr, Or, depth;; left, right;),
                Expr::Pair { left, right } => trivial!(Expr, Pair, depth;; left, right;),
                Expr::Project { e, d } => trivial!(Expr, Project, depth;; e; d),
                Expr::Inject { e, d, tau } => trivial!(Expr, Inject, depth;; e; d, tau),
                Expr::Case {
                    e,
                    xleft,
                    eleft,
                    xright,
                    eright,
                } => {
                    let mut depth_new = depth.clone();
                    for (_, v) in depth_new.iter_mut() {
                        *v += 1;
                    }
                    depth_new.extend([
                        (String::from(xleft.clone()).to_string(), 0),
                        (String::from(xright.clone()).to_string(), 0),
                    ]);
                    Expr::Case {
                        e: Box::new(aux(depth, *e)),
                        xleft: Variable::from("_"),
                        eleft: Box::new(aux(depth_new.clone(), *eleft)),
                        xright: Variable::from("_"),
                        eright: Box::new(aux(depth_new, *eright)),
                    }
                }
                Expr::Fix { x, tau, e } => {
                    let mut depth = depth;
                    for (_, v) in depth.iter_mut() {
                        *v += 1;
                    }
                    depth.insert(String::from(x.clone()).to_string(), 0);
                    Expr::Fix {
                        x: Variable::from("_"),
                        tau: Box::new(tau.to_debruijn()),
                        e: Box::new(aux(depth, *e)),
                    }
                }
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
                ) => trivial!(b1 == b2; l1 == l2, r1 == r2),
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
                ) => trivial!(b1 == b2; l1 == l2, r1 == r2),
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
                ) => trivial!(;c1 == c2, t1 == t2, e1 == e2),
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
                ) => trivial!(b1 == b2; l1 == l2, r1 == r2),
                (
                    Expr::And {
                        left: l1,
                        right: r1,
                    },
                    Expr::And {
                        left: l2,
                        right: r2,
                    },
                )
                | (
                    Expr::Or {
                        left: l1,
                        right: r1,
                    },
                    Expr::Or {
                        left: l2,
                        right: r2,
                    },
                )
                | (
                    Expr::Pair {
                        left: l1,
                        right: r1,
                    },
                    Expr::Pair {
                        left: l2,
                        right: r2,
                    },
                )
                | (Expr::App { lam: l1, arg: r1 }, Expr::App { lam: l2, arg: r2 }) => {
                    trivial!(; l1 == l2, r1 == r2)
                }
                (Expr::Project { e: e1, d: d1 }, Expr::Project { e: e2, d: d2 }) => {
                    trivial!(d1 == d2; e1 == e2)
                }
                (
                    Expr::Inject {
                        e: e1,
                        d: d1,
                        tau: t1,
                    },
                    Expr::Inject {
                        e: e2,
                        d: d2,
                        tau: t2,
                    },
                ) => trivial!(d1 == d2, t1 == t2; e1 == e2),
                (
                    Expr::Case {
                        e: e1,
                        xleft: xl1,
                        eleft: el1,
                        xright: xr1,
                        eright: er1,
                    },
                    Expr::Case {
                        e: e2,
                        xleft: xl2,
                        eleft: el2,
                        xright: xr2,
                        eright: er2,
                    },
                ) => trivial!(xl1 == xl2, xr1 == xr2; e1 == e2, el1 == el2, er1 == er2),
                (Expr::Lam { e: e1, .. }, Expr::Lam { e: e2, .. }) => aux(*e1, *e2),
                (Expr::True, Expr::True)
                | (Expr::False, Expr::False)
                | (Expr::Unit, Expr::Unit) => true,
                (
                    Expr::Fix {
                        x: x1,
                        tau: tau1,
                        e: e1,
                    },
                    Expr::Fix {
                        x: x2,
                        tau: tau2,
                        e: e2,
                    },
                ) => trivial!(x1 == x2, tau1 == tau2; e1 == e2),
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
                    trivial!(Expr, Addop, rename; binop; left, right;)
                }
                Expr::Mulop { binop, left, right } => {
                    trivial!(Expr, Mulop, rename; binop; left, right;)
                }
                Expr::If { cond, then_, else_ } => {
                    trivial!(Expr, If, rename;; cond, then_, else_;)
                }
                Expr::Relop { relop, left, right } => {
                    trivial!(Expr, Relop, rename; relop; left, right;)
                }
                Expr::And { left, right } => trivial!(Expr, And, rename;; left, right;),
                Expr::Or { left, right } => trivial!(Expr, Or, rename;; left, right;),
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
                Expr::App { lam, arg } => trivial!(Expr, App, rename;; lam, arg;),
                Expr::Var(v) => match rename.get(&v.clone()) {
                    Some(val) => val.clone(),
                    None => Expr::Var(v),
                },
                Expr::Pair { left, right } => trivial!(Expr, Pair, rename;; left, right;),
                Expr::Project { e, d } => trivial!(Expr, Project, rename;; e; d),
                Expr::Inject { e, d, tau } => trivial!(Expr, Inject, rename;; e; d, tau),
                Expr::Case {
                    e,
                    xleft,
                    eleft,
                    xright,
                    eright,
                } => {
                    let mut rename = rename;
                    let new_xleft = fresh(&xleft);
                    let new_xright = fresh(&xright);
                    rename.extend([
                        (xleft.clone(), Expr::Var(new_xleft.clone())),
                        (xright.clone(), Expr::Var(new_xright.clone())),
                    ]);
                    Expr::Case {
                        e: Box::new(aux(rename.clone(), *e)),
                        xleft: new_xleft,
                        eleft: Box::new(aux(rename.clone(), *eleft)),
                        xright: new_xright,
                        eright: Box::new(aux(rename, *eright)),
                    }
                }
                Expr::Fix { x, tau, e } => {
                    let mut rename = rename;
                    let new_x = fresh(&x);
                    rename.insert(x, Expr::Var(new_x.clone()));
                    Expr::Fix {
                        x: new_x,
                        tau,
                        e: Box::new(aux(rename, *e)),
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
