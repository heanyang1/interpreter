use std::collections::HashMap;

use crate::ast::{Expr, Type, Variable};

fn fresh(v: &Variable) -> Variable {
    Variable::from(format!("{}_", v.0))
}

fn add_depth<I>(depth: HashMap<Variable, u32>, it: I) -> HashMap<Variable, u32>
where
    I: IntoIterator<Item = Variable>,
{
    let mut depth = depth;
    for (_, v) in depth.iter_mut() {
        *v += 1;
    }
    depth.extend(it.into_iter().map(|v| (v.clone(), 0_u32)));
    depth
}

/// Trivial cases: iterate through an expression's children
macro_rules! trivial {
    ($namespace:tt, $ty:tt, $rename:ident, $method:ident; $($prefix:ident),*; $($i:ident),+; $($suffix:ident),*) => {
        $namespace::$ty {
            $($prefix,)*
            // TODO: remove the extra clone for the last element
            $($i: Box::new($i.$method($rename.clone())),)+
            $($suffix,)*
        }
    };
}

/// Check if two expressions are alpha equivalent
macro_rules! equiv {
    ($($term1:ident == $term2:ident),*; $($nonterm1:ident == $nonterm2:ident),*) => {
        $($term1 == $term2 &&)*
        $(aux(*$nonterm1, *$nonterm2) &&)*
        true
    }
}

pub trait Symbol: Sized {
    fn to_debruijn_map(self, depth: HashMap<Variable, u32>) -> Self;
    fn to_debruijn(self) -> Self {
        self.to_debruijn_map(HashMap::new())
    }
    #[allow(unused)]
    fn alpha_equiv(e1: Self, e2: Self) -> bool;
    fn substitute_map(self, rename: HashMap<Variable, Self>) -> Self;
    fn substitute(self, s: Variable, e: Self) -> Self {
        self.substitute_map(HashMap::from([(s, e)]))
    }
}

impl Symbol for Type {
    fn to_debruijn_map(self, depth: HashMap<Variable, u32>) -> Self {
        match self {
            Type::Num
            | Type::Bool
            | Type::Unit
            | Type::Product { .. }
            | Type::Sum { .. } => self,
            Type::Var(v) => Type::Var(match depth.get(&v) {
                None => v, // v is a free variable
                Some(depth) => Variable::from(*depth),
            }),
            Type::Forall { a, tau } => {
                let depth = add_depth(depth, [a]);
                Type::Forall {
                    a: Variable::from("_"),
                    tau: Box::new(tau.to_debruijn_map(depth)),
                }
            }
            Type::Fn { arg, ret } => trivial!(Type, Fn, depth, to_debruijn_map;; arg, ret;),
            _ => todo!(),
        }
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
                ) => equiv!(; l1 == l2, r1 == r2),
                (Type::Var(v1), Type::Var(v2)) => v1 == v2,
                (Type::Forall { a: a1, tau: t1 }, Type::Forall { a: a2, tau: t2 }) => {
                    equiv!(a1 == a2; t1 == t2)
                }
                _ => false,
            }
        }
        aux(e1.to_debruijn(), e2.to_debruijn())
    }

    fn substitute_map(self, rename: HashMap<Variable, Type>) -> Type {
        match self {
            Type::Num | Type::Bool | Type::Unit => self,
            Type::Fn { arg, ret } => trivial!(Type, Fn, rename, substitute_map;; arg, ret;),
            Type::Product { left, right } => {
                trivial!(Type, Product, rename, substitute_map;; left, right;)
            }
            Type::Sum { left, right } => trivial!(Type, Sum, rename, substitute_map;; left, right;),
            Type::Var(v) => match rename.get(&v) {
                Some(val) => val.clone(),
                None => Type::Var(v),
            },
            Type::Forall { a, tau } => {
                let mut rename = rename;
                let new_a = fresh(&a);
                rename.insert(a, Type::Var(new_a.clone()));
                Type::Forall {
                    a: new_a,
                    tau: Box::new(tau.substitute_map(rename)),
                }
            }
            _ => todo!(),
        }
    }
}

impl Symbol for Expr {
    fn to_debruijn_map(self, depth: HashMap<Variable, u32>) -> Self {
        match self {
            Expr::Num(_) | Expr::True | Expr::False | Expr::Unit => self.clone(),
            Expr::Var(v) => Expr::Var(match depth.get(&v) {
                None => v.clone(), // v is a free variable
                Some(depth) => Variable::from(*depth),
            }),
            Expr::Lam { x, tau, e } => {
                let depth = add_depth(depth, [x.clone()]);
                Expr::Lam {
                    x: Variable::from("_"),
                    tau: Box::new(tau.to_debruijn_map(depth.clone())),
                    e: Box::new(e.to_debruijn_map(depth)),
                }
            }
            Expr::App { lam, arg } => trivial!(Expr, App, depth, to_debruijn_map;; lam, arg;),
            Expr::Addop { binop, left, right } => {
                trivial!(Expr, Addop, depth, to_debruijn_map; binop; left, right;)
            }
            Expr::Mulop { binop, left, right } => {
                trivial!(Expr, Mulop, depth, to_debruijn_map; binop; left, right;)
            }
            Expr::Relop { relop, left, right } => {
                trivial!(Expr, Relop, depth, to_debruijn_map; relop; left, right;)
            }
            Expr::If { cond, then_, else_ } => {
                trivial!(Expr, If, depth, to_debruijn_map;; cond, then_, else_;)
            }
            Expr::And { left, right } => trivial!(Expr, And, depth, to_debruijn_map;; left, right;),
            Expr::Or { left, right } => trivial!(Expr, Or, depth, to_debruijn_map;; left, right;),
            Expr::Pair { left, right } => {
                trivial!(Expr, Pair, depth, to_debruijn_map;; left, right;)
            }
            Expr::Project { e, d } => trivial!(Expr, Project, depth, to_debruijn_map;; e; d),
            Expr::Inject { e, d, tau } => {
                trivial!(Expr, Inject, depth, to_debruijn_map;; e; d, tau)
            }
            Expr::Case {
                e,
                xleft,
                eleft,
                xright,
                eright,
            } => {
                let depth_new = add_depth(depth.clone(), [xleft, xright]);
                Expr::Case {
                    e: Box::new(e.to_debruijn_map(depth)),
                    xleft: Variable::from("_"),
                    eleft: Box::new(eleft.to_debruijn_map(depth_new.clone())),
                    xright: Variable::from("_"),
                    eright: Box::new(eright.to_debruijn_map(depth_new)),
                }
            }
            Expr::Fix { x, tau, e } => {
                let depth = add_depth(depth, [x]);
                Expr::Fix {
                    x: Variable::from("_"),
                    tau: Box::new(tau.to_debruijn_map(depth.clone())),
                    e: Box::new(e.to_debruijn_map(depth)),
                }
            }
            Expr::TyApp { e, tau } => Expr::TyApp {
                e: Box::new(e.to_debruijn_map(depth.clone())),
                tau: Box::new(tau.to_debruijn_map(depth)),
            },
            Expr::TyLam { a, e } => {
                let depth = add_depth(depth, [a]);
                Expr::TyLam {
                    a: Variable::from("_"),
                    e: Box::new(e.to_debruijn_map(depth)),
                }
            }
            _ => todo!("to_debruijn: {self:?}"),
        }
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
                ) => equiv!(b1 == b2; l1 == l2, r1 == r2),
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
                ) => equiv!(b1 == b2; l1 == l2, r1 == r2),
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
                ) => equiv!(;c1 == c2, t1 == t2, e1 == e2),
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
                ) => equiv!(b1 == b2; l1 == l2, r1 == r2),
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
                    equiv!(; l1 == l2, r1 == r2)
                }
                (Expr::Project { e: e1, d: d1 }, Expr::Project { e: e2, d: d2 }) => {
                    equiv!(d1 == d2; e1 == e2)
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
                ) => equiv!(d1 == d2, t1 == t2; e1 == e2),
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
                ) => equiv!(xl1 == xl2, xr1 == xr2; e1 == e2, el1 == el2, er1 == er2),
                (
                    Expr::Lam {
                        x: x1,
                        tau: t1,
                        e: e1,
                    },
                    Expr::Lam {
                        x: x2,
                        tau: t2,
                        e: e2,
                    },
                )
                | (
                    Expr::Fix {
                        x: x1,
                        tau: t1,
                        e: e1,
                    },
                    Expr::Fix {
                        x: x2,
                        tau: t2,
                        e: e2,
                    },
                ) => equiv!(t1 == t2, x1 == x2; e1 == e2),
                (Expr::True, Expr::True)
                | (Expr::False, Expr::False)
                | (Expr::Unit, Expr::Unit) => true,
                (Expr::TyLam { a: a1, e: e1 }, Expr::TyLam { a: a2, e: e2 }) => {
                    equiv!(a1 == a2; e1 == e2)
                }
                (Expr::TyApp { e: e1, tau: t1 }, Expr::TyApp { e: e2, tau: t2 }) => {
                    equiv!(t1 == t2; e1 == e2)
                }
                _ => false,
            }
        }
        aux(e1.to_debruijn(), e2.to_debruijn())
    }
    fn substitute_map(self, rename: HashMap<Variable, Expr>) -> Expr {
        match self {
            Expr::Num(_) | Expr::True | Expr::False | Expr::Unit => self.clone(),
            Expr::Addop { binop, left, right } => {
                trivial!(Expr, Addop, rename, substitute_map; binop; left, right;)
            }
            Expr::Mulop { binop, left, right } => {
                trivial!(Expr, Mulop, rename, substitute_map; binop; left, right;)
            }
            Expr::If { cond, then_, else_ } => {
                trivial!(Expr, If, rename, substitute_map;; cond, then_, else_;)
            }
            Expr::Relop { relop, left, right } => {
                trivial!(Expr, Relop, rename, substitute_map; relop; left, right;)
            }
            Expr::And { left, right } => trivial!(Expr, And, rename, substitute_map;; left, right;),
            Expr::Or { left, right } => trivial!(Expr, Or, rename, substitute_map;; left, right;),
            Expr::Lam { x, tau, e } => {
                let mut rename = rename;
                let new_x = fresh(&x);
                rename.insert(x, Expr::Var(new_x.clone()));
                Expr::Lam {
                    x: new_x,
                    tau,
                    e: Box::new(e.substitute_map(rename)),
                }
            }
            Expr::App { lam, arg } => trivial!(Expr, App, rename, substitute_map;; lam, arg;),
            Expr::Var(v) => match rename.get(&v.clone()) {
                Some(val) => val.clone(),
                None => Expr::Var(v),
            },
            Expr::Pair { left, right } => {
                trivial!(Expr, Pair, rename, substitute_map;; left, right;)
            }
            Expr::Project { e, d } => trivial!(Expr, Project, rename, substitute_map;; e; d),
            Expr::Inject { e, d, tau } => {
                trivial!(Expr, Inject, rename, substitute_map;; e; d, tau)
            }
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
                    e: Box::new(e.substitute_map(rename.clone())),
                    xleft: new_xleft,
                    eleft: Box::new(eleft.substitute_map(rename.clone())),
                    xright: new_xright,
                    eright: Box::new(eright.substitute_map(rename)),
                }
            }
            Expr::Fix { x, tau, e } => {
                let mut rename = rename;
                let new_x = fresh(&x);
                rename.insert(x, Expr::Var(new_x.clone()));
                Expr::Fix {
                    x: new_x,
                    tau,
                    e: Box::new(e.substitute_map(rename)),
                }
            }
            Expr::TyLam { a, e } => {
                let mut rename = rename;
                let new_a = fresh(&a);
                rename.insert(a, Expr::Var(new_a.clone()));
                Expr::TyLam {
                    a: new_a,
                    e: Box::new(e.substitute_map(rename)),
                }
            }
            Expr::TyApp { e, tau } => trivial!(Expr, TyApp, rename, substitute_map;; e; tau),
            _ => todo!(),
        }
    }
}
