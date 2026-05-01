use std::{collections::HashMap, fmt::Display};

use crate::ast::{Expr, Type, Variable};

pub struct Printer(pub &'static str);

impl Printer {
    pub fn print_it<T: Display, It: Iterator<Item = T>>(&self, v: It) -> String {
        let elems: Vec<String> = v.map(|x| format!("{}", x)).collect();
        format!("[{}]", elems.join(self.0))
    }
    pub fn print_map<K: Display, V: Display>(&self, m: &HashMap<K, V>) -> String {
        self.print_it(m.iter().map(|(x, y)| format!("{x}: {y}")))
    }
}

fn fresh(v: &Variable) -> Variable {
    Variable::from(format!("{}_", v.0))
}

fn add_depth(depth: &mut HashMap<Variable, usize>, it: impl IntoIterator<Item = Variable>) {
    for (_, v) in depth.iter_mut() {
        *v += 1;
    }
    depth.extend(it.into_iter().map(|v| (v, 0)));
}

/// Trivial cases: iterate through an expression's children
macro_rules! trivial {
    ($namespace:tt, $ty:tt, $rename:ident, $method:ident; $($prefix:ident),*; $($i:ident),+; $($suffix:ident),*) => {
        $namespace::$ty {
            $($prefix,)*
            $($i: Box::new($i.$method($rename.clone())),)+
            $($suffix,)*
        }
    };
}

pub trait Symbol: Sized {
    fn to_debruijn_map(self, depth: HashMap<Variable, usize>) -> Self;
    fn to_debruijn(self) -> Self {
        self.to_debruijn_map(HashMap::new())
    }
    fn alpha_equiv(e1: Self, e2: Self) -> bool;
    fn substitute_map(self, rename: HashMap<Variable, Self>) -> Self;
    fn substitute(self, s: Variable, e: Self) -> Self {
        self.substitute_map(HashMap::from([(s, e)]))
    }
}

impl Symbol for Type {
    fn to_debruijn_map(self, mut depth: HashMap<Variable, usize>) -> Self {
        match self {
            Type::Num | Type::Bool | Type::Unit => self,
            Type::Product { left, right } => {
                trivial!(Type, Product, depth, to_debruijn_map;; left, right;)
            }
            Type::Sum { left, right } => trivial!(Type, Sum, depth, to_debruijn_map;; left, right;),
            Type::Var(v) => Type::Var(match depth.get(&v) {
                None => v, // v is a free variable
                Some(depth) => Variable::from(depth.to_string()),
            }),
            Type::Forall { a, tau } => {
                add_depth(&mut depth, [a]);
                Type::Forall {
                    a: Variable::from("_"),
                    tau: Box::new(tau.to_debruijn_map(depth)),
                }
            }
            Type::Rec { a, tau } => {
                add_depth(&mut depth, [a]);
                Type::Rec {
                    a: Variable::from("_"),
                    tau: Box::new(tau.to_debruijn_map(depth)),
                }
            }
            Type::Fn { arg, ret } => trivial!(Type, Fn, depth, to_debruijn_map;; arg, ret;),
            Type::Exists { a, tau } => {
                add_depth(&mut depth, [a]);
                Type::Exists {
                    a: Variable::from("_"),
                    tau: Box::new(tau.to_debruijn_map(depth)),
                }
            }
        }
    }

    fn alpha_equiv(e1: Self, e2: Self) -> bool {
        e1.to_debruijn() == e2.to_debruijn()
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
            Type::Rec { a, tau } => {
                let mut rename = rename;
                let new_a = fresh(&a);
                rename.insert(a, Type::Var(new_a.clone()));
                Type::Rec {
                    a: new_a,
                    tau: Box::new(tau.substitute_map(rename)),
                }
            }
            Type::Exists { a, tau } => {
                let mut rename = rename;
                let new_a = fresh(&a);
                rename.insert(a, Type::Var(new_a.clone()));
                Type::Exists {
                    a: new_a,
                    tau: Box::new(tau.substitute_map(rename)),
                }
            }
        }
    }
}

impl Symbol for Expr {
    fn to_debruijn_map(self, mut depth: HashMap<Variable, usize>) -> Self {
        match self {
            Expr::DeBruijn(_) => unreachable!(),
            Expr::Num(_) | Expr::True | Expr::False | Expr::Unit => self.clone(),
            Expr::Var(v) => match depth.get(&v) {
                None => Self::Var(v.clone()), // v is a free variable
                Some(depth) => Self::DeBruijn(*depth),
            },
            Expr::Lam { x, e } => {
                add_depth(&mut depth, [x.clone()]);
                Expr::Lam {
                    x: Variable::from("_"),
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
            Expr::Inject { e, d } => {
                trivial!(Expr, Inject, depth, to_debruijn_map;; e; d)
            }
            Expr::Case {
                e,
                xleft,
                eleft,
                xright,
                eright,
            } => {
                let original_depth = depth.clone();
                add_depth(&mut depth, [xleft.clone(), xright.clone()]);
                Expr::Case {
                    e: Box::new(e.to_debruijn_map(original_depth)),
                    xleft: Variable::from("_"),
                    eleft: Box::new(eleft.to_debruijn_map(depth.clone())),
                    xright: Variable::from("_"),
                    eright: Box::new(eright.to_debruijn_map(depth)),
                }
            }
            Expr::Fix { x, e } => {
                add_depth(&mut depth, [x.clone()]);
                Expr::Fix {
                    x: Variable::from("_"),
                    e: Box::new(e.to_debruijn_map(depth)),
                }
            }
            Expr::TyApp { e, tau } => trivial!(Expr, TyApp, depth, to_debruijn_map;; e, tau;),
            Expr::Fold { e, tau } => trivial!(Expr, Fold, depth, to_debruijn_map;; e, tau;),
            Expr::TyLam { a, e } => {
                add_depth(&mut depth, [a.clone()]);
                Expr::TyLam {
                    a: Variable::from("_"),
                    e: Box::new(e.to_debruijn_map(depth)),
                }
            }
            Expr::Unfold(e) => Expr::Unfold(Box::new(e.to_debruijn_map(depth))),
            Expr::Export {
                e,
                tau_adt,
                tau_mod,
            } => trivial!(Expr, Export, depth, to_debruijn_map;; e, tau_adt, tau_mod;),
            Expr::Import {
                x,
                a,
                e_mod,
                e_body,
            } => {
                add_depth(&mut depth, [x.clone(), a.clone()]);
                Expr::Import {
                    x: Variable::from("_"),
                    a: Variable::from("_"),
                    e_mod: Box::new(e_mod.to_debruijn_map(depth.clone())),
                    e_body: Box::new(e_body.to_debruijn_map(depth)),
                }
            }
        }
    }

    fn alpha_equiv(e1: Self, e2: Self) -> bool {
        e1.to_debruijn() == e2.to_debruijn()
    }

    fn substitute_map(self, rename: HashMap<Variable, Expr>) -> Expr {
        match self {
            Expr::Num(_) | Expr::True | Expr::False | Expr::Unit | Expr::DeBruijn(_) => {
                self.clone()
            }
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
            Expr::Lam { x, e } => {
                let mut rename = rename;
                let new_x = fresh(&x);
                rename.insert(x, Expr::Var(new_x.clone()));
                Expr::Lam {
                    x: new_x,
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
            Expr::Inject { e, d } => {
                trivial!(Expr, Inject, rename, substitute_map;; e; d)
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
            Expr::Fix { x, e } => {
                let mut rename = rename;
                let new_x = fresh(&x);
                rename.insert(x, Expr::Var(new_x.clone()));
                Expr::Fix {
                    x: new_x,
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
            Expr::Fold { e, tau } => trivial!(Expr, Fold, rename, substitute_map;; e; tau),
            Expr::Unfold(e) => Expr::Unfold(Box::new(e.substitute_map(rename))),
            Expr::Export {
                e,
                tau_adt,
                tau_mod,
            } => trivial!(Expr, Export, rename, substitute_map;; e; tau_adt, tau_mod),
            Expr::Import {
                x,
                a,
                e_mod,
                e_body,
            } => {
                let mut rename = rename;
                let new_x = fresh(&x);
                let new_a = fresh(&a);
                rename.extend([
                    (x.clone(), Expr::Var(new_x.clone())),
                    (a.clone(), Expr::Var(new_a.clone())),
                ]);
                Expr::Import {
                    x: new_x,
                    a: new_a,
                    e_mod: Box::new(e_mod.substitute_map(rename.clone())),
                    e_body: Box::new(e_body.substitute_map(rename)),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Type};

    #[test]
    fn test_expr_vec_print_empty() {
        let v: Vec<Expr> = vec![];
        let s = Printer("").print_it(v.iter());
        assert_eq!(s, "[]");
    }

    #[test]
    fn test_expr_vec_print_single() {
        let v = vec![Expr::Num(42)];
        let s = Printer("").print_it(v.iter());
        assert_eq!(s, "[42]");
    }

    #[test]
    fn test_expr_vec_print_multiple() {
        let v = vec![Expr::Num(1), Expr::Num(2), Expr::Num(3)];
        let s = Printer(", ").print_it(v.iter());
        assert_eq!(s, "[1, 2, 3]");
    }

    #[test]
    fn test_type_vec_print_empty() {
        let v: Vec<Type> = vec![];
        let s = Printer("").print_it(v.iter());
        assert_eq!(s, "[]");
    }

    #[test]
    fn test_type_vec_print_single() {
        let v = vec![Type::Num];
        let s = Printer(", ").print_it(v.iter());
        assert_eq!(s, "[num]");
    }

    #[test]
    fn test_type_vec_print_multiple() {
        let v = vec![Type::Num, Type::Bool, Type::Unit];
        let s = Printer(", ").print_it(v.iter());
        assert_eq!(s, "[num, bool, ()]");
    }

    #[test]
    fn test_type_vec_print_complex() {
        let v = vec![
            Type::Num,
            Type::Fn {
                arg: Box::new(Type::Bool),
                ret: Box::new(Type::Num),
            },
        ];
        let s = Printer("|").print_it(v.iter());
        assert_eq!(s, "[num|bool → num]");
    }
}
