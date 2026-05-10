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
    fn substitute_map(self, rename: HashMap<Variable, Self>) -> Self;
    fn substitute(self, s: Variable, e: Self) -> Self {
        self.substitute_map(HashMap::from([(s, e)]))
    }
    fn contains_var(&self, s: &Variable) -> bool;
}

impl Symbol for Type {
    fn contains_var(&self, s: &Variable) -> bool {
        match self {
            Type::Num | Type::Bool | Type::Unit => false,
            Type::Var(x) => x.clone() == s.clone(),
            Type::Product { left, right } | Type::Sum { left, right } => {
                left.contains_var(s) || right.contains_var(s)
            }
            Type::Fn { arg, ret } => arg.contains_var(s) || ret.contains_var(s),
            Type::Forall { a, tau } => a.clone() != s.clone() && tau.contains_var(s),
        }
    }
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
            Type::Fn { arg, ret } => trivial!(Type, Fn, depth, to_debruijn_map;; arg, ret;),
        }
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
            Type::Forall { a, tau } => match rename.get(&a) {
                Some(_) => tau.substitute_map(rename),
                None => Type::Forall {
                    a,
                    tau: Box::new(tau.substitute_map(rename)),
                },
            },
        }
    }
}

impl Symbol for Expr {
    fn contains_var(&self, s: &Variable) -> bool {
        todo!()
    }
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
            Expr::Let { x, e_x, e_in } => {
                let depth_clone = depth.clone();
                add_depth(&mut depth, [x.clone()]);
                Expr::Let {
                    x: Variable::from("_"),
                    e_x: Box::new(e_x.to_debruijn_map(depth_clone)),
                    e_in: Box::new(e_in.to_debruijn_map(depth)),
                }
            }
        }
    }

    fn substitute_map(self, mut rename: HashMap<Variable, Expr>) -> Expr {
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
                let new_x = fresh(&x);
                rename.insert(x, Expr::Var(new_x.clone()));
                Expr::Fix {
                    x: new_x,
                    e: Box::new(e.substitute_map(rename)),
                }
            }
            Expr::Let { x, e_x, e_in } => {
                let new_a = fresh(&x);
                rename.insert(x, Expr::Var(new_a.clone()));
                Expr::Let {
                    x: new_a,
                    e_x: Box::new(e_x.substitute_map(rename.clone())),
                    e_in: Box::new(e_in.substitute_map(rename)),
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
        assert_eq!(s, "[num|(bool → num)]");
    }

    #[test]
    fn test_type_to_debruijn_product() {
        let ty = Type::Product {
            left: Box::new(Type::Num),
            right: Box::new(Type::Bool),
        };
        let result = ty.clone().to_debruijn();
        assert_eq!(result, ty);
    }

    #[test]
    fn test_type_to_debruijn_sum() {
        let ty = Type::Sum {
            left: Box::new(Type::Num),
            right: Box::new(Type::Bool),
        };
        let result = ty.clone().to_debruijn();
        assert_eq!(result, ty);
    }

    #[test]
    fn test_type_to_debruijn_fn() {
        let ty = Type::Fn {
            arg: Box::new(Type::Bool),
            ret: Box::new(Type::Num),
        };
        let result = ty.clone().to_debruijn();
        assert_eq!(result, ty);
    }

    #[test]
    fn test_type_to_debruijn_var() {
        let ty = Type::Var("x".into());
        let result = ty.clone().to_debruijn();
        assert_eq!(result, ty);
    }

    #[test]
    fn test_type_to_debruijn_var_bound() {
        let mut depth = HashMap::new();
        depth.insert("x".into(), 5);
        let ty = Type::Var("x".into());
        let result = ty.to_debruijn_map(depth);
        assert_eq!(result, Type::Var("5".into()));
    }

    #[test]
    fn test_type_to_debruijn_forall() {
        let ty = Type::Forall {
            a: "a".into(),
            tau: Box::new(Type::Var("a".into())),
        };
        let result = ty.clone().to_debruijn();
        match result {
            Type::Forall { a, tau } => {
                assert_eq!(a.0, "_");
                assert_eq!(*tau, Type::Var("0".into()));
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_type_substitute_map_product() {
        let ty = Type::Product {
            left: Box::new(Type::Var("x".into())),
            right: Box::new(Type::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Type::Num), ("y".into(), Type::Bool)]);
        let result = ty.substitute_map(rename);
        assert_eq!(
            result,
            Type::Product {
                left: Box::new(Type::Num),
                right: Box::new(Type::Bool),
            }
        );
    }

    #[test]
    fn test_type_substitute_map_sum() {
        let ty = Type::Sum {
            left: Box::new(Type::Var("x".into())),
            right: Box::new(Type::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Type::Num), ("y".into(), Type::Bool)]);
        let result = ty.substitute_map(rename);
        assert_eq!(
            result,
            Type::Sum {
                left: Box::new(Type::Num),
                right: Box::new(Type::Bool),
            }
        );
    }

    #[test]
    fn test_type_substitute_map_fn() {
        let ty = Type::Fn {
            arg: Box::new(Type::Var("a".into())),
            ret: Box::new(Type::Var("b".into())),
        };
        let rename = HashMap::from([("a".into(), Type::Num), ("b".into(), Type::Bool)]);
        let result = ty.substitute_map(rename);
        assert_eq!(
            result,
            Type::Fn {
                arg: Box::new(Type::Num),
                ret: Box::new(Type::Bool),
            }
        );
    }

    #[test]
    fn test_type_substitute_map_var_found() {
        let ty = Type::Var("x".into());
        let rename = HashMap::from([("x".into(), Type::Num)]);
        let result = ty.substitute_map(rename);
        assert_eq!(result, Type::Num);
    }

    #[test]
    fn test_type_substitute_map_var_not_found() {
        let ty = Type::Var("x".into());
        let rename = HashMap::new();
        let result = ty.substitute_map(rename);
        assert_eq!(result, Type::Var("x".into()));
    }

    #[test]
    fn test_type_substitute_map_forall() {
        let ty = Type::Forall {
            a: "a".into(),
            tau: Box::new(Type::Var("a".into())),
        };
        let rename = HashMap::from([("a".into(), Type::Num)]);
        let result = ty.substitute_map(rename);
        assert_eq!(result, Type::Num);
        let ty = Type::Forall {
            a: "a1".into(),
            tau: Box::new(Type::Var("a".into())),
        };
        let rename = HashMap::from([("a".into(), Type::Num)]);
        let result = ty.substitute_map(rename);
        match result {
            Type::Forall { a, tau } => {
                assert_eq!(a.0, "a1");
                assert_eq!(*tau, Type::Num);
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_expr_to_debruijn_addop() {
        let e = Expr::Addop {
            binop: crate::ast::AddOp::Add,
            left: Box::new(Expr::Num(1)),
            right: Box::new(Expr::Num(2)),
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_mulop() {
        let e = Expr::Mulop {
            binop: crate::ast::MulOp::Mul,
            left: Box::new(Expr::Num(1)),
            right: Box::new(Expr::Num(2)),
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_relop() {
        let e = Expr::Relop {
            relop: crate::ast::RelOp::Lt,
            left: Box::new(Expr::Num(1)),
            right: Box::new(Expr::Num(2)),
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_if() {
        let e = Expr::If {
            cond: Box::new(Expr::True),
            then_: Box::new(Expr::Num(1)),
            else_: Box::new(Expr::Num(2)),
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_and() {
        let e = Expr::And {
            left: Box::new(Expr::True),
            right: Box::new(Expr::False),
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_or() {
        let e = Expr::Or {
            left: Box::new(Expr::True),
            right: Box::new(Expr::False),
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_pair() {
        let e = Expr::Pair {
            left: Box::new(Expr::Num(1)),
            right: Box::new(Expr::Num(2)),
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_project() {
        let e = Expr::Project {
            e: Box::new(Expr::Pair {
                left: Box::new(Expr::Num(1)),
                right: Box::new(Expr::Num(2)),
            }),
            d: crate::ast::Direction::Left,
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_inject() {
        let e = Expr::Inject {
            e: Box::new(Expr::Num(1)),
            d: crate::ast::Direction::Left,
        };
        let result = e.clone().to_debruijn();
        assert_eq!(result, e);
    }

    #[test]
    fn test_expr_to_debruijn_var_bound() {
        let mut depth = HashMap::new();
        depth.insert("x".into(), 3);
        let e = Expr::Var("x".into());
        let result = e.to_debruijn_map(depth);
        assert_eq!(result, Expr::DeBruijn(3));
    }

    #[test]
    fn test_expr_to_debruijn_var_free() {
        let depth = HashMap::new();
        let e = Expr::Var("x".into());
        let result = e.to_debruijn_map(depth);
        assert_eq!(result, Expr::Var("x".into()));
    }

    #[test]
    fn test_expr_to_debruijn_lam() {
        let e = Expr::Lam {
            x: "x".into(),
            e: Box::new(Expr::Var("x".into())),
        };
        let result = e.to_debruijn();
        match result {
            Expr::Lam { x, e } => {
                assert_eq!(x.0, "_");
                assert_eq!(*e, Expr::DeBruijn(0));
            }
            _ => panic!("Expected Lam"),
        }
    }

    #[test]
    fn test_expr_to_debruijn_app() {
        let e = Expr::App {
            lam: Box::new(Expr::Lam {
                x: "x".into(),
                e: Box::new(Expr::Var("x".into())),
            }),
            arg: Box::new(Expr::Num(1)),
        };
        let result = e.to_debruijn();
        match result {
            Expr::App { lam, arg } => match *lam {
                Expr::Lam { x, e } => {
                    assert_eq!(x.0, "_");
                    assert_eq!(e, Box::new(Expr::DeBruijn(0)));
                    assert_eq!(arg, Box::new(Expr::Num(1)));
                }
                _ => panic!("Expect Lam"),
            },
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_expr_to_debruijn_fix() {
        let e = Expr::Fix {
            x: "x".into(),
            e: Box::new(Expr::Var("x".into())),
        };
        let result = e.to_debruijn();
        println!("{result}");
        match result {
            Expr::Fix { x, e } => {
                assert_eq!(x.0, "_");
                assert_eq!(*e, Expr::DeBruijn(0));
            }
            _ => panic!("Expected Fix"),
        }
    }

    #[test]
    fn test_expr_to_debruijn_let() {
        let e = Expr::Let {
            x: "x".into(),
            e_x: Box::new(Expr::Var("x".into())),
            e_in: Box::new(Expr::Var("x".into())),
        };
        let result = e.to_debruijn();
        if let Expr::Let { x, e_x, e_in } = result {
            assert_eq!(x.0, "_");
            assert_eq!(*e_x, Expr::Var("x".into()));
            assert_eq!(*e_in, Expr::DeBruijn(0));
        } else {
            panic!("Expected Let expression");
        }
    }

    #[test]
    fn test_expr_substitute_map_addop() {
        let e = Expr::Addop {
            binop: crate::ast::AddOp::Add,
            left: Box::new(Expr::Var("x".into())),
            right: Box::new(Expr::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Expr::Num(1)), ("y".into(), Expr::Num(2))]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::Addop {
                binop: crate::ast::AddOp::Add,
                left: Box::new(Expr::Num(1)),
                right: Box::new(Expr::Num(2)),
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_mulop() {
        let e = Expr::Mulop {
            binop: crate::ast::MulOp::Mul,
            left: Box::new(Expr::Var("x".into())),
            right: Box::new(Expr::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Expr::Num(1)), ("y".into(), Expr::Num(2))]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::Mulop {
                binop: crate::ast::MulOp::Mul,
                left: Box::new(Expr::Num(1)),
                right: Box::new(Expr::Num(2)),
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_relop() {
        let e = Expr::Relop {
            relop: crate::ast::RelOp::Lt,
            left: Box::new(Expr::Var("x".into())),
            right: Box::new(Expr::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Expr::Num(1)), ("y".into(), Expr::Num(2))]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::Relop {
                relop: crate::ast::RelOp::Lt,
                left: Box::new(Expr::Num(1)),
                right: Box::new(Expr::Num(2)),
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_if() {
        let e = Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_: Box::new(Expr::Var("t".into())),
            else_: Box::new(Expr::Var("e".into())),
        };
        let rename = HashMap::from([
            ("c".into(), Expr::True),
            ("t".into(), Expr::Num(1)),
            ("e".into(), Expr::Num(2)),
        ]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::If {
                cond: Box::new(Expr::True),
                then_: Box::new(Expr::Num(1)),
                else_: Box::new(Expr::Num(2)),
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_and() {
        let e = Expr::And {
            left: Box::new(Expr::Var("x".into())),
            right: Box::new(Expr::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Expr::True), ("y".into(), Expr::False)]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::And {
                left: Box::new(Expr::True),
                right: Box::new(Expr::False),
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_or() {
        let e = Expr::Or {
            left: Box::new(Expr::Var("x".into())),
            right: Box::new(Expr::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Expr::True), ("y".into(), Expr::False)]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::Or {
                left: Box::new(Expr::True),
                right: Box::new(Expr::False),
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_var_found() {
        let e = Expr::Var("x".into());
        let rename = HashMap::from([("x".into(), Expr::Num(42))]);
        let result = e.substitute_map(rename);
        assert_eq!(result, Expr::Num(42));
    }

    #[test]
    fn test_expr_substitute_map_var_not_found() {
        let e = Expr::Var("x".into());
        let rename = HashMap::new();
        let result = e.substitute_map(rename);
        assert_eq!(result, Expr::Var("x".into()));
    }

    #[test]
    fn test_expr_substitute_map_lam() {
        let e = Expr::Lam {
            x: "x".into(),
            e: Box::new(Expr::Var("x".into())),
        };
        let rename = HashMap::new();
        let result = e.substitute_map(rename);
        assert!(matches!(result, Expr::Lam { x, e: _ } if x.0 != "x"));
    }

    #[test]
    fn test_expr_substitute_map_app() {
        let e = Expr::App {
            lam: Box::new(Expr::Var("f".into())),
            arg: Box::new(Expr::Var("x".into())),
        };
        let rename = HashMap::from([
            (
                "f".into(),
                Expr::Lam {
                    x: "y".into(),
                    e: Box::new(Expr::Var("y".into())),
                },
            ),
            ("x".into(), Expr::Num(1)),
        ]);
        let result = e.substitute_map(rename);
        assert!(matches!(result, Expr::App { .. }));
    }

    #[test]
    fn test_expr_substitute_map_pair() {
        let e = Expr::Pair {
            left: Box::new(Expr::Var("x".into())),
            right: Box::new(Expr::Var("y".into())),
        };
        let rename = HashMap::from([("x".into(), Expr::Num(1)), ("y".into(), Expr::Num(2))]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::Pair {
                left: Box::new(Expr::Num(1)),
                right: Box::new(Expr::Num(2)),
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_project() {
        let e = Expr::Project {
            e: Box::new(Expr::Var("p".into())),
            d: crate::ast::Direction::Left,
        };
        let rename = HashMap::from([(
            "p".into(),
            Expr::Pair {
                left: Box::new(Expr::Num(1)),
                right: Box::new(Expr::Num(2)),
            },
        )]);
        let result = e.substitute_map(rename);
        assert!(matches!(result, Expr::Project { .. }));
    }

    #[test]
    fn test_expr_substitute_map_inject() {
        let e = Expr::Inject {
            e: Box::new(Expr::Var("x".into())),
            d: crate::ast::Direction::Left,
        };
        let rename = HashMap::from([("x".into(), Expr::Num(1))]);
        let result = e.substitute_map(rename);
        assert_eq!(
            result,
            Expr::Inject {
                e: Box::new(Expr::Num(1)),
                d: crate::ast::Direction::Left,
            }
        );
    }

    #[test]
    fn test_expr_substitute_map_fix() {
        let e = Expr::Fix {
            x: "f".into(),
            e: Box::new(Expr::Var("f".into())),
        };
        let rename = HashMap::new();
        let result = e.substitute_map(rename);
        assert!(matches!(result, Expr::Fix { x, .. } if x.0 != "f"));
    }

    #[test]
    fn test_expr_substitute_map_let() {
        let e = Expr::Let {
            x: "x".into(),
            e_x: Box::new(Expr::Num(1)),
            e_in: Box::new(Expr::Var("x".into())),
        };
        let rename = HashMap::new();
        let result = e.substitute_map(rename);
        assert!(matches!(result, Expr::Let { x, .. } if x.0 != "x"));
    }

    #[test]
    fn test_expr_substitute_using_trait() {
        let e = Expr::Var("x".into());
        let result = e.substitute("x".into(), Expr::Num(42));
        assert_eq!(result, Expr::Num(42));
    }

    #[test]
    fn test_type_to_debruijn_using_trait() {
        let ty = Type::Var("x".into());
        let result = ty.to_debruijn();
        assert_eq!(result, Type::Var("x".into()));
    }

    #[test]
    fn test_type_substitute_using_trait() {
        let ty = Type::Var("x".into());
        let result = ty.substitute("x".into(), Type::Num);
        assert_eq!(result, Type::Num);
    }

    #[test]
    fn test_printer_print_map() {
        let mut m: HashMap<String, i32> = HashMap::new();
        m.insert("a".to_string(), 1);
        m.insert("b".to_string(), 2);
        let s = Printer(", ").print_map(&m);
        assert!(s.contains("a: 1") || s.contains("b: 2"));
    }

    #[test]
    fn test_printer_print_map_empty() {
        let m: HashMap<String, i32> = HashMap::new();
        let s = Printer(", ").print_map(&m);
        assert_eq!(s, "[]");
    }

    #[test]
    fn test_expr_substitute_map_case() {
        let e = Expr::Case {
            e: Box::new(Expr::Var("x".into())),
            xleft: "l".into(),
            eleft: Box::new(Expr::Var("l".into())),
            xright: "r".into(),
            eright: Box::new(Expr::Var("r".into())),
        };
        let rename = HashMap::from([("x".into(), Expr::Num(1))]);
        let result = e.substitute_map(rename);
        assert!(
            matches!(result, Expr::Case { xleft, xright, .. } if xleft.0 != "l" && xright.0 != "r")
        );
    }
}
