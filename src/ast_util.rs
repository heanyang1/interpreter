use std::collections::HashMap;

use crate::ast::{Expr, Type, Variable};

fn fresh(v: &Variable) -> Variable {
    Variable::from(format!("{}_", v.0))
}

pub trait Symbol: Sized {
    fn to_debruijn_map(self, depth: HashMap<Variable, u32>) -> Self;
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
    fn to_debruijn_map(self, depth: HashMap<Variable, u32>) -> Self {
        match self {
            Type::Num => self,
            _ => todo!(),
        }
    }

    fn alpha_equiv(e1: Self, e2: Self) -> bool {
        e1.to_debruijn() == e2.to_debruijn()
    }

    fn substitute_map(self, rename: HashMap<Variable, Type>) -> Type {
        match self {
            Type::Num => self,
            _ => todo!(),
        }
    }
}

impl Symbol for Expr {
    fn to_debruijn_map(self, depth: HashMap<Variable, u32>) -> Self {
        match self {
            Expr::Num(_) => self.clone(),
            _ => todo!(),
        }
    }

    fn alpha_equiv(e1: Self, e2: Self) -> bool {
        e1.to_debruijn() == e2.to_debruijn()
    }

    fn substitute_map(self, rename: HashMap<Variable, Expr>) -> Expr {
        match self {
            Expr::Num(_) => self.clone(),
            _ => todo!(),
        }
    }
}
