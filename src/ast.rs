#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable(pub String);

impl From<Variable> for String {
    fn from(value: Variable) -> Self {
        value.0
    }
}

impl<T> From<T> for Variable where T: ToString {
    fn from(i: T) -> Self {
        Self(i.to_string())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Num,
    Bool,
    Unit,
    Var(Variable),
    Fn { arg: Box<Type>, ret: Box<Type> },
    Product { left: Box<Type>, right: Box<Type> },
    Sum { left: Box<Type>, right: Box<Type> },
    Rec { a: Variable, tau: Box<Type> },
    Forall { a: Variable, tau: Box<Type> },
    Exists { a: Variable, tau: Box<Type> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddOp {
    Add,
    Sub,
}

impl std::fmt::Display for AddOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddOp::Add => write!(f, "+"),
            AddOp::Sub => write!(f, "-"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MulOp {
    Mul,
    Div,
}

impl std::fmt::Display for MulOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MulOp::Mul => write!(f, "*"),
            MulOp::Div => write!(f, "/"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelOp {
    Lt,
    Gt,
    Eq,
}

impl std::fmt::Display for RelOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelOp::Lt => write!(f, "<"),
            RelOp::Gt => write!(f, ">"),
            RelOp::Eq => write!(f, "="),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Num(i32),
    Addop {
        binop: AddOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Mulop {
        binop: MulOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    True,
    False,
    If {
        cond: Box<Expr>,
        then_: Box<Expr>,
        else_: Box<Expr>,
    },
    Relop {
        relop: RelOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    And {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Or {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Var(Variable),
    Lam {
        x: Variable,
        tau: Box<Type>,
        e: Box<Expr>,
    },
    App {
        lam: Box<Expr>,
        arg: Box<Expr>,
    },
    Unit,
    Pair {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Project {
        e: Box<Expr>,
        d: Direction,
    },
    Inject {
        e: Box<Expr>,
        d: Direction,
        tau: Box<Type>,
    },
    Case {
        e: Box<Expr>,
        xleft: Variable,
        eleft: Box<Expr>,
        xright: Variable,
        eright: Box<Expr>,
    },
    Fix {
        x: Variable,
        tau: Box<Type>,
        e: Box<Expr>,
    },
    TyLam {
        a: Variable,
        e: Box<Expr>,
    },
    TyApp {
        e: Box<Expr>,
        tau: Box<Type>,
    },
    Fold {
        e: Box<Expr>,
        tau: Box<Type>,
    },
    Unfold(Box<Expr>),
    Export {
        e: Box<Expr>,
        tau_adt: Box<Type>,
        tau_mod: Box<Type>,
    },
    Import {
        x: Variable,
        a: Variable,
        e_mod: Box<Expr>,
        e_body: Box<Expr>,
    },
}
