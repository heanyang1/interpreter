use std::fmt::Display;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable(pub String);

impl From<&str> for Variable {
    fn from(value: &str) -> Self {
        Variable(value.to_string())
    }
}

impl From<String> for Variable {
    fn from(value: String) -> Self {
        Variable(value)
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
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

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Num => write!(f, "num"),
            Type::Bool => write!(f, "bool"),
            Type::Unit => write!(f, "()"),
            Type::Var(v) => write!(f, "{}", v),
            Type::Fn { arg, ret } => write!(f, "{} → {}", arg, ret),
            Type::Product { left, right } => write!(f, "{} * {}", left, right),
            Type::Sum { left, right } => write!(f, "{} + {}", left, right),
            Type::Rec { a, tau } => write!(f, "μ {} . {}", a, tau),
            Type::Forall { a, tau } => write!(f, "∀ {} . {}", a, tau),
            Type::Exists { a, tau } => write!(f, "∃ {} . {}", a, tau),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddOp {
    Add,
    Sub,
}

impl Display for AddOp {
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

impl Display for MulOp {
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

impl Display for RelOp {
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
    DeBruijn(usize),
    Lam {
        x: Variable,
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

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(v) => write!(f, "{}", v),
            Expr::DeBruijn(d) => write!(f, "<{}>", d),
            Expr::Num(n) => write!(f, "{}", n),
            Expr::True => write!(f, "true"),
            Expr::False => write!(f, "false"),
            Expr::Unit => write!(f, "()"),
            Expr::Addop { binop, left, right } => write!(f, "({} {} {})", left, binop, right),
            Expr::Mulop { binop, left, right } => write!(f, "({} {} {})", left, binop, right),
            Expr::If { cond, then_, else_ } => {
                write!(f, "(if {} then {} else {})", cond, then_, else_)
            }
            Expr::Relop { relop, left, right } => write!(f, "({} {} {})", left, relop, right),
            Expr::And { left, right } => write!(f, "({} && {})", left, right),
            Expr::Or { left, right } => write!(f, "({} || {})", left, right),
            Expr::Pair { left, right } => write!(f, "({} , {})", left, right),
            Expr::Project { e, d } => match (e.as_ref(), d) {
                (Expr::Pair { left, .. }, Direction::Left) => write!(f, "{}", left),
                (Expr::Pair { right, .. }, Direction::Right) => write!(f, "{}", right),
                _ => write!(f, "{:?}", self),
            },
            Expr::Inject { e, .. } => write!(f, "{}", e),
            Expr::Case {
                e,
                xleft,
                eleft,
                xright,
                eright,
            } => write!(
                f,
                "(case {} of L({}) -> {} | R({}) -> {})",
                e, xleft, eleft, xright, eright
            ),
            Expr::App { lam, arg } => write!(f, "({} {})", lam, arg),
            Expr::Lam { x, e } => write!(f, "(λ {} -> {})", x, e),
            Expr::TyLam { a, e } => write!(f, "(Λ {} -> {})", a, e),
            Expr::TyApp { e, tau } => write!(f, "({} {})", e, tau),
            Expr::Fix { x, e } => write!(f, "(fix {} -> {})", x, e),
            Expr::Fold { e, .. } => write!(f, "(fold {} as ...)", e),
            Expr::Unfold(e) => write!(f, "(unfold {})", e),
            Expr::Export {
                e,
                tau_adt,
                tau_mod,
            } => write!(f, "(export {} without {} as {})", e, tau_adt, tau_mod),
            Expr::Import {
                x,
                a,
                e_mod,
                e_body,
            } => write!(f, "(import ({}, {}) = {} in {})", x, a, e_mod, e_body),
        }
    }
}
