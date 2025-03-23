#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable(pub String);

impl From<Variable> for String {
    fn from(value: Variable) -> Self {
        value.0
    }
}

impl<T> From<T> for Variable
where
    T: ToString,
{
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

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Num => write!(f, "num"),
            Type::Bool => write!(f, "bool"),
            Type::Unit => write!(f, "()"),
            Type::Var(v) => write!(f, "{}", v.0),
            Type::Fn { arg, ret } => write!(f, "{} → {}", arg, ret),
            Type::Product { left, right } => write!(f, "{} * {}", left, right),
            Type::Sum { left, right } => write!(f, "{} + {}", left, right),
            _ => write!(f, "{:?}", self),
        }
    }
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

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(v) => write!(f, "{}", v.0),
            Expr::Num(n) => write!(f, "{}", n),
            Expr::True => write!(f, "true"),
            Expr::False => write!(f, "false"),
            Expr::Unit => write!(f, "()"),
            Expr::Addop { binop, left, right } => write!(f, "({} {} {})", left, binop, right),
            Expr::Mulop { binop, left, right } => write!(f, "({} {} {})", left, binop, right),
            Expr::If { cond, then_, else_ } => {
                write!(f, "if {} then {} else {}", cond, then_, else_)
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
                "case {} of L({}) -> {} | R({}) -> {}",
                e, xleft.0, eleft, xright.0, eright
            ),
            Expr::App { lam, arg } => write!(f, "({} {})", lam, arg),
            Expr::Lam { x, tau, e } => write!(f, "fun ({} : {}) -> {}", x.0, tau, e),
            Expr::TyLam { a, e } => write!(f, "tyfun {} -> {}", a.0, e),
            Expr::TyApp { e, tau } => write!(f, "({} {})", e, tau),
            Expr::Fix { x, tau, e } => write!(f, "fix ({} : {}) -> {}", x.0, tau, e),
            Expr::Fold { e, .. } => write!(f, "fold {} as ...", e),
            Expr::Unfold(e) => write!(f, "unfold {}", e),
            Expr::Export {
                e,
                tau_adt,
                tau_mod,
            } => write!(f, "export {} without {} as {}", e, tau_adt, tau_mod),
            Expr::Import {
                x,
                a,
                e_mod,
                e_body,
            } => write!(f, "import ({}, {}) = {} in {}", x.0, a.0, e_mod, e_body),
        }
    }
}
