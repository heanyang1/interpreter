use crate::{ast::*, do_, monad::Monad};

static mut COUNTER: u32 = 0;

unsafe fn inc() -> u32 {
    unsafe {
        COUNTER += 1;
        COUNTER
    }
}

#[derive(Debug, Clone)]
struct NodeIndex {
    name: Option<String>,
    idx: u32,
}

impl NodeIndex {
    fn new(name: Option<String>) -> Self {
        NodeIndex {
            name,
            idx: unsafe { inc() },
        }
    }
}

struct Writer<T> {
    value: T,
    output: String,
}

impl<T> Monad<T> for Writer<T> {
    type Output<U> = Writer<U>;

    fn bind<U>(self, f: impl FnOnce(T) -> Writer<U>) -> Writer<U> {
        let Writer { value, output } = f(self.value);
        Writer {
            value,
            output: self.output + &output,
        }
    }
}

pub fn to_dot(ast: &Expr, name: Option<String>) -> String {
    match name {
        Some(name) => {
            let root = NodeIndex::new(Some(name.clone()));
            format!(
                "subgraph {} {{\n\t{} [shape=point, width=0.1];\n{}\n}}",
                name,
                root.clone().idx,
                ast.to_graph(root).output
            )
        }
        None => {
            let root = NodeIndex::new(None);
            format!(
                "digraph {{\n\t{} [shape=point, width=0.1];\n{}\n}}",
                root.clone().idx,
                ast.to_graph(root).output
            )
        }
    }
}

trait ToGraph {
    fn to_graph(&self, parent: NodeIndex) -> Writer<NodeIndex>;
}

fn new_node<T>(name: T, parent: NodeIndex, color: &str) -> Writer<NodeIndex>
where
    T: ToString,
{
    let cur = NodeIndex::new(parent.name.clone());
    Writer {
        value: cur.clone(),
        output: format!(
            "\t{} [shape=point, width=0.1, color=\"{}\"];\n\t{} -> {} [label=\"{}\", arrowhead=none, color=\"{}\", fontcolor=\"{}\"];\n",
            cur.clone().idx,
            color,
            parent.idx,
            cur.idx,
            name.to_string(),
            color,
            color,
        ),
    }
}

impl ToGraph for Variable {
    fn to_graph(&self, parent: NodeIndex) -> Writer<NodeIndex> {
        new_node(self.0.clone(), parent, "black")
    }
}

impl ToGraph for Expr {
    fn to_graph(&self, parent: NodeIndex) -> Writer<NodeIndex> {
        match self {
            Expr::Var(_) | Expr::Num(_) | Expr::True | Expr::False | Expr::Unit => {
                new_node(self, parent, "red")
            }
            Expr::Addop { binop, left, right } => do_!(
                new_node(binop, parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Expr::Mulop { binop, left, right } => do_!(
                new_node(binop, parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Expr::If { cond, then_, else_ } => do_!(
                new_node("if", parent, "red") => cur,
                cond.to_graph(cur.clone()),
                then_.to_graph(cur.clone()),
                else_.to_graph(cur)
            ),
            Expr::Relop { left, right, relop } => do_!(
                new_node(relop, parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Expr::And { left, right } => do_!(
                new_node("&&", parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Expr::Or { left, right } => do_!(
                new_node("||", parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Expr::Pair { left, right } => do_!(
                new_node("pair", parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Expr::App { lam, arg } => do_!(
                new_node("app", parent, "red") => cur,
                lam.to_graph(cur.clone()),
                arg.to_graph(cur)
            ),
            Expr::Lam { x, tau, e } => do_!(
                new_node("λ", parent, "red") => cur,
                x.to_graph(cur.clone()),
                tau.to_graph(cur.clone()),
                e.to_graph(cur)
            ),
            Expr::Fix { x, tau, e } => do_!(
                new_node("fix", parent, "red") => cur,
                x.to_graph(cur.clone()),
                tau.to_graph(cur.clone()),
                e.to_graph(cur)
            ),
            Expr::Project { e, d } => do_!(
                new_node(match d {
                    Direction::Left => "P_left",
                    Direction::Right => "P_right",
                }, parent, "red") => cur,
                e.to_graph(cur)
            ),
            Expr::Inject { e, d, tau } => do_!(
                new_node(match d {
                    Direction::Left => "I_left",
                    Direction::Right => "I_right",
                }, parent, "red") => cur,
                e.to_graph(cur.clone()),
                tau.to_graph(cur)
            ),
            Expr::Case {
                e,
                xleft,
                eleft,
                xright,
                eright,
            } => do_!(
                new_node("case", parent, "red") => cur,
                e.to_graph(cur.clone()),
                xleft.to_graph(cur.clone()),
                eleft.to_graph(cur.clone()),
                xright.to_graph(cur.clone()),
                eright.to_graph(cur)
            ),
            Expr::TyApp { e, tau } => do_!(
                new_node("tyapp", parent, "red") => cur,
                e.to_graph(cur.clone()),
                tau.to_graph(cur)
            ),
            Expr::TyLam { a, e } => do_!(
                new_node("Λ", parent, "red") => cur,
                a.to_graph(cur.clone()),
                e.to_graph(cur)
            ),
            Expr::Fold { e, tau } => do_!(
                new_node("fold", parent, "red") => cur,
                e.to_graph(cur.clone()),
                tau.to_graph(cur)
            ),
            Expr::Unfold(e) => do_!(
                new_node("unfold", parent, "red") => cur,
                e.to_graph(cur)
            ),
            Expr::Import {
                x,
                a,
                e_mod,
                e_body,
            } => do_!(
                new_node("import", parent, "red") => cur,
                x.to_graph(cur.clone()),
                a.to_graph(cur.clone()),
                e_mod.to_graph(cur.clone()),
                e_body.to_graph(cur)
            ),
            Expr::Export {
                e,
                tau_adt,
                tau_mod,
            } => do_!(
                new_node("export", parent, "red") => cur,
                e.to_graph(cur.clone()),
                tau_adt.to_graph(cur.clone()),
                tau_mod.to_graph(cur)
            ),
        }
    }
}

impl ToGraph for Type {
    fn to_graph(&self, parent: NodeIndex) -> Writer<NodeIndex> {
        match self {
            Type::Num | Type::Bool | Type::Unit | Type::Var(_) => new_node(self, parent, "blue"),
            Type::Product { left, right } => do_!(
                new_node("*", parent, "blue") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Type::Sum { left, right } => do_!(
                new_node("+", parent, "blue") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Type::Fn { arg, ret } => do_!(
                new_node("→", parent, "blue") => cur,
                arg.to_graph(cur.clone()),
                ret.to_graph(cur)
            ),
            Type::Rec { a, tau } => do_!(
                new_node("rec", parent, "blue") => cur,
                a.to_graph(cur.clone()),
                tau.to_graph(cur)
            ),
            Type::Forall { a, tau } => do_!(
                new_node("∀", parent, "blue") => cur,
                a.to_graph(cur.clone()),
                tau.to_graph(cur)
            ),
            Type::Exists { a, tau } => do_!(
                new_node("∃", parent, "blue") => cur,
                a.to_graph(cur.clone()),
                tau.to_graph(cur)
            ),
        }
    }
}
