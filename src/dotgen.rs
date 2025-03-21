use crate::ast::*;

use petgraph::dot::{Config, Dot};
use petgraph::graph::{Graph, NodeIndex};
use regex::Regex;

pub fn to_dot(ast: &Expr, name: Option<String>) -> String {
    let mut graph = Graph::new();
    let cur = graph.add_node(String::new());
    ast.to_graph(&mut graph, Some(cur));
    let dot = format!(
        "{:?}",
        Dot::with_attr_getters(
            &graph,
            &[Config::NodeNoLabel],
            &|_, _| String::from("arrowhead=none"),
            &|_, _| String::from("shape=point, width=0.1"),
        )
    );
    match name {
        None => dot,
        Some(name) => {
            // the dot graph is wrapped in `digraph { ... }`
            // but we need `subgraph name { ... }`
            let dot_content = dot.strip_prefix("digraph {").unwrap_or(&dot);
            let re=Regex::new(r"[[:blank:]](\d+)[[:blank:]]").unwrap();
            let dot_content = re.replace_all(dot_content, format!(" {name}_$1 "));
            format!("subgraph {name} {{\n\t{dot_content}\n")
        }
    }
}

trait ToGraph {
    fn to_graph(&self, graph: &mut Graph<String, String>, parent: Option<NodeIndex>) -> NodeIndex;
}

macro_rules! add_node {
    ($s:expr, $graph:ident, $parent:ident; $( $children:expr ),* ) => {{
        let cur = $graph.add_node(String::new());
        if let Some(parent) = $parent {
            $graph.add_edge(parent, cur, $s.to_string());
        }
        $(
            $children.to_graph($graph, Some(cur));
        )*
        cur
    }};
}

impl ToGraph for Variable {
    fn to_graph(&self, graph: &mut Graph<String, String>, parent: Option<NodeIndex>) -> NodeIndex {
        let cur = graph.add_node(String::new());
        if let Some(parent) = parent {
            graph.add_edge(parent, cur, self.0.clone());
        }
        cur
    }
}

impl ToGraph for Expr {
    fn to_graph(&self, graph: &mut Graph<String, String>, parent: Option<NodeIndex>) -> NodeIndex {
        match self {
            Expr::Var(x) => x.to_graph(graph, parent),
            Expr::Num(n) => add_node!(n, graph, parent;),
            Expr::Addop { binop, left, right } => add_node!(binop, graph, parent; left, right),
            Expr::Mulop { binop, left, right } => add_node!(binop, graph, parent; left, right),
            Expr::True => add_node!("true", graph, parent;),
            Expr::False => add_node!("false", graph, parent;),
            Expr::If { cond, then_, else_ } => add_node!("if", graph, parent; cond, then_, else_),
            Expr::Relop { left, right, relop } => add_node!(relop, graph, parent; left, right),
            Expr::And { left, right } => add_node!("&&", graph, parent; left, right),
            Expr::Or { left, right } => add_node!("||", graph, parent; left, right),
            Expr::Pair { left, right } => add_node!("pair", graph, parent; left, right),
            Expr::Unit => add_node!("()", graph, parent;),
            Expr::App { lam, arg } => add_node!("app", graph, parent; lam, arg),
            Expr::Lam { x, tau, e } => add_node!("lam", graph, parent; x, tau, e),
            Expr::Fix { x, tau, e } => add_node!("fix", graph, parent; x, tau, e),
            Expr::Project { e, d } => add_node!("proj", graph, parent; e, d),
            Expr::Inject { e, d, tau } => add_node!("inject", graph, parent; e, d, tau),
            Expr::Case {
                e,
                xleft,
                eleft,
                xright,
                eright,
            } => add_node!("case", graph, parent; e, xleft, eleft, xright, eright),
            Expr::TyApp { e, tau } => add_node!("tyapp", graph, parent; e, tau),
            Expr::TyLam { a, e } => add_node!("tylam", graph, parent; a, e),
            Expr::Fold { e, tau } => add_node!("fold", graph, parent; e, tau),
            Expr::Unfold(e) => add_node!("unfold", graph, parent; e),
            Expr::Import {
                x,
                a,
                e_mod,
                e_body,
            } => add_node!("import", graph, parent; x, a, e_mod, e_body),
            Expr::Export {
                e,
                tau_adt,
                tau_mod,
            } => add_node!("export", graph, parent; e, tau_adt, tau_mod),
        }
    }
}

impl ToGraph for Direction {
    fn to_graph(&self, graph: &mut Graph<String, String>, parent: Option<NodeIndex>) -> NodeIndex {
        match self {
            Direction::Left => add_node!("L", graph, parent;),
            Direction::Right => add_node!("R", graph, parent;),
        }
    }
}

impl ToGraph for Type {
    fn to_graph(&self, graph: &mut Graph<String, String>, parent: Option<NodeIndex>) -> NodeIndex {
        match self {
            Type::Num => add_node!("num", graph, parent;),
            Type::Bool => add_node!("bool", graph, parent;),
            Type::Product { left, right } => add_node!("*", graph, parent; left, right),
            Type::Sum { left, right } => add_node!("+", graph, parent; left, right),
            Type::Unit => add_node!("unit", graph, parent;),
            Type::Fn { arg, ret } => add_node!("→", graph, parent; arg, ret),
            Type::Var(v) => v.to_graph(graph, parent),
            Type::Rec { a, tau } => add_node!("rec", graph, parent; a, tau),
            Type::Forall { a, tau } => add_node!("forall", graph, parent; a, tau),
            Type::Exists { a, tau } => add_node!("exists", graph, parent; a, tau),
        }
    }
}
