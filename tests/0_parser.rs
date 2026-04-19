#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::parser::parse;

    #[test]
    fn lam_app() {
        assert_eq!(
            parse("fun x -> x y").unwrap(),
            Box::new(Expr::Lam {
                x: Variable::from("x"),
                e: Box::new(Expr::App {
                    lam: Box::new(Expr::Var("x".into())),
                    arg: Box::new(Expr::Var("y".into()))
                })
            })
        );

        assert_eq!(
            parse("x y z").unwrap(),
            parse("((x y) z)").unwrap()
        );

        assert_eq!(
            parse("fun x -> fun y -> x y").unwrap(),
            parse("fun x -> (fun y -> x y)").unwrap(),
        );
    }
}
