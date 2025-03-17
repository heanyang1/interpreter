#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::parser::parse;

    #[test]
    fn lam_app() {
        assert_eq!(
            parse("fun (x : num) -> x y").unwrap(),
            Box::new(Expr::Lam {
                x: Variable::from("x"),
                tau: Box::new(Type::Num),
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
            parse("fun (x : num) -> fun (y:num) -> x y").unwrap(),
            parse("fun (x : num) -> (fun (y:num) -> x y)").unwrap(),
        );
    }
}
