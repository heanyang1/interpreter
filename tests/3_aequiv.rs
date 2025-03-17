#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::ast_util::Symbol;
    use interpreter::parser::parse;

    #[test]
    fn inline_test() {
        let expr1 = parse("(fun (x : num) -> x) y").unwrap();
        assert!(Expr::alpha_equiv(
            *expr1.clone(),
            expr1.substitute(Variable::from("x"), Expr::Num(0))
        ));
        assert!(Expr::alpha_equiv(
            *parse("(fun (x : num) -> x) 0").unwrap(),
            expr1.substitute(Variable::from("y"), Expr::Num(0))
        ));

        let expr2 = parse("x + (fun (x : num) -> y)").unwrap();
        assert!(Expr::alpha_equiv(
            expr2.substitute(Variable::from("x"), Expr::Num(0)),
            *parse("0 + (fun (x : num) -> y)").unwrap()
        ));
        assert!(Expr::alpha_equiv(
            expr2.substitute(Variable::from("y"), Expr::Num(0)),
            *parse("x + (fun (x : num) -> 0)").unwrap()
        ));

        assert!(Expr::alpha_equiv(
            *parse("fun (x : num) -> x").unwrap(),
            *parse("fun (y : num) -> y").unwrap()
        ));

        assert!(!Expr::alpha_equiv(
            *parse("fun (x : num) -> fun (x : num) -> x + x").unwrap(),
            *parse("fun (x : num) -> fun (y : num) -> y + x").unwrap()
        ))
    }

    #[test]
    fn lec_2_example() {
        let expr1 = parse("(fun (z : num) -> x)").unwrap();
        assert!(Expr::alpha_equiv(
            expr1.substitute(Variable::from("x"), Expr::Var("y".into())),
            *parse("(fun (z : num) -> y)").unwrap()
        ));

        let expr2 = parse("fun (y : num) -> (x y)").unwrap();
        assert!(Expr::alpha_equiv(
            expr2.substitute(Variable::from("x"), Expr::Var("y".into())),
            *parse("fun (y_ : num) -> (y y_)").unwrap()
        ));
        assert!(Expr::alpha_equiv(
            expr2.substitute(Variable::from("x"), Expr::Num(0)),
            *parse("fun (y_ : num) -> (0 y_)").unwrap()
        ));

        let expr3 = parse("x (fun (x : num) -> (x x))").unwrap();
        assert!(Expr::alpha_equiv(
            expr3.substitute(Variable::from("x"), Expr::Var("y".into())),
            *parse("y (fun (x : num) -> (x x))").unwrap()
        ));
    }

    #[test]
    fn arithmetic_test() {
        assert!(Expr::alpha_equiv(
            *parse("fun (x : num) -> 3 + x - 2 * x / z").unwrap(),
            *parse("fun (y : num) -> 3 + y - 2 * y / z").unwrap()
        ));
        assert!(!Expr::alpha_equiv(
            *parse("fun (x : num) -> 3 + x - 2 * x / z").unwrap(),
            *parse("fun (x : num) -> 3 + y - 2 * x / z").unwrap()
        ));
        assert!(!Expr::alpha_equiv(
            *parse("fun (x : num) -> 3 + x - 2 * x / z").unwrap(),
            parse("fun (x : num) -> 3 + y - 2 * x / z")
                .unwrap()
                .substitute(Variable::from("y"), Expr::Var("x".into())),
        ));
    }

    #[test]
    fn conditional_test() {
        assert!(Expr::alpha_equiv(
            *parse("fun (x : num) -> 1&&x||z<0").unwrap(),
            *parse("fun (y : num) -> 1&&y||z<0").unwrap()
        ));

        assert!(Expr::alpha_equiv(
            parse("fun (x : num) -> if 1 && x then z < 0 || y < z else x == y")
                .unwrap()
                .substitute(Variable::from("y"), Expr::Var("x".into())),
            *parse("fun (x_ : num) -> if 1 && x_ then z < 0 || x < z else x_ == x").unwrap()
        ));

        assert!(Expr::alpha_equiv(
            *parse("fun (x : num) -> if true then x else x").unwrap(),
            *parse("fun (y : num) -> if true then y else y").unwrap()
        ));

        assert!(!Expr::alpha_equiv(
            *parse("if true then x else x").unwrap(),
            *parse("if false then x else x").unwrap()
        ));
    }
}
