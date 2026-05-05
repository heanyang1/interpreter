#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::evaluate::eval;
    use interpreter::flags::{Mode, OutputMode};
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn eval_test() {
        let poly = parse(
            r#"
            let id = fun x -> x in id 100
            "#,
        )
        .unwrap();
        assert_eq!(eval(&poly, Mode::Eval, OutputMode::Full), Expr::Num(100));
        assert_eq!(type_check(&poly).unwrap(), Type::Num);
        let poly = parse(
            r#"
            let id = fun u -> fun x -> x in (id ()) 100
            "#,
        )
        .unwrap();
        assert_eq!(eval(&poly, Mode::Eval, OutputMode::Full), Expr::Num(100));
        assert_eq!(type_check(&poly).unwrap(), Type::Num);
        let opt = parse(
            r#"
            let none = (inj () = L) in
            let some = fun x -> (inj x = R) in
            case (some 1) {
              L(x) -> 0
            | R(n) -> n + 1
            }
            "#,
        )
        .unwrap();
        assert_eq!(eval(&opt, Mode::Eval, OutputMode::Full), Expr::Num(2));
        assert_eq!(type_check(&opt).unwrap(), Type::Num);
    }

    #[test]
    fn different_types() {
        let poly = parse(
            r#"
            let id = fun x -> x in if (id true) then (id 100) else 1
            "#,
        )
        .unwrap();
        assert_eq!(eval(&poly, Mode::Eval, OutputMode::Full), Expr::Num(100));
        assert_eq!(type_check(&poly).unwrap(), Type::Num);
    }
}
