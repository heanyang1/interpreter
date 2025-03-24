#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::ast_util::Symbol;
    use interpreter::evaluate::eval;
    use interpreter::flags::{Mode, OutputMode};
    use interpreter::parser::{parse, parse_type};
    use interpreter::typecheck::type_check;

    #[test]
    fn eval_test() {
        let poly = parse(
            r#"
            let id : forall a . a -> a = tyfun a -> fun (x : a) -> x in
              id [num] 100
            "#,
        )
        .unwrap();
        assert_eq!(eval(&poly, Mode::Eval, OutputMode::Full), Expr::Num(100));
        assert_eq!(type_check(&poly).unwrap(), Type::Num);
        let poly = parse(
            r#"
            let id : unit -> (forall a . a -> a) = fun (u : unit) -> (tyfun a -> fun (x : a) -> x) in
              (id ()) [num] 100
            "#,
        )
        .unwrap();
        assert_eq!(eval(&poly, Mode::Eval, OutputMode::Full), Expr::Num(100));
        assert_eq!(type_check(&poly).unwrap(), Type::Num);
        let opt = parse(
            r#"
            let none : forall a . unit + a = tyfun a -> (inj () = L as unit + a) in
            let some : forall a . a -> (unit + a) =
              tyfun a -> fun (x : a) -> (inj x = R as unit + a)
            in
            case (some [num] 1) {
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
    fn aequiv() {
        assert!(Expr::alpha_equiv(
            *parse("tyfun a -> fun (x : a) -> x").unwrap(),
            *parse("tyfun b -> fun (x : b) -> x").unwrap()
        ));
        println!(
            "{:#?}",
            parse(
                r#"
            let id : forall a . a -> a = tyfun a -> fun (x : a) -> x in
              id [num] 100
            "#,
            )
            .unwrap()
            .to_debruijn()
        );
        assert!(Expr::alpha_equiv(
            *parse(
                r#"
                let id : forall a . a -> a = tyfun a -> fun (x : a) -> x in
                  id [num] 100
                "#,
            )
            .unwrap(),
            *parse(
                r#"
                let id : forall b . b -> b = tyfun b -> fun (y : b) -> y in
                  id [num] 100
                "#,
            )
            .unwrap()
        ));
    }

    #[test]
    fn ty_aequiv() {
        assert!(Type::alpha_equiv(
            parse_type("forall b . a")
                .unwrap()
                .substitute(Variable::from("a"), *parse_type("num").unwrap()),
            *parse_type("forall a . num").unwrap()
        ));
        assert!(Type::alpha_equiv(
            parse_type("forall b . a")
                .unwrap()
                .substitute(Variable::from("a"), *parse_type("b").unwrap()),
            *parse_type("forall c . b").unwrap()
        ));
        assert!(!Type::alpha_equiv(
            parse_type("forall b . a")
                .unwrap()
                .substitute(Variable::from("a"), *parse_type("b").unwrap()),
            *parse_type("forall b . b").unwrap()
        ));
        assert!(Type::alpha_equiv(
            parse_type("forall b . forall b . a")
                .unwrap()
                .substitute(Variable::from("a"), *parse_type("b").unwrap()),
            *parse_type("forall q . forall c . b").unwrap()
        ));
        assert!(!Type::alpha_equiv(
            parse_type("forall b . forall b . a")
                .unwrap()
                .substitute(Variable::from("a"), *parse_type("b").unwrap()),
            *parse_type("forall a . forall b . a").unwrap()
        ));

        assert!(Type::alpha_equiv(
            *parse_type("forall a . a").unwrap(),
            *parse_type("forall b . b").unwrap()
        ));
        assert!(!Type::alpha_equiv(
            *parse_type("forall a . a").unwrap(),
            *parse_type("forall b . num").unwrap()
        ));
        assert!(Type::alpha_equiv(
            *parse_type("forall a . forall b . a -> b").unwrap(),
            *parse_type("forall x . forall y . x -> y").unwrap()
        ));
    }
}
