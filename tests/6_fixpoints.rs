#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::ast_util::Symbol;
    use interpreter::evaluate::eval;
    use interpreter::flags::Verbosity;
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn eval_test() {
        let fact = parse(
            r#"
            letrec fact : num -> num = fun (n : num) ->
              if n == 0 then 1 else n * (fact (n - 1))
            in
              fact 5
            "#,
        )
        .unwrap();
        assert_eq!(eval(&fact, Verbosity::Normal), Expr::Num(120));
        assert_eq!(type_check(&fact).unwrap(), Type::Num);
    }

    #[test]
    fn aequiv() {
        let fact = parse(
            r#"
            letrec fact : num -> num = fun (n : num) ->
              if n == 0 then 1 else n * (fact (n - 1))
            in
              fact 5
            "#,
        )
        .unwrap();
        assert!(Expr::alpha_equiv(
            fact.clone().substitute(Variable::from("n"), Expr::Var("t".into())),
            *fact
        ));
    }
}
