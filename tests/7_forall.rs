#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::evaluate::eval;
    use interpreter::flags::{Mode, OutputMode};
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    #[ignore]
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
        // TODO: Add examples where forall types is instantiated as different types
    }
}
