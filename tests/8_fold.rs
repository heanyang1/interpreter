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
        let objrec = parse(
            r#"
            let x : rec a . num * (a -> num) =
              fold (0, fun (o : rec a . num * (a -> num)) -> (unfold o).L)
              as rec a . num * (a -> num)
            in
            (unfold x).L
            "#,
        )
        .unwrap();
        assert_eq!(eval(&objrec, Mode::Eval, OutputMode::Full), Expr::Num(0));
        assert_eq!(type_check(&objrec).unwrap(), Type::Num);
        let counter = parse(
            r#"
            letrec constr : num -> (rec a . num * (unit -> a)) =
              fun (x : num) ->
                fold (x, fun (u : unit) -> constr (x + 1))
                as rec a . num * (unit -> a)
            in
            let c1 : rec a . num * (unit -> a) = (constr 1) in
            let c2 : rec a . num * (unit -> a) = ((unfold c1).R ()) in
            (unfold c2).L
            "#,
        )
        .unwrap();
        assert_eq!(eval(&counter, Mode::Eval, OutputMode::Full), Expr::Num(2));
        assert_eq!(type_check(&counter).unwrap(), Type::Num);
    }
}
