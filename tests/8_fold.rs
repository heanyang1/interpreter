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

    #[test]
    fn aequiv() {
        assert!(Expr::alpha_equiv(
            *parse(
                r#"
                let x : rec a . num * (a -> num) =
                  fold (0, fun (o : rec a . num * (a -> num)) -> (unfold o).L)
                  as rec a . num * (a -> num)
                in
                (unfold x).L
                "#,
            )
            .unwrap(),
            *parse(
                r#"
                let y : rec b . num * (b -> num) =
                  fold (0, fun (o : rec b . num * (b -> num)) -> (unfold o).L)
                  as rec b . num * (b -> num)
                in
                (unfold y).L
                "#,
            )
            .unwrap()
        ));
    }

    #[test]
    fn ty_aequiv() {
        assert!(Type::alpha_equiv(
            *parse_type("rec b . num * (b -> num)").unwrap(),
            *parse_type("rec c . num * (c -> num)").unwrap()
        ));
        assert!(!Type::alpha_equiv(
            *parse_type("rec a . unit * (a -> num)").unwrap(),
            *parse_type("rec a . num * (a -> num)").unwrap()
        ));
    }
}
