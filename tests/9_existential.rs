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
        let objmod = parse(
            r#"
            let m : exists b . rec a . b * (a -> num) =
                export (fold (0, fun (o : rec a . num * (a -> num)) -> (unfold o).L)
                        as rec a . num * (a -> num))
                without num as exists b . rec a . b * (a -> num)
            in
            import (m2, a) = m in (
                let x : a = (unfold m2).L in
                let n : num = ((unfold m2).R m2) in
                n
            )
            "#,
        )
        .unwrap();
        assert_eq!(eval(&objmod, Mode::Eval, OutputMode::Full), Expr::Num(0));
        assert_eq!(type_check(&objmod).unwrap(), Type::Num);
        let objmod = parse(
            r#"
            let m : unit -> (exists b . rec a . b * (a -> num)) =
                fun (u : unit) ->
                    export (fold (0, fun (o : rec a . num * (a -> num)) -> (unfold o).L)
                            as rec a . num * (a -> num))
                    without num as exists b . rec a . b * (a -> num)
            in
            import (m2, a) = (m ()) in (
                let x : a = (unfold m2).L in
                let n : num = ((unfold m2).R m2) in
                n
            )
            "#,
        )
        .unwrap();
        assert_eq!(eval(&objmod, Mode::Eval, OutputMode::Full), Expr::Num(0));
        assert_eq!(type_check(&objmod).unwrap(), Type::Num);
    }

    #[test]
    fn aequiv() {
        assert!(Expr::alpha_equiv(
            *parse(
                r#"
                let m : exists c . rec a . c * (a -> num) =
                    export (fold (0, fun (o : rec a . num * (a -> num)) -> (unfold o).L)
                            as rec a . num * (a -> num))
                    without num as exists c . rec a . c * (a -> num)
                in
                import (m3, a) = m in (
                    let y : a = (unfold m3).L in
                    let p : num = ((unfold m3).R m3) in
                    p
                )
                "#,
            )
            .unwrap(),
            *parse(
                r#"
                let m : exists b . rec a . b * (a -> num) =
                    export (fold (0, fun (o : rec a . num * (a -> num)) -> (unfold o).L)
                            as rec a . num * (a -> num))
                    without num as exists b . rec a . b * (a -> num)
                in
                import (m2, a) = m in (
                    let x : a = (unfold m2).L in
                    let n : num = ((unfold m2).R m2) in
                    n
                )
                "#,
            )
            .unwrap()
        ));
    }

    #[test]
    fn ty_aequiv() {
        assert!(Type::alpha_equiv(
            *parse_type("exists c . rec d . c * (d -> num)").unwrap(),
            *parse_type("exists b . rec a . b * (a -> num)").unwrap()
        ));
        assert!(!Type::alpha_equiv(
            *parse_type("exists b . rec a . b * (a -> num)").unwrap(),
            *parse_type("exists b . rec a . b * (a -> unit)").unwrap()
        ));
        assert!(Type::alpha_equiv(
            *parse_type("exists b . rec a . b * (a -> num)").unwrap(),
            parse_type("exists b . rec a . b * (a -> num)")
                .unwrap()
                .substitute(Variable::from("a"), Type::Var(Variable::from("c")))
        ));
    }
}
