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
}
