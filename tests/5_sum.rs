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
        let expr1 = parse("case (inj 1=L as num+num) {L(l)->l+1|R(r)->3*r}").unwrap();
        assert_eq!(eval(&expr1, Verbosity::Normal), Expr::Num(2));
        assert_eq!(type_check(&expr1).unwrap(), Type::Num);
        let expr2 = parse(
            "let x:(num*num)+num = inj 1=R as (num*num)+num in case x {L(n)->(n.L)+1|R(n)->3*n}",
        )
        .unwrap();
        assert_eq!(eval(&expr2, Verbosity::Normal), Expr::Num(3));
        assert_eq!(type_check(&expr2).unwrap(), Type::Num);
        let expr3 = parse(
            r#"
            let x:(num->num)+num =
                (
                    inj 1 = R as (num->num)+num,
                    inj (fun (n:num) -> n+1) = L as (num->num)+num
                ).R
            in case x {L(f) -> (f 1) | R(n)->3*n}
            "#,
        )
        .unwrap();
        assert_eq!(eval(&expr3, Verbosity::Normal), Expr::Num(2));
        assert_eq!(type_check(&expr3).unwrap(), Type::Num);
    }

    #[test]
    fn aequiv() {
        let expr1 = parse("case (inj 1=L as num+num) {L(l)->l+1|R(r)->3*r}").unwrap();
        assert!(Expr::alpha_equiv(
            expr1.substitute(Variable::from("l"), Expr::Var("n".into())),
            *parse("case (inj 1=L as num+num) {L(n)->n+1|R(r_)->3*r_}").unwrap()
        ));
        assert!(Expr::alpha_equiv(
            expr1.substitute(Variable::from("r"), Expr::Var("n".into())),
            *parse("case (inj 1=L as num+num) {L(l_)->n+1|R(n)->3*n}").unwrap()
        ));

        let expr3 = parse(
            r#"
            let x:(num->num)+num =
                (
                    inj 1 = R as (num->num)+num,
                    inj (fun (n:num) -> n+1) = L as (num->num)+num
                ).R
            in case x {L(f) -> (f 1) | R(n)->3*n}
            "#,
        )
        .unwrap();
        assert!(Expr::alpha_equiv(
            expr3.substitute(Variable::from("n"), Expr::Var("t".into())),
            *expr3
        ));
    }
}
