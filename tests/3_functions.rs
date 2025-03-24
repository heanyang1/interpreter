#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::evaluate::eval;
    use interpreter::flags::{Mode, OutputMode};
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn simple_functions() {
        let expr1 = parse("let f : num -> num = fun (x : num) -> x + 1 in f 2").unwrap();
        assert_eq!(eval(&expr1, Mode::Eval, OutputMode::Full), Expr::Num(3));
        assert_eq!(type_check(&expr1).unwrap(), Type::Num);
        let expr2 = parse("(fun (x : num) -> x) 2").unwrap();
        assert_eq!(eval(&expr2, Mode::Eval, OutputMode::Full), Expr::Num(2));
        assert_eq!(type_check(&expr2).unwrap(), Type::Num);
    }

    #[test]
    fn shadow() {
        let expr1 = parse("let f : num -> num -> num = fun (x : num) -> fun (x : num) -> x in (f 0) 1").unwrap();
        assert_eq!(eval(&expr1, Mode::Eval, OutputMode::Full), Expr::Num(1));
        assert_eq!(type_check(&expr1).unwrap(), Type::Num);
    }
}
