#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::evaluate::eval;
    use interpreter::flags::{Mode, OutputMode};
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn numbers() {
        let one = parse("1").unwrap();
        assert_eq!(eval(&one, Mode::Eval, OutputMode::Full), Expr::Num(1));
        assert_eq!(type_check(&one).unwrap(), Type::Num);
        let num = parse("1234567").unwrap();
        assert_eq!(eval(&num, Mode::Eval, OutputMode::Full), Expr::Num(1234567));
        assert_eq!(type_check(&num).unwrap(), Type::Num);
        let zero = parse("0").unwrap();
        assert_eq!(eval(&zero, Mode::Eval, OutputMode::Full), Expr::Num(0));
        assert_eq!(type_check(&zero).unwrap(), Type::Num);
    }

    #[test]
    fn simple_arithmetic() {
        let add = parse("1+2").unwrap();
        assert_eq!(eval(&add, Mode::Eval, OutputMode::Full), Expr::Num(3));
        assert_eq!(type_check(&add).unwrap(), Type::Num);
        let sub = parse("1-2").unwrap();
        assert_eq!(eval(&sub, Mode::Eval, OutputMode::Full), Expr::Num(-1));
        assert_eq!(type_check(&sub).unwrap(), Type::Num);
        let mul = parse("1*2").unwrap();
        assert_eq!(eval(&mul, Mode::Eval, OutputMode::Full), Expr::Num(2));
        assert_eq!(type_check(&mul).unwrap(), Type::Num);
        let div = parse("1/2").unwrap();
        assert_eq!(eval(&div, Mode::Eval, OutputMode::Full), Expr::Num(0));
        assert_eq!(type_check(&div).unwrap(), Type::Num);
    }

    #[test]
    fn complex_arithmetic() {
        let expr = parse("1 +(1   *((2-3))+4)/( 5 +6)").unwrap();
        assert_eq!(eval(&expr, Mode::Eval, OutputMode::Full), Expr::Num(1));
        assert_eq!(type_check(&expr).unwrap(), Type::Num);
    }
}
