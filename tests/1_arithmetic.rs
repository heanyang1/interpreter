#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::evaluate::eval;
    use interpreter::typecheck::type_check;
    use interpreter::flags::Verbosity;
    use interpreter::parser::parse;

    #[test]
    fn numbers() {
        let one = parse("1").unwrap();
        assert_eq!(eval(&one, Verbosity::Normal), Expr::Num(1));
        assert_eq!(type_check(&one).unwrap(), Type::Num);
        let num = parse("1234567").unwrap();
        assert_eq!(eval(&num, Verbosity::Normal), Expr::Num(1234567));
        assert_eq!(type_check(&num).unwrap(), Type::Num);
        let zero = parse("0").unwrap();
        assert_eq!(eval(&zero, Verbosity::Normal), Expr::Num(0));
        assert_eq!(type_check(&zero).unwrap(), Type::Num);
    }

    #[test]
    fn simple_arithmetic() {
        let add = parse("1+2").unwrap();
        assert_eq!(eval(&add, Verbosity::Normal), Expr::Num(3));
        assert_eq!(type_check(&add).unwrap(), Type::Num);
        let sub = parse("1-2").unwrap();
        assert_eq!(eval(&sub, Verbosity::Normal), Expr::Num(-1));
        assert_eq!(type_check(&sub).unwrap(), Type::Num);
        let mul = parse("1*2").unwrap();
        assert_eq!(eval(&mul, Verbosity::Normal), Expr::Num(2));
        assert_eq!(type_check(&mul).unwrap(), Type::Num);
        let div = parse("1/2").unwrap();
        assert_eq!(eval(&div, Verbosity::Normal), Expr::Num(0));
        assert_eq!(type_check(&div).unwrap(), Type::Num);
    }

    #[test]
    fn complex_arithmetic() {
        let expr = parse("1 +(1   *((2-3))+4)/( 5 +6)").unwrap();
        assert_eq!(eval(&expr, Verbosity::Normal), Expr::Num(1));
        assert_eq!(type_check(&expr).unwrap(), Type::Num);
    }
}