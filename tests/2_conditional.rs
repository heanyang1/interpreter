#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::evaluate::eval;
    use interpreter::flags::Verbosity;
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn relop() {
        let eq = parse("1==1").unwrap();
        assert_eq!(eval(&eq, Verbosity::Normal), Expr::True);
        assert_eq!(type_check(&eq).unwrap(), Type::Bool);
        let lt = parse("1<2").unwrap();
        assert_eq!(eval(&lt, Verbosity::Normal), Expr::True);
        assert_eq!(type_check(&lt).unwrap(), Type::Bool);
        let gt = parse("2>1").unwrap();
        assert_eq!(eval(&gt, Verbosity::Normal), Expr::True);
        assert_eq!(type_check(&gt).unwrap(), Type::Bool);
        let eq_false = parse("1==2").unwrap();
        assert_eq!(eval(&eq_false, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&eq_false).unwrap(), Type::Bool);
        let lt_false = parse("2<1").unwrap();
        assert_eq!(eval(&lt_false, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&lt_false).unwrap(), Type::Bool);
        let gt_false = parse("1>2").unwrap();
        assert_eq!(eval(&gt_false, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&gt_false).unwrap(), Type::Bool);
    }

    #[test]
    fn and_or() {
        let and1 = parse("true && true").unwrap();
        assert_eq!(eval(&and1, Verbosity::Normal), Expr::True);
        assert_eq!(type_check(&and1).unwrap(), Type::Bool);
        let and2 = parse("true && false").unwrap();
        assert_eq!(eval(&and2, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&and2).unwrap(), Type::Bool);
        let and3 = parse("false && true").unwrap();
        assert_eq!(eval(&and3, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&and3).unwrap(), Type::Bool);
        let and4 = parse("false && false").unwrap();
        assert_eq!(eval(&and4, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&and4).unwrap(), Type::Bool);

        let or1 = parse("true || true").unwrap();
        assert_eq!(eval(&or1, Verbosity::Normal), Expr::True);
        assert_eq!(type_check(&or1).unwrap(), Type::Bool);
        let or2 = parse("true || false").unwrap();
        assert_eq!(eval(&or2, Verbosity::Normal), Expr::True);
        assert_eq!(type_check(&or2).unwrap(), Type::Bool);
        let or3 = parse("false || true").unwrap();
        assert_eq!(eval(&or3, Verbosity::Normal), Expr::True);
        assert_eq!(type_check(&or3).unwrap(), Type::Bool);
        let or4 = parse("false || false").unwrap();
        assert_eq!(eval(&or4, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&or4).unwrap(), Type::Bool);
    }

    #[test]
    fn ifelse() {
        let expr1 = parse("if true then 1 else 2").unwrap();
        assert_eq!(eval(&expr1, Verbosity::Normal), Expr::Num(1));
        assert_eq!(type_check(&expr1).unwrap(), Type::Num);
        let expr2 = parse("if false then 1 else 2").unwrap();
        assert_eq!(eval(&expr2, Verbosity::Normal), Expr::Num(2));
        assert_eq!(type_check(&expr2).unwrap(), Type::Num);
        let expr3 = parse("if false then 1*2 else (if true then 2+4 else 3/5)").unwrap();
        assert_eq!(eval(&expr3, Verbosity::Normal), Expr::Num(6));
        assert_eq!(type_check(&expr3).unwrap(), Type::Num);
    }

    #[test]
    fn complex_relop() {
        let expr1 = parse("(1+2>3||4>5)&&4==5").unwrap();
        assert_eq!(eval(&expr1, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&expr1).unwrap(), Type::Bool);
        let expr2 = parse("if 1<2*3 then 3==4+1 else 4>5").unwrap();
        assert_eq!(eval(&expr2, Verbosity::Normal), Expr::False);
        assert_eq!(type_check(&expr2).unwrap(), Type::Bool);
    }
}
