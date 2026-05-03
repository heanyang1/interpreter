#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::evaluate::eval;
    use interpreter::flags::{Mode, OutputMode};
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn eval_test() {
        let expr1 = parse("(1+2,3-4).L").unwrap();
        assert_eq!(eval(&expr1, Mode::Eval, OutputMode::Full), Expr::Num(3));
        assert_eq!(type_check(&expr1).unwrap(), Type::Num);
        let expr2 = parse("(1*2,3/4).R").unwrap();
        assert_eq!(eval(&expr2, Mode::Eval, OutputMode::Full), Expr::Num(0));
        assert_eq!(type_check(&expr2).unwrap(), Type::Num);
        let expr3 = parse("((1+2,3-4).L,(1*2,3/4).R).L").unwrap();
        assert_eq!(eval(&expr3, Mode::Eval, OutputMode::Full), Expr::Num(3));
        assert_eq!(type_check(&expr3).unwrap(), Type::Num);
        let expr4 = parse("(((),(1,2)),())").unwrap();
        assert_eq!(
            eval(&expr4, Mode::Eval, OutputMode::Full),
            Expr::Pair {
                left: Box::new(Expr::Pair {
                    left: Box::new(Expr::Unit),
                    right: Box::new(Expr::Pair {
                        left: Box::new(Expr::Num(1)),
                        right: Box::new(Expr::Num(2))
                    })
                }),
                right: Box::new(Expr::Unit)
            }
        );
        assert_eq!(
            type_check(&expr4).unwrap(),
            Type::Product {
                left: Box::new(Type::Product {
                    left: Box::new(Type::Unit),
                    right: Box::new(Type::Product {
                        left: Box::new(Type::Num),
                        right: Box::new(Type::Num)
                    })
                }),
                right: Box::new(Type::Unit)
            }
        );
    }
}
