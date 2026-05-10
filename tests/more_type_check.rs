#[cfg(test)]
mod tests {
    use interpreter::ast::*;
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn typecheck_unit() {
        assert_eq!(type_check(&parse("()").unwrap()).unwrap(), Type::Unit);
    }

    #[test]
    fn typecheck_true_false() {
        assert_eq!(type_check(&parse("true").unwrap()).unwrap(), Type::Bool);
        assert_eq!(type_check(&parse("false").unwrap()).unwrap(), Type::Bool);
    }

    #[test]
    fn typecheck_numbers() {
        assert_eq!(type_check(&parse("1").unwrap()).unwrap(), Type::Num);
        assert_eq!(type_check(&parse("0").unwrap()).unwrap(), Type::Num);
    }

    #[test]
    fn typecheck_arithmetic() {
        assert_eq!(type_check(&parse("1+2").unwrap()).unwrap(), Type::Num);
        assert_eq!(type_check(&parse("1-2").unwrap()).unwrap(), Type::Num);
        assert_eq!(type_check(&parse("1*2").unwrap()).unwrap(), Type::Num);
        assert_eq!(type_check(&parse("1/2").unwrap()).unwrap(), Type::Num);
    }

    #[test]
    fn typecheck_relops() {
        assert_eq!(type_check(&parse("1<2").unwrap()).unwrap(), Type::Bool);
        assert_eq!(type_check(&parse("1>2").unwrap()).unwrap(), Type::Bool);
        assert_eq!(type_check(&parse("1==2").unwrap()).unwrap(), Type::Bool);
    }

    #[test]
    fn typecheck_and_or() {
        assert_eq!(
            type_check(&parse("true && false").unwrap()).unwrap(),
            Type::Bool
        );
        assert_eq!(
            type_check(&parse("true || false").unwrap()).unwrap(),
            Type::Bool
        );
    }

    #[test]
    fn typecheck_if() {
        assert_eq!(
            type_check(&parse("if true then 1 else 2").unwrap()).unwrap(),
            Type::Num
        );
        assert_eq!(
            type_check(&parse("if false then 1 else 2").unwrap()).unwrap(),
            Type::Num
        );
    }

    #[test]
    fn typecheck_lambda() {
        assert_eq!(
            type_check(&parse("(fun x -> x) 1").unwrap()).unwrap(),
            Type::Num
        );
        assert_eq!(
            type_check(&parse("(fun x -> 1) 2").unwrap()).unwrap(),
            Type::Num
        );
    }

    #[test]
    fn typecheck_let() {
        assert_eq!(
            type_check(&parse("let f = fun x -> x + 1 in f 2").unwrap()).unwrap(),
            Type::Num
        );
    }

    #[test]
    fn typecheck_free_var() {
        let expr = parse("let id = fun x -> x in id").unwrap();
        let ty = type_check(&expr).unwrap();
        println!("{ty}");
        match ty {
            Type::Forall { a, tau } => match *tau {
                Type::Fn { arg, ret } => {
                    assert!(matches!(*arg.clone(), Type::Var(a)));
                    assert!(matches!(*ret.clone(), Type::Var(a)));
                }
                _ => panic!("Expected function type, got {:?}", tau),
            },
            _ => panic!("Expected forall type, got {:?}", ty),
        }
    }

    #[test]
    fn typecheck_fn_const() {
        let expr = parse("fun x -> true && x").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Fn { arg, ret } => {
                assert!(matches!(*arg.clone(), Type::Bool));
                assert!(matches!(*ret.clone(), Type::Bool));
            }
            _ => panic!("Expected function type, got {:?}", ty),
        }
    }

    #[test]
    fn typecheck_fn_nested() {
        let expr = parse("let f = fun x -> fun y -> x + y in f").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Fn { arg, ret } => {
                assert!(matches!(*arg.clone(), Type::Num));
                match *ret.clone() {
                    Type::Fn { arg, ret } => {
                        assert!(matches!((*arg, *ret), (Type::Num, Type::Num)))
                    }
                    _ => panic!("Expected nested function type"),
                }
            }
            _ => panic!("Expected function type, got {:?}", ty),
        }
    }

    #[test]
    fn typecheck_fn_passing_fn() {
        let expr = parse("fun f -> (f true) < 2").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Fn { arg, ret } => {
                match *arg.clone() {
                    Type::Fn { arg, ret } => {
                        assert!(matches!((*arg, *ret), (Type::Bool, Type::Num)))
                    }
                    _ => panic!("Expected nested function type"),
                }
                assert!(matches!(*ret.clone(), Type::Bool));
            }
            _ => panic!("Expected function type, got {ty}"),
        }
    }

    #[test]
    fn typecheck_pair() {
        let expr = parse("(1, true)").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Product { left, right } => {
                assert!(matches!(*left, Type::Num));
                assert!(matches!(*right, Type::Bool));
            }
            _ => panic!("Expected product type, got {ty}"),
        }
    }

    #[test]
    fn typecheck_project_left() {
        let expr = parse("(1, true).L").unwrap();
        let ty = type_check(&expr).unwrap();
        assert_eq!(ty, Type::Num);
    }

    #[test]
    fn typecheck_project_right() {
        let expr = parse("(1, true).R").unwrap();
        let ty = type_check(&expr).unwrap();
        assert_eq!(ty, Type::Bool);
    }

    #[test]
    fn typecheck_inject_left() {
        let expr = parse("inj 1 = L").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Forall { a: _, tau } => match *tau {
                Type::Sum { left, right: _ } => {
                    assert!(matches!(*left, Type::Num));
                }
                _ => panic!("Expected sum type in forall, got {:?}", tau),
            },
            Type::Sum { left, right: _ } => {
                assert!(matches!(*left, Type::Num));
            }
            _ => panic!("Expected sum or forall type, got {ty}"),
        }
    }

    #[test]
    fn typecheck_inject_right() {
        let expr = parse("inj true = R").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Forall { a: _, tau } => match *tau {
                Type::Sum { left: _, right } => {
                    assert!(matches!(*right, Type::Bool));
                }
                _ => panic!("Expected sum type in forall, got {:?}", tau),
            },
            Type::Sum { left: _, right } => {
                assert!(matches!(*right, Type::Bool));
            }
            _ => panic!("Expected sum or forall type, got {ty}"),
        }
    }

    #[test]
    fn typecheck_case() {
        let expr = parse("case inj 1 = L { L(x) -> x | R(y) -> y }").unwrap();
        let ty = type_check(&expr).unwrap();
        assert_eq!(ty, Type::Num);
    }

    #[test]
    fn typecheck_fix() {
        let expr = parse("fix f -> 1").unwrap();
        let ty = type_check(&expr).unwrap();
        assert_eq!(ty, Type::Num);
    }

    #[test]
    fn typecheck_letrec() {
        let expr = parse("letrec f = fun x -> if x == 0 then 0 else (f (x - 1)) + 1 in f").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Fn { arg, ret } => {
                assert!(matches!(*arg, Type::Num));
                assert!(matches!(*ret, Type::Num));
            }
            _ => panic!("Expected function type, got {ty}"),
        }
    }

    #[test]
    fn typecheck_free_variable_error() {
        let expr = parse("x").unwrap();
        let result = type_check(&expr);
        assert!(result.is_err());
    }

    #[test]
    fn typecheck_polymorphism_multiple_vars() {
        let expr = parse("let id = fun x -> x in let f = fun y -> y in (id true, f 1)").unwrap();
        let ty = type_check(&expr).unwrap();
        match ty {
            Type::Product { left, right } => {
                assert!(matches!(*left, Type::Bool));
                assert!(matches!(*right, Type::Num));
            }
            _ => panic!("Expected product type, got {ty}"),
        }
    }

    #[test]
    fn typecheck_generalize() {
        let expr = parse(
            r#"
            let f = fun x -> fun y -> x y in
            let g = f (fun x -> x) in g 1
            "#,
        )
        .unwrap();
        let ty = type_check(&expr).unwrap();
        assert_eq!(ty, Type::Num)
    }
}
