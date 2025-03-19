#[cfg(test)]
mod tests {
    use interpreter::parser::parse;
    use interpreter::typecheck::type_check;

    #[test]
    fn arithmetic() {
        let add = parse("1+()").unwrap();
        assert!(type_check(&add).is_err());
        let sub = parse("()-()").unwrap();
        assert!(type_check(&sub).is_err());
        let mul = parse("1*(1,2)").unwrap();
        assert!(type_check(&mul).is_err());
        let div = parse("(inj 1=L as num+num)/1").unwrap();
        assert!(type_check(&div).is_err());
    }

    #[test]
    fn conditionals() {
        let or = parse("true || 1").unwrap();
        assert!(type_check(&or).is_err());
        let and = parse("() && true").unwrap();
        assert!(type_check(&and).is_err());
        let if_diff = parse("if true then 1 else ()").unwrap();
        assert!(type_check(&if_diff).is_err());
        let if_cond = parse("if 0 then 1 else 2").unwrap();
        assert!(type_check(&if_cond).is_err());
        let eq = parse("1==()").unwrap();
        assert!(type_check(&eq).is_err());
        let lt = parse("1<(2,3)").unwrap();
        assert!(type_check(&lt).is_err());
        let gt = parse("(fun (x:num+num) -> x)>1").unwrap();
        assert!(type_check(&gt).is_err());
    }

    #[test]
    fn functions() {
        let free_var = parse("x").unwrap();
        assert!(type_check(&free_var).is_err());
        let app_ty = parse("(fun (x:num+num) -> x) 1").unwrap();
        assert!(type_check(&app_ty).is_err());
        let app_nonfun = parse("1 ()").unwrap();
        assert!(type_check(&app_nonfun).is_err());
    }

    #[test]
    fn adt() {
        let proj = parse("1.L").unwrap();
        assert!(type_check(&proj).is_err());
        let inj = parse("inj ()=L as num+num").unwrap();
        assert!(type_check(&inj).is_err());
        let case = parse("case () {L(l)->l+1|R(r)->3*r}").unwrap();
        assert!(type_check(&case).is_err());
        let case_arm = parse("case (inj 1=L as num+(num*num)) {L(l)->l+1|R(r)->3*r}").unwrap();
        assert!(type_check(&case_arm).is_err());
    }

    #[test]
    fn fixpoints() {
        let fix = parse("letrec f : num = 5 in f 1").unwrap();
        assert!(type_check(&fix).is_err());
    }
}
