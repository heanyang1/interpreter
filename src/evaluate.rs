use crate::{
    ast::*,
    ast_util::Symbol,
    dotgen::to_dot,
    flags::Verbosity,
};

pub enum Outcome {
    Step(Expr),
    Value,
}

/// The `|->` operator
fn fall_through(
    (e, hole): (&Expr, impl FnOnce(Expr) -> Expr),
    next: impl FnOnce() -> Outcome,
) -> Outcome {
    match try_step(e) {
        Outcome::Step(next_e) => Outcome::Step(hole(next_e)),
        Outcome::Value => next(),
    }
}

/// Syntax sugar for `fall_through`
macro_rules! free_fall {
  // Base case
  ($e:expr) => { $e };

  // Recursive case
  ($e:expr, $($rest:tt)*) => {
    fall_through($e, ||{ free_fall!($($rest)*) })
  };
}

macro_rules! eval_left {
    ($binop:ident, $left:ident, $right:ident, $op:tt) => {
        ($left, |l| Expr::$op {
            $binop: $binop.clone(),
            left: Box::new(l),
            right: $right.clone(),
        })
    };
}

macro_rules! eval_right {
    ($binop:ident, $left:ident, $right:ident, $op:tt) => {
        ($right, |r| Expr::$op {
            $binop: $binop.clone(),
            left: $left.clone(),
            right: Box::new(r),
        })
    };
}

static mut COUNTER: u32 = 0;

unsafe fn inc() -> u32 {
    unsafe {
        COUNTER += 1;
        COUNTER
    }
}

pub fn eval(e: &Expr, verbose: Verbosity) -> Expr {
    match try_step(e) {
        Outcome::Step(e_stepped) => {
            match verbose {
                Verbosity::VeryVerbose => println!("stepped: {e:#?} |-> {e_stepped:#?}"),
                Verbosity::VerboseAST => {
                    println!("{}", to_dot(e, Some(format!("step{}", unsafe { inc() }))))
                }
                _ => (),
            }
            eval(&e_stepped, verbose)
        }
        Outcome::Value => e.clone(),
    }
}

pub fn try_step(expr: &Expr) -> Outcome {
    match expr {
        Expr::Lam { .. }
        | Expr::Num { .. }
        | Expr::True
        | Expr::False
        | Expr::Pair { .. }
        | Expr::Unit
        | Expr::Inject { .. }
        | Expr::TyLam { .. }
        | Expr::Export { .. }
        | Expr::Fold { .. } => Outcome::Value,
        // 1. arithmetic
        Expr::Addop { binop, left, right } => free_fall!(
            eval_left!(binop, left, right, Addop),
            eval_right!(binop, left, right, Addop),
            if let (Expr::Num(l), Expr::Num(r)) = (left.as_ref(), right.as_ref()) {
                match binop {
                    AddOp::Add => Outcome::Step(Expr::Num(l + r)),
                    AddOp::Sub => Outcome::Step(Expr::Num(l - r)),
                }
            } else {
                unreachable!()
            }
        ),
        Expr::Mulop { binop, left, right } => free_fall!(
            eval_left!(binop, left, right, Mulop),
            eval_right!(binop, left, right, Mulop),
            if let (Expr::Num(l), Expr::Num(r)) = (left.as_ref(), right.as_ref()) {
                match binop {
                    MulOp::Mul => Outcome::Step(Expr::Num(l * r)),
                    MulOp::Div => Outcome::Step(Expr::Num(l / r)),
                }
            } else {
                unreachable!()
            }
        ),
        // 2. conditionals
        Expr::If { cond, then_, else_ } => free_fall!(
            (cond, |c| Expr::If {
                cond: Box::new(c),
                then_: then_.clone(),
                else_: else_.clone(),
            }),
            match cond.as_ref() {
                Expr::True => Outcome::Step(*then_.clone()),
                Expr::False => Outcome::Step(*else_.clone()),
                _ => unreachable!(),
            }
        ),
        Expr::Relop { relop, left, right } => free_fall!(
            eval_left!(relop, left, right, Relop),
            eval_right!(relop, left, right, Relop),
            if let (Expr::Num(l), Expr::Num(r)) = (left.as_ref(), right.as_ref()) {
                let result = match relop {
                    RelOp::Lt => l < r,
                    RelOp::Gt => l > r,
                    RelOp::Eq => l == r,
                };
                match result {
                    true => Outcome::Step(Expr::True),
                    false => Outcome::Step(Expr::False),
                }
            } else {
                unreachable!()
            }
        ),
        Expr::And { left, right } => free_fall!(
            (left, |l| Expr::And {
                left: Box::new(l),
                right: right.clone(),
            }),
            (right, |r| Expr::And {
                left: left.clone(),
                right: Box::new(r),
            }),
            match (left.as_ref(), right.as_ref()) {
                (Expr::True, Expr::True) => Outcome::Step(Expr::True),
                (Expr::False, _) => Outcome::Step(Expr::False),
                (Expr::True, Expr::False) => Outcome::Step(Expr::False),
                _ => unreachable!("{left:?} {right:?}"),
            }
        ),
        Expr::Or { left, right } => free_fall!(
            (left, |l| Expr::Or {
                left: Box::new(l),
                right: right.clone(),
            }),
            (right, |r| Expr::Or {
                left: left.clone(),
                right: Box::new(r),
            }),
            match (left.as_ref(), right.as_ref()) {
                (Expr::False, Expr::False) => Outcome::Step(Expr::False),
                (Expr::True, _) => Outcome::Step(Expr::True),
                (Expr::False, Expr::True) => Outcome::Step(Expr::True),
                _ => unreachable!("{left:?} {right:?}"),
            }
        ),
        // 3. functions
        Expr::App { lam, arg } => free_fall!(
            (lam, |l| Expr::App {
                lam: Box::new(l),
                arg: arg.clone(),
            }),
            match lam.as_ref() {
                Expr::Lam { x, e, .. } =>
                    Outcome::Step(e.clone().substitute(x.clone(), *arg.clone())),
                _ => unreachable!(),
            }
        ),
        Expr::Var(x) => unreachable!("Free variable {x:?} should be found in type checking"),
        // 4. product types
        Expr::Project { e, d } => free_fall!(
            (e, |e| Expr::Project {
                e: Box::new(e),
                d: d.clone()
            }),
            match e.as_ref() {
                Expr::Pair { left, right } => match d {
                    Direction::Left => Outcome::Step(*left.clone()),
                    Direction::Right => Outcome::Step(*right.clone()),
                },
                _ => unreachable!(),
            }
        ),
        // 5. sum types
        Expr::Case {
            e,
            xleft,
            eleft,
            xright,
            eright,
        } => {
            free_fall!(
                (e, |e| Expr::Case {
                    e: Box::new(e),
                    xleft: xleft.clone(),
                    eleft: eleft.clone(),
                    xright: xright.clone(),
                    eright: eright.clone(),
                }),
                match e.as_ref() {
                    Expr::Inject { e, d, .. } => match d {
                        Direction::Left =>
                            Outcome::Step(eleft.clone().substitute(xleft.clone(), *e.clone())),
                        Direction::Right =>
                            Outcome::Step(eright.clone().substitute(xright.clone(), *e.clone())),
                    },
                    _ => unreachable!(),
                }
            )
        }
        // 6. fixpoints
        Expr::Fix { x, e, .. } => Outcome::Step(e.clone().substitute(x.clone(), expr.clone())),
        // 7. polymorphism
        Expr::TyApp { e, tau } => free_fall!(
            (e, |e| Expr::TyApp {
                e: Box::new(e),
                tau: tau.clone(),
            }),
            match e.as_ref() {
                Expr::TyLam { e, .. } => Outcome::Step(*e.clone()),
                _ => unreachable!("{e:?}"),
            }
        ),
        // 8. recursive types
        Expr::Unfold(e) => free_fall!(
            (e, |e| Expr::Unfold(Box::new(e))),
            match e.as_ref() {
                Expr::Fold { e, .. } => Outcome::Step(*e.clone()),
                _ => unreachable!(),
            }
        ),
        _ => todo!(),
    }
}
