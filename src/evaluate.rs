use crate::{ast::*, flags::Verbosity};

pub enum Outcome {
    Step(Expr),
    Value,
}

/// The `|->` operator
fn fall_through(
    (e, hole): (&Expr, impl FnOnce(Expr) -> Expr),
    next: impl FnOnce() -> Result<Outcome, String>,
) -> Result<Outcome, String> {
    match try_step(e) {
        Ok(Outcome::Step(next_e)) => Ok(Outcome::Step(hole(next_e))),
        Ok(Outcome::Value) => next(),
        Err(e) => Err(e),
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

pub fn eval(e: &Expr, verbose: Verbosity) -> Result<Expr, String> {
    match try_step(e) {
        Ok(Outcome::Step(e_stepped)) => {
            if verbose == Verbosity::VeryVerbose {
                println!("stepped: {e:?}|->{e_stepped:?}");
            }
            eval(&e_stepped, verbose)
        }
        Ok(Outcome::Value) => Ok(e.clone()),
        Err(e) => Err(e),
    }
}

pub fn try_step(e: &Expr) -> Result<Outcome, String> {
    match e {
        Expr::Lam { .. }
        | Expr::Num { .. }
        | Expr::True
        | Expr::False
        | Expr::Pair { .. }
        | Expr::Unit
        | Expr::Inject { .. }
        | Expr::TyLam { .. }
        | Expr::Export { .. }
        | Expr::Fold { .. } => Ok(Outcome::Value),
        // 1. arithmetic
        Expr::Addop { binop, left, right } => free_fall!(
            eval_left!(binop, left, right, Addop),
            eval_right!(binop, left, right, Addop),
            if let (Expr::Num(l), Expr::Num(r)) = (left.as_ref(), right.as_ref()) {
                Ok(match binop {
                    AddOp::Add => Outcome::Step(Expr::Num(l + r)),
                    AddOp::Sub => Outcome::Step(Expr::Num(l - r)),
                })
            } else {
                unreachable!()
            }
        ),
        Expr::Mulop { binop, left, right } => free_fall!(
            eval_left!(binop, left, right, Mulop),
            eval_right!(binop, left, right, Mulop),
            if let (Expr::Num(l), Expr::Num(r)) = (left.as_ref(), right.as_ref()) {
                match binop {
                    MulOp::Mul => Ok(Outcome::Step(Expr::Num(l * r))),
                    MulOp::Div => Ok(Outcome::Step(Expr::Num(l / r))),
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
                Expr::True => Ok(Outcome::Step(*then_.clone())),
                Expr::False => Ok(Outcome::Step(*else_.clone())),
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
                    true => Ok(Outcome::Step(Expr::True)),
                    false => Ok(Outcome::Step(Expr::False)),
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
                (Expr::True, Expr::True) => Ok(Outcome::Step(Expr::True)),
                (Expr::False, _) => Ok(Outcome::Step(Expr::False)),
                (Expr::True, Expr::False) => Ok(Outcome::Step(Expr::False)),
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
                (Expr::False, Expr::False) => Ok(Outcome::Step(Expr::False)),
                (Expr::True, _) => Ok(Outcome::Step(Expr::True)),
                (Expr::False, Expr::True) => Ok(Outcome::Step(Expr::True)),
                _ => unreachable!("{left:?} {right:?}"),
            }
        ),
        _ => todo!(),
    }
}
