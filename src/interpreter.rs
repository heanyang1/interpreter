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
            binop: $binop.clone(),
            left: Box::new(l),
            right: $right.clone(),
        })
    };
}

macro_rules! eval_right {
    ($binop:ident, $left:ident, $right:ident, $op:tt) => {
        ($right, |r| Expr::$op {
            binop: $binop.clone(),
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
                Ok(match binop {
                    MulOp::Mul => Outcome::Step(Expr::Num(l * r)),
                    MulOp::Div => Outcome::Step(Expr::Num(l / r)),
                })
            } else {
                unreachable!()
            }
        ),
        _ => todo!(),
    }
}
