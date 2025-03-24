use crate::{
    ast::*,
    ast_util::Symbol,
    flags::{format_ast, Mode, OutputMode},
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

pub fn eval(e: &Expr, mode: Mode, output: OutputMode) -> Expr {
    match try_step(e) {
        Outcome::Step(e_stepped) => {
            if mode == Mode::VeryVerbose {
                println!(
                    "{}",
                    format_ast(e, output, Some(format!("step{}", unsafe { inc() })))
                )
            }
            eval(&e_stepped, mode, output)
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
        _ => todo!(),
    }
}
