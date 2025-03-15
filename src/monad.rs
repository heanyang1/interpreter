/// The `>>=` operator
pub fn bind<T1, T2, E>(a: Result<T1, E>, f: impl FnOnce(T1) -> Result<T2, E>) -> Result<T2, E> {
    match a {
        Ok(x) => f(x),
        Err(e) => Err(e),
    }
}

/// Something similar to Haskell's `do` notation
#[macro_export]
macro_rules! do_ {
  // Base case: when there's only one expression left, just return it.
  ($e:expr) => { $e };

  // Recursive case: bind the result of the first expression to the rest of the block.
  ($e:expr => $pat:pat, $($rest:tt)*) => {
    bind($e, move |$pat| do_!($($rest)*))
  };

  // Handle the case where the result of the expression is ignored.
  ($e:expr, $($rest:tt)*) => {
    bind($e, move |_| do_!($($rest)*))
  };
}
