pub trait Monad<T> {
    /// just a dirty trick to use `Monad<U>` inside `Monad<T>`
    type Output<U>: Monad<U>;

    /// The `>>=` operator
    fn bind<U>(self, f: impl FnOnce(T) -> Self::Output<U>) -> Self::Output<U>;

    // The `return` operator
    fn ret(value: T) -> Self::Output<T>;
}

impl<T, E> Monad<T> for Result<T, E> {
    type Output<U> = Result<U, E>;

    fn bind<U>(self, f: impl FnOnce(T) -> Result<U, E>) -> Result<U, E> {
        match self {
            Ok(x) => f(x),
            Err(e) => Err(e),
        }
    }

    fn ret(value: T) -> Result<T, E> {
        Ok(value)
    }
}

/// Something similar to Haskell's `do` notation
#[macro_export]
macro_rules! do_ {
  // Base case: when there's only one expression left, just return it.
  ($e:expr) => { $e };

  // Recursive case: bind the result of the first expression to the rest of the block.
  ($e:expr => $pat:pat, $($rest:tt)*) => {
    $e.bind(move |$pat| do_!($($rest)*))
  };

  // Handle the case where the result of the expression is ignored.
  ($e:expr, $($rest:tt)*) => {
    $e.bind(move |_| do_!($($rest)*))
  };
}
