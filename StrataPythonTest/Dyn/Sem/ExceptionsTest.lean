/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Exceptions
meta import StrataPython.Dyn.Sem.Exceptions

set_option autoImplicit false

/-!
# The text of an exception

`str(e)` of built-in exceptions, against CPython 3.12.15: `str(ValueError())` is `''`,
`str(ValueError('x'))` is `'x'`, `str(ValueError(1, 'a'))` is `"(1, 'a')"`, `str(KeyError('a'))`
is `"'a'"`, `str(KeyError('a', 'b'))` is `"('a', 'b')"`, `str(ValueError((1,)))` is `'(1,)'`,
`str(ValueError(None))` is `'None'` and `str(ValueError(1.5))` is `'1.5'`.
-/

namespace StrataPython.Dyn.Sem.ExceptionsTest

open StrataPython.Dyn.Sem

/-- An exception of the class `cls` with the arguments `args`. -/
def strOf (cls : Builtin) (args : Array Value) : Option String :=
  excStr (.builtin cls) (.tuple args)

#guard strOf .ValueError #[] == some ""
#guard strOf .ValueError #[.ofString "x"] == some "x"
#guard strOf .ValueError #[.int 1, .ofString "a"] == some "(1, 'a')"
#guard strOf .KeyError #[.ofString "a"] == some "'a'"
#guard strOf .KeyError #[.ofString "a", .ofString "b"] == some "('a', 'b')"
#guard strOf .ValueError #[.tuple #[.int 1]] == some "(1,)"
#guard strOf .ValueError #[.none] == some "None"
#guard strOf .ValueError #[.ofFloat 1.5] == some "1.5"
-- A class with a text of its own has none here: `str(OSError(2, "No such file"))` is
-- `[Errno 2] No such file`.
#guard strOf .OSError #[.int 2, .ofString "No such file"] == none
#guard strOf .FileNotFoundError #[.int 2, .ofString "No such file"] == none
#guard strOf .SyntaxError #[.ofString "msg"] == none
-- An argument whose `str` needs its protocol has no text yet.
#guard strOf .ValueError #[.obj 3] == none

end StrataPython.Dyn.Sem.ExceptionsTest
