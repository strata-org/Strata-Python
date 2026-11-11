/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Bind

set_option autoImplicit false

/-!
# The arguments of a `METH_VARARGS` method

Generic over the record, the argument errors of a built-in method that takes its arguments as
one tuple and no keywords (`METH_VARARGS`), and counts them with `PyArg_ParseTuple`
(`Python/getargs.c`), as `str.find` does, or doesn't count them, as `set.union` does. A count
error names the method without its type: "find() takes at least 1 argument (0 given)". The
error for a keyword names the type only in a method call, so it stops with a gap.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

/-- The parameters of a `METH_VARARGS` method: its name, and how many positional arguments it
takes; `varargs` for one that takes any number. -/
structure ParseTupleSig where
  name : String
  minpos : Nat := 0
  maxpos : Nat := 0
  varargs : Bool := false
  deriving Repr, Inhabited

section
variable {m : Type → Type 1} {V : Type}

/-- **The arguments `args` (a tuple) of a call with the keywords `kwargs` (a dict)**, checked
as `method_vectorcall_VARARGS` and `vgetargs1_impl` check them: the arguments, or the
`TypeError`. -/
def parseTupleArgs [PyReads m V] (sig : ParseTupleSig) (args kwargs : V) : m (Array V) := do
  -- The message names the method with its type in a method call (`str.find()`), but without it
  -- through a stored bound method (`find()`).
  if (← PyReads.dictLen kwargs) > 0 then
    PyPure.gap s!"the message of a keyword argument to {sig.name} depends on how it is called"
  let xs ← tupleItems args
  let n := xs.size
  if sig.varargs || (sig.minpos ≤ n && n ≤ sig.maxpos) then return xs
  let k := if n < sig.minpos then sig.minpos else sig.maxpos
  let q := if sig.minpos == sig.maxpos then "exactly"
    else if n < sig.minpos then "at least" else "at most"
  raiseBuiltin "TypeError" s!"{sig.name}() takes {q} {k} argument{plural k} ({n} given)"

end

end

end StrataPython.Dyn.Sem.Library
