/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Store
public import StrataPython.Dyn.Sem.Format

set_option autoImplicit false

/-!
# The text of an exception

`excStr` is `str(e)` for an exception of a built-in class whose text is `BaseException`'s or
`KeyError`'s, for arguments that are immediates, and `none` for other arguments; the full `str`
of an exception, through its arguments' own `str` and `repr`, is `Proto/Repr.lean`'s.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- `repr(v)` for an immediate whose `repr` needs no protocol. -/
def immRepr : Value → Option String
  | .none => some "None"
  | .bool b => some (if b then "True" else "False")
  | .int i => (Format.intRepr i).toOption
  | .float bits => some (Format.floatRepr bits)
  | .str s => some (Format.strRepr s.s)
  | .tuple xs => do
    let parts ← xs.attach.toList.mapM fun ⟨x, _⟩ => immRepr x
    pure ("(" ++ ", ".intercalate parts ++ (if parts.length == 1 then ",)" else ")"))
  | _ => none

/-- `str(v)` for an immediate whose `str` needs no protocol. -/
def immStr : Value → Option String
  | .str s => some s.s
  | v => immRepr v

/-- Whether the built-in class `b` gets its `__str__` from a class whose text is not
`BaseException`'s: `OSError`, `SyntaxError`, `BaseExceptionGroup` and the three Unicode errors.
`AttributeError`, `ImportError`, `KeyError` and `NameError` also define `__str__`; for arguments
given by position, all but `KeyError`'s agree with `BaseException`'s. -/
def ownStr (b : Builtin) : Bool :=
  b.info.mro.any fun c => [Builtin.OSError, .SyntaxError, .BaseExceptionGroup,
    .UnicodeDecodeError, .UnicodeEncodeError, .UnicodeTranslateError].contains c

/-- `str(e)` for an exception of the built-in class `cls` with the arguments `args`: the empty
string for no argument, `str` of a single argument (`repr` of it for `KeyError`), and `repr` of
the tuple otherwise; `none` for a class whose `__str__` gives another text (`ownStr`). -/
def excStr (cls : Value) (args : Value) : Option String :=
  match cls with
  | .builtin b => if ownStr b then none else
    match args with
    | .tuple #[] => some ""
    | .tuple #[a] => if b == .KeyError then immRepr a else immStr a
    | .tuple _ => immRepr args
    | _ => none
  | _ => none

end

end StrataPython.Dyn.Sem
