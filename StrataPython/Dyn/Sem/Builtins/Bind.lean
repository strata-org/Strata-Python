/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Ops

set_option autoImplicit false

/-!
# The binder of built-ins

Generic over the record, `bindBuiltinArgs sig args kwargs` binds the arguments of a call of a
built-in to its parameters, as CPython 3.12's argument parsers do, with their `TypeError`s. A
signature (`BuiltinSig`) is data: the parameters, and the style of the messages, which is the
parser that CPython's built-in uses:

* `methO` and `noArgs`, the calling conventions `METH_O` and `METH_NOARGS`
  ("list.append() takes exactly one argument (0 given)", "str.upper() takes no arguments (1
  given)");
* `posOnly`, Argument Clinic with positional-only parameters (`_PyArg_CheckPositional`: "pop
  expected at most 1 argument, got 2");
* `keywords`, Argument Clinic with keywords (`_PyArg_UnpackKeywords`: "sum() takes at least 1
  positional argument (0 given)", "'x' is an invalid keyword argument for sum()", "round() missing
  required argument 'number' (pos 1)");
* `wrapper`, a slot wrapper such as `int.__add__` (`check_num_args`: "expected 1 argument, got
  0").

The checks of a method descriptor or slot wrapper called unbound are `Proto.descrSelf`'s.
-/

namespace StrataPython.Dyn.Sem.Builtins

open Proto

@[expose] public section

/-- The parser whose messages a built-in's argument errors have. -/
inductive BindStyle where
  | methO
  | noArgs
  | posOnly
  | keywords
  | wrapper
  deriving DecidableEq, Repr, Inhabited

/-- The parameters of a built-in and its message style. -/
structure BuiltinSig where
  /-- The name in the messages of Argument Clinic and of slot wrappers: `pop`, `sum`, `__add__`. -/
  name : String
  /-- The name in the messages of the calling conventions: `list.pop`, `sum`. -/
  qualname : String
  style : BindStyle
  /-- The number of positional-only parameters. -/
  posonly : Nat := 0
  /-- The number of required positional parameters. -/
  minpos : Nat := 0
  /-- The number of positional parameters. -/
  maxpos : Nat := 0
  /-- The names of the parameters after the positional-only ones: the positional-or-keyword
  ones, then the keyword-only ones. -/
  kwnames : Array String := #[]
  /-- The number of required keyword-only parameters. -/
  reqKwOnly : Nat := 0
  /-- Whether positional arguments beyond `maxpos` are collected (`*args`). -/
  varargs : Bool := false
  deriving Repr, Inhabited

/-- The arguments bound to a built-in's parameters: one per parameter, `none` for one not given;
and the positional arguments collected by `*args`. -/
structure BoundArgs (V : Type) where
  params : Array (Option V)
  rest : Array V := #[]

/-- `"s"` unless `n` is 1. -/
def plural (n : Nat) : String := if n == 1 then "" else "s"

section
variable {m : Type → Type 1} {V : Type}

/-- The `str` keys of the kwargs dict `kw` with their values, in order; a key that is not a `str`
raises CPython's `TypeError`, and an instance of a subclass of `str` stops with a gap. -/
def kwPairs [PyReads m V] (kw : V) : m (Array (String × V)) := do
  (← PyReads.dictEntries kw).mapM fun (k, v, _) => do
    let some s ← strArg? "a keyword" k | raiseBuiltin "TypeError" "keywords must be strings"
    pure (s, v)

/-- `_PyArg_UnpackKeywords`: positional arguments `xs` and keyword arguments `kws` bound to the
parameters of `sig`. -/
def unpackKeywords [PyReads m V] (sig : BuiltinSig) (xs : Array V) (kws : Array (String × V)) :
    m (BoundArgs V) := do
  let fname := sig.name ++ "()"
  let nargs := xs.size
  let maxargs := sig.posonly + sig.kwnames.size
  let npos := if sig.varargs then min nargs sig.maxpos else nargs
  if !sig.varargs then
    if nargs + kws.size > maxargs then
      raiseBuiltin "TypeError" s!"{fname} takes at most {maxargs} {if nargs == 0 then "keyword " else ""}argument{plural maxargs} ({nargs + kws.size} given)"
    if nargs > sig.maxpos then
      if sig.maxpos == 0 then raiseBuiltin "TypeError" s!"{fname} takes no positional arguments"
      raiseBuiltin "TypeError" s!"{fname} takes {if sig.minpos < sig.maxpos then "at most" else "exactly"} {sig.maxpos} positional argument{plural sig.maxpos} ({nargs} given)"
  let minposonly := min sig.posonly sig.minpos
  if npos < minposonly then
    raiseBuiltin "TypeError" s!"{fname} takes {if minposonly < sig.maxpos then "at least" else "exactly"} {minposonly} positional argument{plural minposonly} ({npos} given)"
  let mut params : Array (Option V) := (xs.extract 0 npos).map some
  let mut used := 0
  for i in [npos:maxargs] do
    let name := if i < sig.posonly then "" else sig.kwnames[i - sig.posonly]!
    let found := if i < sig.posonly then none else (kws.find? (·.1 == name)).map (·.2)
    match found with
    | some v =>
      params := params.push (some v)
      used := used + 1
    | none =>
      if i < sig.minpos || (sig.maxpos ≤ i && i < sig.maxpos + sig.reqKwOnly) then
        raiseBuiltin "TypeError" s!"{fname} missing required argument '{name}' (pos {i + 1})"
      params := params.push none
  if used < kws.size then
    for i in [sig.posonly:npos] do
      let name := sig.kwnames[i - sig.posonly]!
      if kws.any (·.1 == name) then
        raiseBuiltin "TypeError" s!"argument for {fname} given by name ('{name}') and position ({i + 1})"
    for (k, _) in kws do
      if !sig.kwnames.contains k then
        raiseBuiltin "TypeError" s!"'{k}' is an invalid keyword argument for {fname}"
  return { params, rest := xs.extract npos nargs }

/-- **The arguments `args` (a tuple) and `kwargs` (a dict) bound to the parameters of `sig`**,
with the `TypeError` of CPython's parser of the built-in. -/
def bindBuiltinArgs [PyReads m V] (sig : BuiltinSig) (args kwargs : V) : m (BoundArgs V) := do
  let xs ← tupleItems args
  let n := xs.size
  let hasKw := (← PyReads.dictLen kwargs) > 0
  match sig.style with
  | .methO =>
    if hasKw then raiseBuiltin "TypeError" s!"{sig.qualname}() takes no keyword arguments"
    if n != 1 then
      raiseBuiltin "TypeError" s!"{sig.qualname}() takes exactly one argument ({n} given)"
    return { params := xs.map some }
  | .noArgs =>
    if hasKw then raiseBuiltin "TypeError" s!"{sig.qualname}() takes no keyword arguments"
    if n != 0 then raiseBuiltin "TypeError" s!"{sig.qualname}() takes no arguments ({n} given)"
    return { params := #[] }
  | .wrapper =>
    if hasKw then raiseBuiltin "TypeError" s!"wrapper {sig.name}() takes no keyword arguments"
    if n != sig.maxpos then
      raiseBuiltin "TypeError" s!"expected {sig.maxpos} argument{plural sig.maxpos}, got {n}"
    return { params := xs.map some }
  | .posOnly =>
    if hasKw then raiseBuiltin "TypeError" s!"{sig.qualname}() takes no keyword arguments"
    if n < sig.minpos then
      raiseBuiltin "TypeError" s!"{sig.name} expected {if sig.minpos == sig.maxpos then "" else "at least "}{sig.minpos} argument{plural sig.minpos}, got {n}"
    if n > sig.maxpos && !sig.varargs then
      raiseBuiltin "TypeError" s!"{sig.name} expected {if sig.minpos == sig.maxpos then "" else "at most "}{sig.maxpos} argument{plural sig.maxpos}, got {n}"
    let npos := min n sig.maxpos
    return { params := (xs.extract 0 npos).map some ++ Array.replicate (sig.maxpos - npos) none,
             rest := xs.extract npos n }
  | .keywords => unpackKeywords sig xs (← kwPairs kwargs)

end

end

end StrataPython.Dyn.Sem.Builtins
