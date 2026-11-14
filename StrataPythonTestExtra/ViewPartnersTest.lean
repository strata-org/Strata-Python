/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Python -- shake: keep
meta import StrataPython.Dyn.Sem.Proto.Ops

/-! # The built-in slots that a dict view meets

A dict view's binary operators and comparisons call the dunders of both operands' types, in
CPython's order (`binaryDunder`, `richDunder`). For a built-in `self` of a type that
`givesNotImpl`, `trySlot` doesn't call the slot, and takes it as `NotImplemented`, which CPython's
slot must then give for a view; another type's own slot stops with a gap. A view
meets a built-in `self` there only if `otherCheck` lets the pair through: an immediate value, a
list, a dict, a set, a frozenset, or an object of a type that `hashesByAddr`. This test runs
`StrataPythonTest/Dyn/Sem/view_partners.py` with CPython 3.12, which calls every binary and
comparison dunder of a sample of each built-in type with a `dict_keys` view. It fails if one of
those types has no sample, or has a dunder that doesn't give `NotImplemented`, other than the
sequence slots of `str`, `bytes`, `tuple` and `list` (`seqSlot?`) and `%` of `str` and `bytes`
(`printfFirst?`), which never reach the shortcut.
-/

namespace StrataPython.ViewPartnersTest

open StrataPython.Dyn.Sem

private meta def script : System.FilePath := "StrataPythonTest/Dyn/Sem/view_partners.py"

/-- The built-in types whose values the semantics holds as immediates, which `otherCheck` lets
through: the types of `Value`'s constructors other than `builtin` and `obj`, and the types of
the built-in constants (`Value.builtin`), such as `type`, `builtin_function_or_method` and
`_sitebuiltins.Quitter`. -/
private meta def immediateTypes : List Builtin :=
  [.«NoneType», .«NotImplementedType», .«ellipsis», .«bool», .«int», .«float», .«str», .«bytes»,
   .«tuple», .«range», .«slice», .«builtin_function_or_method», .«method_descriptor»,
   .«wrapper_descriptor», .«method-wrapper», .«classmethod_descriptor», .«getset_descriptor»,
   .«member_descriptor», .«method», .«traceback»] ++
  (Builtin.allConstants.map Builtin.typeOf).toList

/-- The built-in type whose name (`info.name`) is `t`. -/
private meta def typeNamed? (t : String) : Option Builtin :=
  Builtin.allConstants.find? fun b => b.info.kind == .type && b.info.name == t

/-- Whether `otherCheck` lets an operand of the built-in type `b` meet a view: not a view
itself, which calls its own table. -/
private meta def meetsView (b : Builtin) : Bool :=
  b.info.kind == .type &&
  (immediateTypes.contains b || [.«list», .«dict», .«set», .«frozenset»].contains b ||
    Proto.hashesByAddr b)

/-- The built-in slots that don't give `NotImplemented` for a view and never reach `trySlot`'s
shortcut. -/
private meta def allowed : List (String × String) :=
  ["str", "bytes"].flatMap (fun t => [(t, "__add__"), (t, "__mul__"), (t, "__rmul__"), (t, "__mod__")]) ++
  ["tuple", "list"].flatMap (fun t => [(t, "__add__"), (t, "__mul__"), (t, "__rmul__")])

private meta def main : IO Unit := withPython fun python => do
  let r ← IO.Process.output { cmd := python.toString, args := #["-I", script.toString] }
  if r.exitCode != 0 then
    throw <| .userError s!"{script} failed:\n{r.stderr}"
  let mut sampled : Array String := #[]
  let mut bad : Array String := #[]
  for l in r.stdout.splitOn "\n" do
    match l.splitOn " " with
    | ["SAMPLED", t] => sampled := sampled.push t
    | [t, n] =>
      if (typeNamed? t).any meetsView && !allowed.contains (t, n) then bad := bad.push l
    | _ => pure ()
  let missing := (Builtin.allConstants.filter meetsView).filter (!sampled.contains ·.info.name)
  unless missing.isEmpty do
    throw <| .userError s!"no sample in {script} for: {missing.map (·.info.name)}"
  unless bad.isEmpty do
    throw <| .userError s!"built-in slots that don't give NotImplemented for a dict view: {bad}"

#eval main

end StrataPython.ViewPartnersTest
