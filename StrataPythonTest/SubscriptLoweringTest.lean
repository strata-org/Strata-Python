/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PythonToCore

meta section

namespace StrataPython.ToCore.Tests

open Strata
open StrataPython

/-! # V1 subscript-lowering

On the deprecated V1 direct-to-Core path, `keys[i]` and `blended_cost[k]` are
lowered by special cases keyed on the subscripted variable's name: `keys` to
`list_str_get` and `blended_cost` to `dict_str_any_get_str`. These checks verify
that lowering, comparing the result modulo source locations (`Core.eraseLocs`).
The subscript key is immaterial: the special cases match only on the base
variable's name. Neither lowering emits a bounds or key-presence check; adding
one is a TODO tracked as a follow-up.
-/

private def sr : SourceRange := default

private def loadName (name : String) : expr SourceRange :=
  .Name sr { val := name, ann := sr } (.Load sr)

private def intLiteral (value : Nat) : expr SourceRange :=
  .Constant sr (.ConPos sr { val := value, ann := sr }) { val := none, ann := sr }

private def subscript (base : String) (key : expr SourceRange) : expr SourceRange :=
  .Subscript sr (loadName base) key (.Load sr)

private def ctx : TranslationContext := default

/-! `keys[0]` lowers to `list_str_get(keys, 0)`, up to source locations. -/
#guard
  Core.eraseLocs (PyExprToCore ctx (subscript "keys" (intLiteral 0))).expr ==
    Core.eraseLocs
      (.app Core.valueLoc
        (.app Core.valueLoc (.op Core.valueLoc "list_str_get" none)
          (.fvar Core.valueLoc "keys" none))
        (.intConst Core.valueLoc 0))

/-! `blended_cost[0]` lowers to `dict_str_any_get_str(blended_cost, 0)`, up to
    source locations. -/
#guard
  Core.eraseLocs (PyExprToCore ctx (subscript "blended_cost" (intLiteral 0))).expr ==
    Core.eraseLocs
      (.app Core.valueLoc
        (.app Core.valueLoc (.op Core.valueLoc "dict_str_any_get_str" none)
          (.fvar Core.valueLoc "blended_cost" none))
        (.intConst Core.valueLoc 0))

/-! A non-special base takes the bounds-checked fallback: a `subscript_bounds_check`
    assert and `dict_str_any_get`, up to source locations. -/
#guard
  let r := PyExprToCore ctx (subscript "d" (intLiteral 0))
  r.stmts.length == 1 &&
    Core.eraseLocs r.expr == Core.eraseLocs
      (.app Core.valueLoc
        (.app Core.valueLoc (.op Core.valueLoc "dict_str_any_get" none)
          (.fvar Core.valueLoc "d" none))
        (.intConst Core.valueLoc 0))

/-! The lowered subscript carries the real file and source range from the
    context: translating `keys[0]` whose subscript node spans bytes 42-58 in
    `foo.py` gives a result located at exactly that file and range — the actual
    positions, not just "some location". -/
#guard
  let subRange : SourceRange := { start := ⟨42⟩, stop := ⟨58⟩ }
  let ctxFile : TranslationContext := { (default : TranslationContext) with filePath := "foo.py" }
  let sub : expr SourceRange := .Subscript subRange (loadName "keys") (intLiteral 0) (.Load sr)
  let loc := (PyExprToCore ctxFile sub).expr.metadata
  loc.uri == some (.file "foo.py") && loc.range == subRange

end StrataPython.ToCore.Tests
