/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
public import StrataDyn.DDMRead
public import StrataDyn.Exec.Run
public import StrataPython.Dyn.Sem.Run

set_option autoImplicit false

/-! # Running a small module with the Python semantics

Tests that run small modules in the IR's text with `PySem` can share two functions: `showV`
prints a value briefly, and `runMain` runs a module's `@m.main` and prints its result or its
fault.  Each test gives `runMain` its own printer for the objects that `main` returns.
-/

public section

namespace StrataPython.DynRun

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn StrataPython.Dyn.Sem

/-- A short text of a value, for the tests' output. -/
def showV : Value → String
  | .none => "None"
  | .bool b => if b then "True" else "False"
  | .int i => toString i
  | .str s => Format.strRepr s.s
  | .float bits => Format.floatRepr bits
  | .range a b c => if c == 1 then s!"range({a}, {b})" else s!"range({a}, {b}, {c})"
  | .builtin b => b.info.name
  | .tuple xs => "(" ++ ", ".intercalate (xs.attach.toList.map fun ⟨x, _⟩ => showV x) ++
      (if xs.size == 1 then ",)" else ")")
  | .obj id => s!"<object {id}>"
  | .traceback => "<traceback>"
  | v => reprStr v

/-- Run `@m.main` of the module `text` with fuel 1000, and print its result or its fault.  An
object that `main` returns is printed by `showObj`, or as `object N` when `showObj` gives
`none`. -/
def runMain (showObj : Obj Run → Option String) (text : String) : IO Unit := do
  match ← Module.read Py.env text "t.dyn" with
  | .error e => IO.println s!"read: {e}"
  | .ok m =>
    let o := runModule PySem.model m (.str (.str .base "m") "main") #[] 1000
    match o.result with
    | .ok _ => match o.read? Value with
      | some (.obj id) =>
        IO.println ((o.snapshot.world.store.get? id >>= showObj).getD s!"object {id}")
      | some v => IO.println (showV v)
      | none => IO.println "a result that is not a value"
    | .fault f => IO.println s!"fault: {repr f}"

end StrataPython.DynRun

end
