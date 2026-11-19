/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Canonical
public import StrataDyn.DDMRead
meta import StrataPython.Dyn.Canonical
meta import StrataDyn.DDMRead
import StrataDyn.Env.WF
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Reading the loop records of `py.loops`

`PyCanonical.records?` reads each function's `py.loops` attribute into loop records, and gives
`none` if an entry does not read, which `PyCanonical.runModule` reports.
-/

namespace StrataPython.Dyn.PyCanonicalTest

open Strata.Dyn StrataPython.Dyn

private def lbl (s : String) (k : Nat) : Label := ⟨.num (.str .base s) k⟩

private def rec (fs : Array (String × String)) : AttrValue :=
  .record (fs.map fun (k, v) => (.str .base k, .const (.str v)))

private def infoWith (vs : Array AttrValue) : Info :=
  { attrs := #[(Shape.key "loops", .list vs)] }

#guard PyCanonical.records? (infoWith #[rec #[("head", "head.0"), ("done", "done.0")],
    rec #[("head", "head.1"), ("done", "done.1")]]) ==
  some [{ head := lbl "head" 0, done := some (lbl "done" 0) },
        { head := lbl "head" 1, done := some (lbl "done" 1) }]
-- A record without its `done` is of a loop that control never leaves.
#guard PyCanonical.records? (infoWith #[rec #[("head", "head.0")]]) ==
  some [{ head := lbl "head" 0, done := none }]
-- A record whose label is not a string, or that has no head: the attribute does not read.
#guard PyCanonical.records? (infoWith #[.record #[(.str .base "head", .const (.str "head.1")),
    (.str .base "done", .const (.int 1))]]) == none
#guard PyCanonical.records? (infoWith #[rec #[("done", "done.3")]]) == none
-- No attribute: no records.
#guard PyCanonical.records? {} == some []
-- The shape matches `py.Completion`'s constructors.
#guard PyCanonical.shape.roles? == some { normal := 0, brk := 3, cont := 4, forwarded := [1, 2] }

/-- Read `text` in `Py.env`, and print why `PyCanonical.runModule` rejects it, or that it does
not. -/
private def failures (text : String) : IO Unit := do
  match ← Module.read Py.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match PyCanonical.runModule m with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok _ => IO.println "accepted"

-- A function whose `py.loops` attribute has a record with no head: it is reported, not dropped.
/-- info: m.f: its py.loops attribute does not read as loop records -/
#guard_msgs in
#eval failures "module m {
  func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value) {
    #[py.loops = [{done = \"done.0\"}]]

    entry.0(%args.0 : py.Value, %kwargs.0 : py.Value):
      jump ^start.0()
    start.0():
      %none.0 : py.Value = py.noneLit
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%none.0)
      ret(%ret.0)
  }
}
"

end StrataPython.Dyn.PyCanonicalTest
