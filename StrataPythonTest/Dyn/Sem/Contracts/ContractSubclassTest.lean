/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
import StrataDyn.DSL
import StrataDyn.DDMRead
import StrataDyn.Exec.Run
meta import StrataPython.Dyn.Sem.Table
meta import StrataDyn.DDMRead
meta import StrataDyn.Exec.Run

set_option autoImplicit false

/-!
# The contract operations on instances of subclasses of built-in classes

A test environment, `PyR`, adds one instruction, `pr.hcase(i)`, whose rule builds instances of
subclasses of `str`, `tuple`, `dict`, `int` and `bytes` by hand and applies the case `i` of a
contract operation to them, so that the cases don't depend on which of these classes' `__new__`
the semantics models for a subclass.  Each operation
that asks for exactly a `str`, a tuple or a dict ignores them, as its docstring says.
-/

namespace StrataPython.Dyn.Sem.ContractSubclassTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn.Sem

public environment PyR extends Py where
  namespace pr
  open py
  insn hcase (i : base.Int) (^err (exc : Value)) : Value
  end pr

#dyn_types PyR

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- A class `name` with the single built-in base `base`. -/
public def subclassOf (name : String) (base : Builtin) : PyM σ .writes false Value := do
  PyPure.allocObj (.builtin .type) (.cls
    { name, qualname := name, «module» := "m", bases := #[.builtin base],
      mroTail := #[.builtin base, .builtin .object], ns := ← PyPure.allocDict,
      solidBase := .builtin base.info.solidBase })

/-- A `bool`. -/
public def bv (b : Bool) : Value := .bool b

/-- Case `i`: a contract operation applied to instances of subclasses of built-in classes. -/
public def hcaseM (i : Int) : PyM σ .writes false Value := do
  let S ← subclassOf "S" .str
  let T ← subclassOf "T" .tuple
  let D ← subclassOf "D" .dict
  let I ← subclassOf "I" .int
  let sx ← PyReads.allocInstance S (.str (.ofString "x")) #[] #[]
  let t12 ← PyReads.allocInstance T (.tuple #[.int 1, .int 2]) #[] #[]
  let ix ← PyReads.allocInstance I (.int 1) #[] #[]
  -- {S("x"): 1, "y": 2}
  let kw ← PyPure.allocDict
  PyWrites.dictSet kw sx (.int 1) (some (← Proto.hash sx)) fun _ => pure false
  PyWrites.dictSet kw (.ofString "y") (.int 2) none fun _ => pure false
  -- D(x=1)
  let dx ← PyReads.allocInstance D .dict #[] #[]
  PyWrites.dictSet dx (.ofString "x") (.int 1) none fun _ => pure false
  let empty ← PyPure.allocDict
  match i with
  | 0 => Contracts.argOf kw kw (-1) "x" (.int 7)              -- S("x") key ignored → 7
  | 1 => Contracts.argOf t12 empty 0 "a" (.int 7)              -- tuple subclass args ignored → 7
  | 2 => Contracts.argOf (.tuple #[]) dx (-1) "x" (.int 7)     -- dict subclass kwargs ignored → 7
  | 3 => do let r ← Contracts.extraKwargs kw #["x"]; pure (.int (← PyReads.dictLen r)) -- keeps S("x") and y → 2
  | 4 => do let r ← Contracts.extraKwargs dx #[]; pure (.int (← PyReads.dictLen r))  -- dict subclass → 0
  | 5 => bv <$> Contracts.bindsTo (.tuple #[]) kw 0 true #[]   -- non-exact-str key → False
  | 6 => bv <$> Contracts.bindsTo t12 empty 2 false #["a", "b"] -- tuple subclass → False
  | 7 => bv <$> Contracts.bindsTo (.tuple #[]) dx 1 false #["x"] -- dict subclass → False
  | 8 => bv <$> Contracts.dictKeysWithin kw #["x", "y"]        -- S key → False
  | 9 => bv <$> Contracts.dictKeysWithin dx #["x"]             -- dict subclass → False
  | 10 => bv <$> Contracts.strIsOneOf sx #["x"]                -- False
  | 11 => bv <$> Contracts.intIsOneOf ix #[1]                  -- False
  | 12 => bv <$> Contracts.isImmutableScalar ix                -- False
  | 13 => bv <$> Contracts.isImmutableScalar sx                -- False
  | 14 => bv <$> Contracts.typeIsSubclass (.int 1) (← PyReads.allocInstance T (.tuple #[.builtin .int]) #[] #[])  -- tuple subclass as cls
  | 15 => bv <$> Contracts.isInstance (.int 1) (← PyReads.allocInstance T (.tuple #[.builtin .int]) #[] #[])
  | 16 => bv <$> Contracts.typeIsSubclass sx (.builtin .str)    -- True
  | 17 => Contracts.len sx                                      -- 1
  | 18 => Contracts.len t12                                     -- 2
  | 19 => Contracts.len dx                                      -- 1
  | 20 => bv <$> Contracts.reSearch "^x$" sx                   -- the stored str is searched: True
  | 21 => do                                                   -- a subclass of bytes: TypeError
    let Bs ← subclassOf "Bs" .bytes
    bv <$> Contracts.reSearch "a" (← PyReads.allocInstance Bs (.bytes #[97]) #[] #[])
  | 22 => do                                                   -- a str subclass with __buffer__: True
    let Sb ← subclassOf "Sb" .str
    let some cd ← Proto.classData? Sb | pure .none
    PyWrites.dictSet cd.ns (.ofString "__buffer__") .none none fun _ => pure false
    bv <$> Contracts.reSearch "x" (← PyReads.allocInstance Sb (.str (.ofString "x")) #[] #[])
  | 23 => do                                                   -- a bytes subclass with __buffer__: gap
    let Bb ← subclassOf "Bb" .bytes
    let some cd ← Proto.classData? Bb | pure .none
    PyWrites.dictSet cd.ns (.ofString "__buffer__") .none none fun _ => pure false
    bv <$> Contracts.reSearch "a" (← PyReads.allocInstance Bb (.bytes #[97]) #[] #[])
  | 24 => do                                                   -- a bytes subclass with
    let Br ← subclassOf "Br" .bytes                            -- __release_buffer__: gap
    let some cd ← Proto.classData? Br | pure .none
    PyWrites.dictSet cd.ns (.ofString "__release_buffer__") .none none fun _ => pure false
    bv <$> Contracts.reSearch "a" (← PyReads.allocInstance Br (.bytes #[97]) #[] #[])
  | _ => pure .none

@[dyn_sem PyR.hcase, expose] public def hcase (i : Int) (err : Target E [Value]) : Sem ε E Value :=
  runRule err #[] (hcaseM i)
end

public section
-- The compiler specializes every piece's step machines into `py.call`'s implementation, which
-- takes more than the default budget.
set_option maxHeartbeats 1000000 in
#dyn_sem_table PyRSem for PyR (world := World)
end

/-- Run `@m.main` of `text`, and print its result, its exception or its fault. -/
def runText (text : String) : IO Unit := do
  match ← Module.read PyR.env text "t.dyn" with
  | .error e => IO.println s!"read: {e}"
  | .ok m =>
    let o := runModule PyRSem.model m (.str (.str .base "m") "main") #[] 1000
    match o.result, o.read? Value with
    | .ok _, some (.obj id) =>
      match o.snapshot.world.store.get? id with
      | some { cls, payload := .exc e, .. } =>
        let args := match e.args with
          | .tuple xs => xs.toList.map fun (x : Value) => match x with | .str t => t.s | v => reprStr v
          | v => [reprStr v]
        IO.println s!"exception {reprStr cls} {args}"
      | _ => IO.println s!"object {id}"
    | .ok _, some v => IO.println (reprStr v)
    | .ok _, none => IO.println "a result that is not a value"
    | .fault f, _ => IO.println s!"fault: {repr f}"

/-- Run case `i`. -/
def hcaseRun (i : Nat) : IO Unit := runText s!"module m \{
  func @m.main() -> py.Value \{
    entry.0():
      %v.0 : py.Value = pr.hcase({i}) ^err.0()
      ret(%v.0)
    err.0(%e.0 : py.Value):
      ret(%e.0)
  }
}"

/-- info: StrataPython.Dyn.Sem.Value.int 7 -/
#guard_msgs in
#eval hcaseRun 0
/-- info: StrataPython.Dyn.Sem.Value.int 7 -/
#guard_msgs in
#eval hcaseRun 1
/-- info: StrataPython.Dyn.Sem.Value.int 7 -/
#guard_msgs in
#eval hcaseRun 2
/-- info: StrataPython.Dyn.Sem.Value.int 2 -/
#guard_msgs in
#eval hcaseRun 3
/-- info: StrataPython.Dyn.Sem.Value.int 0 -/
#guard_msgs in
#eval hcaseRun 4
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 5
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 6
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 7
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 8
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 9
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 10
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 11
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 12
/-- info: StrataPython.Dyn.Sem.Value.bool false -/
#guard_msgs in
#eval hcaseRun 13
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.typeIsSubclass: an instance of a subclass of tuple is not modelled" -/
#guard_msgs in
#eval hcaseRun 14
/-- info: fault: Strata.Dyn.Exec.Fault.gap "isinstance with a second argument that is an object, not a class" -/
#guard_msgs in
#eval hcaseRun 15
/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval hcaseRun 16
/-- info: StrataPython.Dyn.Sem.Value.int 1 -/
#guard_msgs in
#eval hcaseRun 17
/-- info: StrataPython.Dyn.Sem.Value.int 2 -/
#guard_msgs in
#eval hcaseRun 18
/-- info: StrataPython.Dyn.Sem.Value.int 1 -/
#guard_msgs in
#eval hcaseRun 19
/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval hcaseRun 20
/-- info: exception StrataPython.Dyn.Sem.Value.builtin (StrataPython.Dyn.Sem.Builtin.TypeError) [cannot use a string pattern on a bytes-like object] -/
#guard_msgs in
#eval hcaseRun 21
/-- info: StrataPython.Dyn.Sem.Value.bool true -/
#guard_msgs in
#eval hcaseRun 22
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.reSearch: a subject whose class defines __buffer__ is not modelled" -/
#guard_msgs in
#eval hcaseRun 23
/-- info: fault: Strata.Dyn.Exec.Fault.gap "py.reSearch: a subject whose class defines __release_buffer__ is not modelled" -/
#guard_msgs in
#eval hcaseRun 24
end StrataPython.Dyn.Sem.ContractSubclassTest
