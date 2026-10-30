/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.DDM
public import StrataDyn.WF
public import StrataPython.Dyn.Translate
import all StrataPython.Dyn.Translate
import StrataDyn.Env.WF
-- The translator and the checker both run as compiled code below.
meta import StrataDyn.DDM
meta import StrataDyn.WF
meta import StrataPython.Dyn.Translate
meta import StrataPythonTest.Dyn.TestUtil

set_option autoImplicit false

/-!
# The translator's output is well formed

Python ASTs written by hand, so these run without Python.  `StrataPythonTestExtra/
DynTranslateTest.lean` checks the corpus.

    x = 1
    def f(a):
        while a < x:
            a = a + 1
        return a
    f(2)
    g = 1j
-/

namespace StrataPython.Dyn.PyTranslateTest

open Strata.Dyn
open StrataPython.Dyn.PyTranslate
open StrataPython (stmt expr)
open StrataDDM (SourceRange)

private def none' : SourceRange := .none

private def load (s : String) : expr SourceRange := .Name none' ⟨none', s⟩ (.Load none')

private def store (s : String) : expr SourceRange := .Name none' ⟨none', s⟩ (.Store none')

private def int (n : Nat) : expr SourceRange :=
  .Constant none' (.ConPos none' ⟨none', n⟩) ⟨none', none⟩

private def assign (x : String) (e : expr SourceRange) : stmt SourceRange :=
  .Assign none' ⟨none', #[store x]⟩ e ⟨none', none⟩

private def fDef : stmt SourceRange :=
  let a : StrataPython.arg SourceRange := .mk_arg none' ⟨none', "a"⟩ ⟨none', none⟩ ⟨none', none⟩
  let args : StrataPython.arguments SourceRange :=
    .mk_arguments none' ⟨none', #[]⟩ ⟨none', #[a]⟩ ⟨none', none⟩ ⟨none', #[]⟩ ⟨none', #[]⟩
      ⟨none', none⟩ ⟨none', #[]⟩
  let test := .Compare none' (load "a") ⟨none', #[.Lt none']⟩ ⟨none', #[load "x"]⟩
  let loop := .While none' test ⟨none', #[assign "a" (.BinOp none' (load "a") (.Add none')
    (int 1))]⟩ ⟨none', #[]⟩
  .FunctionDef none' ⟨none', "f"⟩ args ⟨none', #[loop, .Return none' ⟨none', some (load "a")⟩]⟩
    ⟨none', #[]⟩ ⟨none', none⟩ ⟨none', none⟩ ⟨none', #[]⟩

private def call : stmt SourceRange :=
  .Expr none' (.Call none' (load "f") ⟨none', #[int 2]⟩ ⟨none', #[]⟩)

private def complexLit : stmt SourceRange :=
  assign "g" (.Constant none' (.ConComplex none' ⟨none', "0.0"⟩ ⟨none', "1.0"⟩) ⟨none', none⟩)

private def supported : Result := translate "m" #[assign "x" (int 1), fDef, call]

private def withComplex : Result := translate "m" #[assign "x" (int 1), fDef, call, complexLit]

#guard (StrataPython.Dyn.TestUtil.dottedNames supported.module.raw).isEmpty

#guard supported.ok

-- The module body, then `f`.
#guard supported.module.raw.funcs.map (nameText ·.name) = #["m.<module>", "m.f"]

-- A rejected complex literal is a diagnostic.
#guard withComplex.diagnostics.map (·.message) = #["complex literal is not supported"]

/-- `a, b += 1`, which CPython's parser rejects, built by hand: the translator reports an
internal error rather than dropping the statement. -/
private def augTuple : Result := translate "m" #[.AugAssign none'
  (.Tuple none' ⟨none', #[store "a", store "b"]⟩ (.Store none')) (.Add none') (int 1)]

#guard augTuple.diagnostics.map (·.message) = #["a target CPython rejects"]

#guard augTuple.diagnostics.all (·.kind == .internal)

/-- `[1 for …]` with no `for` clause, which CPython's parser never produces, built by hand: an
internal error. -/
private def noGenerator : Result :=
  translate "m" #[assign "x" (.ListComp none' (int 1) ⟨none', #[]⟩)]

#guard noGenerator.diagnostics.map (·.message) = #["list comprehension without a generator"]
#guard noGenerator.diagnostics.all (·.kind == .internal)

/-! ## A function whose build fails is a stub

Each failure is an internal error, and the function is replaced by its stub, so the module
is still checked. -/

private def fName : Name := .str (.str .base "m") "f"
private def gName : Name := .str (.str .base "m") "g"

/-- Build `name`, taking one value, with `body`. -/
private def built (name : Name) (body : PyBuild.PyM SourceRange Unit) :
    {fn : Func Py.env SourceRange // fn.WF} × Array String :=
  let (f, st) := builtFunc name #[(.str .base "a", Py.Value)] none' fun _ => do
    body
    return ({} : TState)
  (f, st.diagnostics.map fun d => s!"{d.kind.text}: {d.message}")

/-- A body that closes its block twice, a misuse. -/
private def misused : PyBuild.PyM SourceRange Unit := do
  (Build.unreachable : BuildM Py.env SourceRange Unit)
  (Build.unreachable : BuildM Py.env SourceRange Unit)

/-- A body that returns a `Bool`, so the function is not well formed. -/
private def wrongResult : PyBuild.PyM SourceRange Unit := do
  (do Build.ret (← Build.emitConst (.str .base "r") (.bool true)) :
    BuildM Py.env SourceRange Unit)

/-- A body that refers to `m.g` and returns `None`. -/
private def callsG : PyBuild.PyM SourceRange Unit := do
  let _ ← (Build.emitFunc gName Base.Code : BuildM Py.env SourceRange ValId)
  PyBuild.emitReturnNone

private def printed (r : {fn : Func Py.env SourceRange // fn.WF} × Array String) : IO Unit := do
  for d in r.2 do IO.println d
  IO.println (r.1.val.format .full)

/-- info: internal error: m.g: a block finished with no block open
module m.g {
  func @m.g(%a.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%a.0 : py.Value):
      unreachable
  }
} -/
#guard_msgs in
#eval printed (built gName misused)

/-- info: internal error: m.g is not well formed
module m.g {
  func @m.g(%a.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%a.0 : py.Value):
      unreachable
  }
} -/
#guard_msgs in
#eval printed (built gName wrongResult)

/-- A body that branches on `True` to `l` and `r`, both of which jump to `j`.  `l` defines a
`None`, and `j` returns it if `outside`, where it is out of scope, as `r` also enters `j`;
otherwise `j` returns a `None` of its own. -/
private def joins (outside : Bool) : PyBuild.PyM SourceRange Unit := do
  let c ← (Build.emitConst (.str .base "c") (.bool true) : BuildM Py.env SourceRange ValId)
  let l ← (Build.freshLabel "l" : BuildM Py.env SourceRange Label)
  let r ← (Build.freshLabel "r" : BuildM Py.env SourceRange Label)
  let j ← (Build.freshLabel "j" : BuildM Py.env SourceRange Label)
  (Build.finishBlock (.branch none' c (Build.goto l) (Build.goto r)) :
    BuildM Py.env SourceRange Unit)
  (Build.startBlock l : BuildM Py.env SourceRange Unit)
  let v ← PyBuild.noneLit
  (Build.finishBlock (.jump none' (Build.goto j)) : BuildM Py.env SourceRange Unit)
  (Build.startBlock r : BuildM Py.env SourceRange Unit)
  (Build.finishBlock (.jump none' (Build.goto j)) : BuildM Py.env SourceRange Unit)
  (Build.startBlock j : BuildM Py.env SourceRange Unit)
  if outside then PyBuild.emitReturn v else PyBuild.emitReturnNone

-- A use out of scope is an internal error that says why.
/-- info: internal error: m.g is not well formed: `%none.0` (defined in `l.0`) is used in `j.0`, reachable via `entry.0 → r.0 → j.0` without it -/
#guard_msgs in
#eval show IO Unit from for d in (built gName (joins true)).2 do IO.println d

-- Its twin builds.
#guard (built gName (joins false)).2.isEmpty

-- A body without a failure is kept as built.
#guard (built gName PyBuild.emitReturnNone).2.isEmpty
#guard (built gName PyBuild.emitReturnNone).1.val.blocks.size == 1

-- A caller of a stub gives a checked module, with no further diagnostic.
#guard (assemble (.str .base "m") #[(built fName callsG).1, (built gName wrongResult).1]
  none').2.isEmpty
#guard (assemble (.str .base "m") #[(built fName callsG).1, (built gName wrongResult).1]
  none').1.raw.funcs.map (nameText ·.name) = #["m.f", "m.g"]

-- A function named twice is an internal error, and the first is kept.
#guard (assemble (.str .base "m") #[(built gName PyBuild.emitReturnNone).1,
  (built gName wrongResult).1] none').2.map (·.message) = #["m.g is emitted twice"]
#guard (assemble (.str .base "m") #[(built gName PyBuild.emitReturnNone).1,
  (built gName wrongResult).1] none').1.raw.funcs.map (·.blocks.size) = #[1]

-- A reference to a function the module lacks is an internal error, and the module is empty.
#guard (assemble (.str .base "m") #[(built fName callsG).1] none').2.map (·.message) =
  #["m references a function it does not define: m.f"]
#guard (assemble (.str .base "m") #[(built fName callsG).1] none').1.raw.funcs.isEmpty

/-- The context of a module made of `fDef`, and the job that emits `f`. -/
private def fCtx : Ctx :=
  let table := PyScope.analyze #[fDef]
  { table, module := "m", moduleName := .str .base "m", scope := 0, cur := table.scopes[0]! }

private def fJob : FuncJob :=
  match fDef with
  | .FunctionDef _ _ args ⟨_, body⟩ .. =>
    { name := (Name.base.str "m").str "f", scope := 1, cur := fCtx.table.scopes[1]!,
      args := some args, body, range := none', stub := none }
  | _ => { name := .base, scope := 1, cur := fCtx.table.scopes[1]!, args := none, body := #[],
           range := none', stub := none }

/-- `f` queued twice: emitted once, and the second job is an internal error. -/
private def queuedTwice :=
  emitQueued fCtx {} (by simp) { pending := #[fJob, fJob] } 0 #[]

#guard queuedTwice.1.map (nameText ·.val.name) = #["m.f"]
#guard queuedTwice.2.diagnostics.map (·.message) = #["m.f is queued twice"]

/-- A job for a scope the table lacks is an internal error, and is skipped. -/
private def noScope :=
  emitQueued fCtx {} (by simp) { pending := #[{ fJob with scope := 99 }] } 0 #[]

#guard noScope.1.isEmpty
#guard noScope.2.diagnostics.map (·.message) = #["m.f has no scope in the table"]

private def noArgs : StrataPython.arguments SourceRange :=
  .mk_arguments none' ⟨none', #[]⟩ ⟨none', #[]⟩ ⟨none', none⟩ ⟨none', #[]⟩ ⟨none', #[]⟩
    ⟨none', none⟩ ⟨none', #[]⟩

private def mkDef (n : String) (body : Array (stmt SourceRange)) : stmt SourceRange :=
  .FunctionDef none' ⟨none', n⟩ noArgs ⟨none', body⟩ ⟨none', #[]⟩ ⟨none', none⟩ ⟨none', none⟩
    ⟨none', #[]⟩

/-- Two `def`s at the same range share one scope (`childScope?` finds a child by its range),
which no parsed program has.  The second is queued twice, so the translation fails visibly:
it is not `g` translated with `f`'s scope. -/
private def sameRange : Result := translate "m" #[
  mkDef "f" #[assign "x" (load "y"), .Return none' ⟨none', some (load "x")⟩],
  mkDef "g" #[.Return none' ⟨none', some (load "x")⟩]]

#guard sameRange.diagnostics.map (·.message) =
  #["m.f.1 is queued twice", "m references a function it does not define: m.<module>"]
#guard sameRange.module.raw.funcs.isEmpty

end StrataPython.Dyn.PyTranslateTest
