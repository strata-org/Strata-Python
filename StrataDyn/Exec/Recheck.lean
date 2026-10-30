/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command
public import StrataDyn.Exec.Rules

/-!
# Checking every built table again, with every module's private declarations in view

`#dyn_sem_table` checks that its rules run as they are written, but in a `module` file it can't
see another module's private declarations, nor a module that another module imports only
privately, nor another module's `@[init]` attribute.  So it cannot see a swap whose lemma is
private there, or in such a module, nor a definition whose run-time value comes from an
initializer there.

`recheckTableModules root src exe` finds the built modules that hold a table: the `.olean` files
under `root` (the build's `.lake/build/lib/lean`) whose source file exists under `src`, read
without importing them.  Then it checks each such module in its own process of `exe`, the
`dynRecheck` executable, which imports the module alone, at the private level, where every
module's compiled code and every body is visible, and checks that module's tables again.  One
process per module keeps the memory to one module's imports (about 1 GB), and Lean can't import
a second environment with its extensions into one process.  A module of the package that holds
a table but that the listing missed is a finding too.  It returns each finding as text.  A
package runs it after its build, as a test.

It sees only built modules: a table in a test file that is not a library module is not
rechecked, and another package checks its own build.
-/

namespace Strata.Dyn.Exec

open Lean

public meta section

/-- The module that declares `c`, if it is imported. -/
def moduleOf (env : Environment) (c : Lean.Name) : Option Lean.Name :=
  env.getModuleIdxFor? c >>= (env.header.moduleNames[·.toNat]?)

/-- The package's built modules under `root`: each `.olean` file whose source file, relative to
`src`, exists; and those of them whose module data has a `tableExt` entry. -/
def tableModules (root src : System.FilePath) : IO (Lean.NameSet × Array Lean.Name) := do
  let mut pkg : Lean.NameSet := {}
  let mut out := #[]
  for f in ← root.walkDir do
    unless f.extension == some "olean" do continue
    let rel := (f.toString.drop (root.toString.length + 1)).dropEnd ".olean".length
    unless ← (src / s!"{rel}.lean").pathExists do continue
    let m := (rel.toString.replace "/" ".").toName
    pkg := pkg.insert m
    let (d, _) ← readModuleData f
    if d.entries.any fun (n, es) => n == ``tableExt && !es.isEmpty then
      out := out.push m
  return (pkg, out.qsort (·.lt ·))

/-- The tables that module `m` of the environment declares, checked again in that environment,
as text, the package's modules (`pkg`) of the environment that hold a table but are not in
`found`, and for each entry of `ending`, the library loops whose loops it prints (the tables are
checked with `endingPartials`), the first loop it reaches, or that it reaches none. -/
def recheckModule (m : Lean.Name) (pkg : Lean.NameSet) (found : Array Lean.Name)
    (ending : List Lean.Name := endingPartials) : MetaM (Array String) := do
  let env ← getEnv
  let mut out := #[]
  let mut missed : Lean.NameSet := {}
  for t in tableExt.getState env do
    let some tm := moduleOf env t.table
      | out := out.push s!"the table {t.ns} belongs to no imported module"
        continue
    if tm == m then
      let emitted : Lean.NameSet := t.emitted.foldl (·.insert ·) {}
      if let some why ← notAsProved t.table
          m!"the table {t.ns}, through {privateToUserName t.table}," (emitted.contains ·) then
        out := out.push (← why.toString)
    else if pkg.contains tm && !found.contains tm && !missed.contains tm then
      missed := missed.insert tm
      out := out.push s!"{tm} holds a table, but the recheck did not find it"
  -- Here every body is visible: each trusted library loop must still reach a loop, and its first
  -- loop is printed, so that a test pins it.
  for n in ending do
    match ← findNotAsProved n m!"{.ofConstName n}" (ending := []) with
    | some f =>
      if f.kind == .loop then
        out := out.push s!"the trusted library loop {n} reaches {f.reached} \
          ({" → ".intercalate (f.path.toList.map toString)})"
      else
        out := out.push s!"endingPartials lists {n}, which reaches no loop but another finding: \
          {← f.msg.toString}"
    | none =>
      out := out.push s!"endingPartials lists {n}, but it reaches no loop that the check rejects: \
        remove it"
  return out

/-- The findings of module `m`'s tables, checked again in an environment that imports `m` alone,
at the private level, and of the package's modules there that hold a table but are not in
`mods`.  It keeps that environment until the process ends, so a run checks one module.  The caller must
have enabled initializers (`enableInitializersExecution`). -/
def recheckOneModule (m : Lean.Name) (pkg : Lean.NameSet) (mods : Array Lean.Name)
    (ending : List Lean.Name := endingPartials) : IO (Array String) := do
  let env ← importModules #[{ module := m }] {} (loadExts := true) (level := .private)
  let (found, _) ← (recheckModule m pkg mods ending |>.run' {} {}).toIO
    { fileName := s!"<recheck {m}>", fileMap := default } { env }
  return found

/-- Every finding of the tables of the built modules under `root`, whose sources are under
`src`, checked again with all compiled code in view, sorted.  Each module is checked in its own
process of `exe`, the `dynRecheck` executable, which finds its imports through the `LEAN_PATH`
it inherits; a run that fails is an error. -/
def recheckTableModules (root src exe : System.FilePath) : IO (Array String) := do
  let (_, mods) ← tableModules root src
  let mut out := #[]
  for m in mods do
    let r ← IO.Process.output
      { cmd := exe.toString, args := #[root.toString, src.toString, m.toString] }
    unless r.exitCode == 0 do
      throw <| IO.userError s!"dynRecheck {m} failed ({r.exitCode}):\n{r.stderr}"
    out := out ++ (r.stdout.splitOn "\n").toArray.filter (· != "")
  return (out.qsort (· < ·)).toList.eraseDups.toArray

end

end Strata.Dyn.Exec
