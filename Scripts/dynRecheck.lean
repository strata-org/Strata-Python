/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataDyn.Exec.Recheck

-- Not a `module` file: `main` calls the check, which is `meta` code in StrataDyn.

/-! `dynRecheck ROOT SRC MODULE [--without M | --ending N]`: the findings of the tables of the
built module `MODULE`, checked again with all compiled code in view, one per line
(`recheckOneModule`).  `ROOT` holds the build's `.olean` files, and `SRC` the sources.
`--without M` leaves `M` out of the modules found to hold a table, so a test can see that the
recheck reports such a module; `--ending N` adds `N` to the trusted library loops whose loops the
recheck prints (the tables are still checked with `endingPartials`), so a test can see that it
reports an entry that reaches no loop. -/

unsafe def main (args : List String) : IO UInt32 := do
  let (root, src, m, without, extra) ← match args with
    | [root, src, m] => pure (root, src, m, none, [])
    | [root, src, m, "--without", w] => pure (root, src, m, some w.toName, [])
    | [root, src, m, "--ending", n] => pure (root, src, m, none, [n.toName])
    | _ => IO.eprintln "usage: dynRecheck ROOT SRC MODULE [--without M | --ending N]"; return 2
  Lean.initSearchPath (← Lean.findSysroot) [root]
  -- Lean imports a module with its extensions only when initializers may run.
  Lean.enableInitializersExecution
  let (pkg, mods) ← Strata.Dyn.Exec.tableModules root src
  let mods := mods.filter (some · != without)
  for f in ← Strata.Dyn.Exec.recheckOneModule m.toName pkg mods
      (Strata.Dyn.Exec.endingPartials ++ extra) do
    IO.println f
  return 0
