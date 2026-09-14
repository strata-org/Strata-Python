/-
CLI: pylate INPUT [--src FILE.py] [-o LOG.json]
             [--policy strict|eafp|audit] [--abort CATS] [--model CATS]
             [--sorts checked|residual] [--check-only]
       pylate --dump-rules

`INPUT` is a `.python.st.ion` Strata AST, produced by the repo's
`strata_python py_to_strata` and read through `StrataDDM.Program.fromIon`.
`Syntax/Label.lean` puts a `Pos` on every node and `Syntax/Check.lean` matches the
AST's constructors directly, so the lowering is total by construction.

It needs the Python source for line and column information, because a
`SourceRange` is a pair of byte offsets; the source comes from `--src`, or from
the `.py` beside the `.python.st.ion`.

Runs the Validation subset checker fused with the lowering, then either analyzes
the program or reports the full violation list, and writes one RENDER_SPEC.md
log. The abort policy (default strict) selects which machine-raise categories
become aborts; --abort and --model take comma-separated category overrides.
-/
import Pylate
import StrataPython.ReadPython
import Pylate.Analyzer

open Pylate

structure Args where
  ast    : Option String := none
  src    : Option String := none
  out    : Option String := none
  preset : String := "strict"
  aborts : List String := []
  models : List String := []
  sorts  : String := "checked"
  /-- Stop after admission: report accept/reject and skip the analysis. -/
  checkOnly : Bool := false
  /-- Extra `(preset, output)` pairs from `--emit`. Analysing several policies in
      one process amortises the ~51ms of Lean runtime startup, which measured at
      roughly 83% of the CPU in a full corpus run: the analysis of a small file is
      about 5ms, the process coming up is ten times that. Parsing and lowering are
      shared too. Each policy still runs in a fresh context -- `runProgramDefault`
      is `.run { policy }` on a default `Actx` -- so no cache leaks between them. -/
  emits  : List (String × String) := []

def parseArgs (args : List String) : Option Args :=
  let rec go (args : List String) (acc : Args) : Option Args :=
    match args with
    | [] => some acc
    | "--src" :: v :: rest => go rest { acc with src := some v }
    | "-o" :: v :: rest => go rest { acc with out := some v }
    | "--policy" :: v :: rest => go rest { acc with preset := v }
    | "--sorts" :: v :: rest => go rest { acc with sorts := v }
    | "--check-only" :: rest => go rest { acc with checkOnly := true }
    | "--abort" :: v :: rest =>
      go rest { acc with aborts := acc.aborts ++ v.splitOn "," }
    | "--model" :: v :: rest =>
      go rest { acc with models := acc.models ++ v.splitOn "," }
    | "--emit" :: v :: rest =>
      match v.splitOn "=" with
      | [preset, path] => go rest { acc with emits := acc.emits ++ [(preset, path)] }
      | _ => none
    | a :: rest =>
      if acc.ast.isNone then go rest { acc with ast := some a } else none
  match go args {} with
  | some a => if a.ast.isSome then some a else none
  | none => none

def presetPolicy (name : String) : Option Policy :=
  match name with
  | "strict" => some Policy.strict
  | "eafp" => some Policy.eafp
  | "audit" => some Policy.audit
  | _ => none

def buildPolicy (a : Args) : Option Policy := do
  let base ← match a.preset with
    | "strict" => some Policy.strict
    | "eafp" => some Policy.eafp
    | "audit" => some Policy.audit
    | _ => none
  let mut pol := base
  for c in a.aborts do
    if !policyCategories.contains c then none
    pol := pol.override c RMode.abort
  for c in a.models do
    if !policyCategories.contains c then none
    pol := pol.override c RMode.model
  if !a.aborts.isEmpty || !a.models.isEmpty then
    pol := { pol with preset := a.preset ++ "+overrides" }
  pure pol

/-- Every rule key in the two rule sets, one per line, as
    `builtin<TAB>list.append`. The validity gate reads this rather than a list of
    its own: a rule added without a scenario has to show up as uncovered, and it
    cannot do that if the gate is also the thing that decides what exists. -/
def dumpRules : IO Unit := do
  for r in RuleDriven.builtinRuleSet.rules do
    IO.println s!"builtin\t{r.key.render}"
  for r in RuleDriven.Syntax.syntaxRuleSet.rules do
    IO.println s!"syntax\t{r.key.render}"

def main (args : List String) : IO UInt32 := do
  if args == ["--dump-rules"] then
    dumpRules
    return 0
  match parseArgs args with
  | none =>
    IO.eprintln "usage: pylate INPUT.python.st.ion|AST.json [--src FILE.py] [-o LOG.json] [--policy strict|eafp|audit] [--emit POLICY=PATH ...] [--abort CATS] [--model CATS] [--dump-rules] [--check-only] [--sorts checked|residual]"
    return 2
  | some a =>
    if a.sorts != "checked" && a.sorts != "residual" then
      IO.eprintln "pylate: --sorts takes checked (fixpoint claims checked by switch catch-alls; default) or residual (per-flavor ADTs; trusts the fixpoint, requires the certificate)"
      return 2
    let some pol := buildPolicy a
      | do
        let cats := ",".intercalate policyCategories
        IO.eprintln s!"pylate: unknown policy or category (presets: strict eafp audit; categories: {cats})"
        return 2
    let ionPath := a.ast.get!
    -- The front end is the StrataDDM Ion importer. `readPythonStrata` decodes the
    -- file into the typed Strata AST, `Label.relabel` puts a `Pos` on every node,
    -- and `lowerModule` matches its constructors directly -- there is no JSON in
    -- the input path at all.
    if !ionPath.endsWith ".st.ion" then
      IO.eprintln s!"pylate: expected a .python.st.ion Strata AST, got {ionPath}"
      return 2
    -- A `SourceRange` is a byte range, so line and column need the source text.
    let srcPath : String :=
      match a.src with
      | some p => p
      | none =>
        if ionPath.endsWith ".python.st.ion" then
          (ionPath.dropEnd ".python.st.ion".length).toString ++ ".py"
        else ionPath
    let srcText : Option String ←
      match ← (IO.FS.readFile srcPath).toBaseIO with
      | .ok t => pure (some t)
      | .error _ => pure none
    let some text := srcText
      | do
        IO.eprintln s!"pylate: cannot read the Python source {srcPath}, which is needed for line and column information"
        return 2
    let stmts ←
      match ← (StrataPython.readPythonStrata ionPath).toBaseIO with
      | .ok s => pure s
      | .error e =>
        IO.eprintln s!"pylate: cannot read {ionPath}: {e}"
        return 2
    let body := Pylate.Label.relabel (Pylate.Label.Src.of text) stmts
    let srcName := a.src.getD ionPath
    let srcLines := if a.src.isSome then text.splitOn "\n" else []
    -- Lower once, whatever the policy: admission does not depend on it.
    let lowered := lowerModule body
    let analyse := fun (policy : Policy) =>
      match lowered with
      | .ok prog =>
        if a.checkOnly then emitCheckOnly srcName srcLines
        else
          let (m, ctx) :=
            (Pylate.RuleDriven.runProgramDefault prog).run { policy }
          emitAccepted srcName srcLines ctx m a.sorts
      | .err vs => emitRejected srcName srcLines vs
    if a.emits.isEmpty then
      let out := (analyse pol).pretty
      match a.out with
      | some p => IO.FS.writeFile p out
      | none => IO.println out
    else
      for (preset, path) in a.emits do
        let some policy := presetPolicy preset
          | do
            IO.eprintln s!"pylate: unknown policy '{preset}' in --emit"
            return 2
        IO.FS.writeFile path (analyse policy).pretty
    return 0
