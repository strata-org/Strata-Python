/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all StrataPython.Dyn.Scope
import all StrataPython.Dyn.Translate
public meta import Lean.Elab.Command

set_option autoImplicit false

/-!
# The translator's partial definitions

Lean records no equation for a recursive `partial def`, so no theorem can say anything about
its result.  These checks pin the definitions that stand in the way of proofs about
`translate`:

* `#partial_defs_in M ns`: the recursive `partial def`s that the module `M` declares, `where`
  helpers included, named without the namespace `ns`.  A `partial def` that does not recurse
  is an ordinary definition, so it is not listed;
* `#opaque_reach M f`: the opaque constants and the axioms that the definition of `f`, from the
  module `M`, reaches through the values of definitions.  A recursive `partial def` is one.
  So are some of Lean's own constants: primitives such as `String.hash`, and the opaque
  helpers inside `while` and `WellFounded.extrinsicFix`, which have unfolding lemmas.  The
  walk does not look inside an opaque constant, and it leaves out Lean's three standard
  axioms.

* `#fuel_loops M f`: the definitions named `Strata…` that the definition of `f`, from the
  module `M`, reaches through the values of definitions, and that use fuel.  Each is listed
  with the theorem that proves its fuel enough, from `provedFuel`, or as unproved.  The check
  finds two shapes of fuel by itself: a `for _ in [a:b]` loop whose body ignores the index
  (also with `for h : _ in`), and structural recursion on a `Nat`.  It does not find other
  shapes, such as a `while` loop, a search over `List.range n`, or well-founded recursion on a
  fuel argument (`#uses_fuel` pins these); `otherFuel` lists the reached definitions with
  such fuel by hand.

The walks follow the values of definitions, so they do not see a `@[csimp]` replacement that
the compiled code runs instead of a definition.  A theorem proves each such replacement equal
to the definition it replaces.

The goal is that `translate` reaches only Lean's own constants, and that every fuel it uses is
proved enough.

All three import `M` afresh with every module's private data.  Without it, a definition whose
module does not expose its body appears as an axiom, and the walk would stop there.
-/

namespace StrataPython.Dyn.TotalityTest

open Lean Elab Command

/-- Lean's standard axioms. -/
private meta def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The constants that `root`'s definition reaches through the values of definitions.  The walk
looks only inside definitions. -/
private meta def reached (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := NameSet.empty.insert root
  let mut todo := #[root]
  let mut out := #[]
  -- Each constant is pushed once, so this is one step per constant, and one more.
  for _ in [0:env.constants.map₁.size + env.constants.map₂.toList.length + 1] do
    let some n := todo.back? | break
    todo := todo.pop
    out := out.push n
    if let some (.defnInfo d) := env.find? n then
      for c in d.value.getUsedConstants do
        unless seen.contains c do
          seen := seen.insert c
          todo := todo.push c
  return out

/-- The opaque constants and the axioms other than `standardAxioms` that `root`'s definition
reaches. -/
private meta def opaqueReach (env : Environment) (root : Name) : Array Name :=
  (reached env root).filter fun n =>
    match env.find? n with
    | some (.opaqueInfo _) => true
    | some (.axiomInfo _) => !standardAxioms.contains n
    | _ => false

/-- The recursive `partial def`s that the module `m` declares: the opaque constants with an
`_unsafe_rec` implementation. -/
private meta def partialDefsIn (env : Environment) (m : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? m | return #[]
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some idx then continue
    if let .opaqueInfo _ := ci then
      if env.contains (Compiler.mkUnsafeRecName n) then out := out.push n
  return out

/-- `n` without the `_private.<module>.0.` prefix and the namespace `ns`. -/
private meta def shortName (ns n : Name) : Name :=
  (privateToUserName n).replacePrefix ns .anonymous

/-- The count of `names`, then each on its own line, without the namespace `ns`, sorted. -/
private meta def listNames (ns : Name) (names : Array Name) : MessageData :=
  let short := (names.map (shortName ns ·)).qsort (·.toString < ·.toString)
  m!"{short.size}:{short.foldl (fun m n => m ++ m!"\n  {n}") m!""}"

/-- Whether `e` is a loop over a range whose body ignores the index: fuel.  In
`for h : _ in r`, the index may appear in the type of `h`. -/
private meta def isFuelLoop (e : Expr) : Bool :=
  (e.isAppOf ``ForIn.forIn || e.isAppOf ``ForIn'.forIn') &&
    e.getAppArgs.any (·.isAppOf ``Std.Legacy.Range.mk) &&
    match e.getAppArgs.back? with
    | some (.lam _ _ body _) =>
      if e.isAppOf ``ForIn'.forIn' then
        match body with
        | .lam _ _ inner _ => !inner.hasLooseBVar 1
        | _ => false
      else !body.hasLooseBVar 0
    | _ => false

/-- Whether the value `v` uses fuel: a range loop that ignores its index, or structural
recursion on a `Nat`. -/
private meta def usesFuel (v : Expr) : Bool :=
  (v.find? isFuelLoop).isSome ||
    (v.find? fun e => e.isConstOf ``Nat.brecOn || e.isConstOf ``Nat.rec).isSome

/-- The definitions that use fuel, each with the theorem that proves its fuel enough.  For
`addAncs`, the theorem says instead that every entry it adds is right for any fuel, because
`ancAt` falls back to `chain` for a missing entry.  `sdF` appears only in the termination
measure of `settle`, so it never runs. -/
private meta def provedFuel : List (Name × Name) :=
  [(`Strata.Dyn.Body.addAncs, `Strata.Dyn.Body.addAncs_good),
   (`Strata.Dyn.Body.chain, `Strata.Dyn.Body.above_iff),
   (`Strata.Dyn.Body.grow, `Strata.Dyn.Body.reached_spec),
   (`Strata.Dyn.Body.intersect, `Strata.Dyn.Body.intersect_spec),
   (`Strata.Dyn.Body.sdF, `Strata.Dyn.Body.sdF_fuel),
   (`Strata.Dyn.Name.keyNatAux, `Strata.Dyn.Name.natVal_natDigits),
   (`Strata.Dyn.NatTrie.insertAt, `Strata.Dyn.NatTrie.find?_insertAt)]

/-- The definitions that use fuel in a shape `usesFuel` does not find. -/
private meta def otherFuel : List Name := []

/-- The definitions named `Strata…` that `root`'s definition reaches and that use fuel, with
those of `otherFuel` that it reaches. -/
private meta def fuelReach (env : Environment) (root : Name) : Array Name :=
  (reached env root).filter fun n =>
    let user := privateToUserName n
    otherFuel.contains user ||
      (user.getRoot.toString.startsWith "Strata" &&
        match env.find? n with
        | some (.defnInfo d) => usesFuel d.value
        | _ => false)

/-- The environment of the modules `ms` and their imports, with their private data. -/
private meta def fullEnv (ms : Array Name) : CommandElabM Environment :=
  liftM (m := IO) <| importModules (ms.map fun m => { module := m }) {} (level := .private)

/-- The modules with the theorems of `provedFuel` that `translate`'s module does not import. -/
private meta def fuelProofModules : Array Name := #[]

elab "#partial_defs_in " m:ident ns:ident : command => do
  logInfo (listNames ns.getId (partialDefsIn (← fullEnv #[m.getId]) m.getId))

elab "#fuel_loops " m:ident f:ident : command => do
  let env ← fullEnv (#[m.getId] ++ fuelProofModules)
  unless env.contains f.getId do throwError "unknown constant {f.getId}"
  -- A theorem outside a `public section` has a private name.
  let theorems : NameSet := env.constants.fold (init := {}) fun s n ci =>
    if ci matches .thmInfo _ then s.insert (privateToUserName n) else s
  let found := (fuelReach env f.getId).map privateToUserName
  for (d, _) in provedFuel do
    unless found.contains d do throwError "{d} is in provedFuel but is not found as fuel"
  let lines : Array String := found.map fun n =>
    match provedFuel.lookup n with
    | some thm =>
      if theorems.contains thm then s!"{n} (proved: {thm})"
      else s!"{n} (theorem {thm} not found)"
    | none => s!"{n} (unproved)"
  let sorted := lines.qsort (· < ·)
  logInfo m!"{sorted.size}:{sorted.foldl (fun m l => m ++ m!"\n  {l}") m!""}"

elab "#uses_fuel " f:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload f
  let some (.defnInfo d) := (← getEnv).find? n | throwError "{n} is not a definition"
  logInfo m!"{usesFuel d.value}"

elab "#opaque_reach " m:ident f:ident : command => do
  let env ← fullEnv #[m.getId]
  unless env.contains f.getId do throwError "unknown constant {f.getId}"
  logInfo (listNames .anonymous (opaqueReach env f.getId))

/--
info: 0:
-/
#guard_msgs in
#partial_defs_in StrataPython.Dyn.Scope StrataPython.Dyn.PyScope

/--
info: 10:
  clause
  findAnn
  forStmt
  ifStmt
  transStmt
  transStmts
  tryFinallyStmt
  tryStmt
  whileStmt
  withStmt
-/
#guard_msgs in
#partial_defs_in StrataPython.Dyn.Translate StrataPython.Dyn.PyTranslate

/--
info: 13:
  Lean.Syntax.decodeScientificLitVal?.decode
  Std.Internal.idOpaque
  Strata.Dyn.DomDiag.body
  StrataPython.Dyn.PyTranslate.findAnn
  StrataPython.Dyn.PyTranslate.transStmts
  String.Internal.append
  String.Internal.get
  String.Internal.length
  String.hash
  System.Platform.getNumBits
  WellFounded.opaqueFix
  mixHash
  repeatM.impl
-/
#guard_msgs in
#opaque_reach StrataPython.Dyn.Translate StrataPython.Dyn.PyTranslate.translate

/--
info: 14:
  Strata.Dyn.Body.addAncs (proved: Strata.Dyn.Body.addAncs_good)
  Strata.Dyn.Body.chain (proved: Strata.Dyn.Body.above_iff)
  Strata.Dyn.Body.grow (proved: Strata.Dyn.Body.reached_spec)
  Strata.Dyn.Body.intersect (proved: Strata.Dyn.Body.intersect_spec)
  Strata.Dyn.Body.sdF (proved: Strata.Dyn.Body.sdF_fuel)
  Strata.Dyn.Body.search (unproved)
  Strata.Dyn.Name.keyNatAux (proved: Strata.Dyn.Name.natVal_natDigits)
  Strata.Dyn.NatTrie.insertAt (proved: Strata.Dyn.NatTrie.find?_insertAt)
  StrataPython.Dyn.PyScope.analyzeBlock (unproved)
  StrataPython.Dyn.PyScope.extendNamedExprScope (unproved)
  StrataPython.Dyn.PyScope.splicedChildren (unproved)
  StrataPython.Dyn.PyTranslate.childScope? (unproved)
  StrataPython.Dyn.PyTranslate.enclosingPlace (unproved)
  StrataPython.Dyn.PyTranslate.firstParam? (unproved)
-/
#guard_msgs in
#fuel_loops StrataPython.Dyn.Translate StrataPython.Dyn.PyTranslate.translate

/-! ## The shapes of fuel the check finds -/

private def rangeFuel (n : Nat) : Nat := Id.run do
  let mut x := 0
  for _ in [0:n] do x := x + 1
  return x

private def memFuel (n : Nat) : Nat := Id.run do
  let mut x := 0
  for _h : _ in [0:n] do x := x + 1
  return x

private def recFuel : Nat → Nat → Nat
  | 0, a => a
  | f + 1, a => recFuel f (a + 1)

private def indexLoop (a : Array Nat) : Nat := Id.run do
  let mut x := 0
  for h : i in [0:a.size] do x := x + a[i]
  return x

private def whileFuel (n : Nat) : Nat := Id.run do
  let mut x := 0
  while x < n do x := x + 1
  return x

private def listRangeFuel (n : Nat) : Nat := ((List.range n).find? (· > 3)).getD 0

private def wfFuel (fuel : Nat) : Nat := if fuel = 0 then 0 else wfFuel (fuel - 1)
termination_by fuel

/-- info: true -/
#guard_msgs in #uses_fuel rangeFuel
/-- info: true -/
#guard_msgs in #uses_fuel memFuel
/-- info: true -/
#guard_msgs in #uses_fuel recFuel
-- A loop that uses its index is not fuel.
/-- info: false -/
#guard_msgs in #uses_fuel indexLoop
-- Shapes the check does not find, which `otherFuel` must list by hand.
/-- info: false -/
#guard_msgs in #uses_fuel whileFuel
/-- info: false -/
#guard_msgs in #uses_fuel listRangeFuel
/-- info: false -/
#guard_msgs in #uses_fuel wfFuel

/-! ## Equations

A total definition has equations that a proof can unfold. -/

open StrataPython.Dyn.PyScope in
open StrataDDM (SourceRange) in
/-- `case [x, *rest]:` captures `x` and `rest`, in order. -/
example (sr : SourceRange) :
    patternCaptures (.MatchSequence sr ⟨sr, #[.MatchAs sr ⟨sr, none⟩ ⟨sr, some ⟨sr, "x"⟩⟩,
      .MatchStar sr ⟨sr, some ⟨sr, "rest"⟩⟩]⟩) = #[("x", sr), ("rest", sr)] := by
  simp [patternCaptures]

open StrataPython.Dyn.PyScope in
/-- An empty statement list records nothing. -/
example : visitStmts #[] = pure () := by
  simp [visitStmts]

open StrataPython.Dyn.PyTranslate in
open StrataPython (expr cmpop) in
open StrataDDM (SourceRange) in
/-- A comparison with one operator evaluates its operands, then compares them. -/
example (l r : expr SourceRange) (op : cmpop SourceRange) :
    PyTranslate.compare l #[op] #[r] =
      (do let a ← transExpr l; cmpOp op a (← transExpr r)) := by
  simp [PyTranslate.compare]

end StrataPython.Dyn.TotalityTest
