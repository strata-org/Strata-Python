/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Sem
public import StrataDyn.Exec.Rules
public import StrataDyn.Exec.Table
public import StrataDyn.Exec.Types

/-!
# Executable semantics

What a Dyn instruction means, as a Lean function, and the machine that runs a module.  A
module that writes rules imports this one, which does not bring in the IR, so that the rule
interface's `Label` and `Region` do not meet the IR's.  A module that runs programs imports
`StrataDyn.Exec.Run`.  `docs/Dyn.md`, "Giving a language its semantics", is a guide to
writing rules, with examples from While and the test environment.

```lean
open Strata.Dyn.Exec

#dyn_types Demo

@[dyn_lang] class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  out : HasPart ε.W Output
  heap : HasHeap σ ε
  tagInt : TagOf σ Int

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [Lang σ ε]

@[dyn_sem Demo.add] def add (a b : Int) : Int := a + b
@[dyn_sem Demo.div] def div (a b : Int) (err : Target E [Int]) : Sem ε E Int := do
  if b = 0 then jump err 1
  return a / b
@[dyn_sem Demo.loop]
def loop (cond : Region ε [] Bool) (body : Region ε [] Unit) (_st : Option Unit)
    (again : Again E Unit) : Sem ε E Unit := do
  if ← runRegion cond () then
    runRegion body ()
    jump again ()
@[dyn_sem Demo.cellNew] def cellNew (v : Int) : Sem ε E (Ref σ Int) := newRef v
@[dyn_sem Demo.print] def print (x : Int) : Sem ε E Unit :=
  modifyThe Output fun o => { o with items := o.items.push x }

#dyn_sem_table DemoSem for Demo (world := DemoWorld)
```

* **Rules** (`Exec/Sem.lean`, `Exec/Rules.lean`) are ordinary `do` code in a free monad
  `Sem ε E α`, at Lean types only.  A rule takes its operands, then one `Region` per region,
  one `Target` per successor and, if it loops, its state and its operation's `Again`.  It
  returns, `jump`s along a target, stops by `semanticGap` or `semanticFailure`, runs a region
  by `runRegion`, loops by a `jump` to its `Again` with a new state, picks by `chooseNat`,
  `choose` or `chooseInt`, blocks an infeasible path by `assume`, reaches the parts of the world
  it names through `[HasPart ε.W P]`, each access one `update` request, makes, reads, writes
  and updates the machine's cells through `[HasHeap σ ε]`, and calls and binds closures
  through `[HasCall σ ε]`, each at the tags of the Lean types it reaches, `[TagOf σ α]`,
  `[SigOf σ as r]` and, over a list-kinded type variable, `[TagsOf σ cs]`.  A rule takes no
  fuel: the machine runs its requests as steps.  `@[dyn_type]` and `@[dyn_sem]` check
  each registration against the `environment` record.
* **Types** (`Exec/Types.lean`): `#dyn_types E`, which generates each datatype's Lean type,
  before `E`'s rules name them.
* **The table** (`Exec/Table.lean`): `#dyn_coverage` and `#dyn_sem_table`, which
  generates the decoding of tags and one wrapper per instruction.
* **The base's rules** (`Exec/Base.lean`): its types' Lean types, its terminators' rules, and
  the rules of the contracts' `old` and `cellLoc`, which stop with a gap.  Every environment that
  extends `Base` inherits them: the module that generates its table imports
  `StrataDyn.Exec.Base`.
* **Linking** (`Exec/Link.lean`) resolves every name through 2-3 trees once; **validation**
  (`Exec/Check.lean`) checks the linked module's tags and scopes once.
* **The machine** (`Exec/Machine.lean`): a first-order state, `step` with events,
  and hooks.  `Exec/Trace.lean` gives the step relation of `step`, whose runs, with no fuel,
  and their behaviours are what proofs are about; the run under one oracle is one of them, and
  every run is the run under some oracle.  **The fused run** (`Exec/Fused.lean`), `runFused`,
  the engine for execution, which stops or ends where the run under its oracle stands after at
  least as many steps (`runFused_eq`).  `Exec/Run.lean` starts and runs
  a module, from a `Snapshot` of a heap and a world, the initial one or where an earlier run
  ended.

## Design

* **Lean types, and tags.**  A rule names Lean types only: `Ref σ Int`, `FnRef σ [Int] Int`,
  `While.IntList.Val`.  The engine tags each value with a `Ty`, a tag: a head applied to tags.
  Heads `0` and `1` are a ref's and a code pointer's, and a table numbers each Lean type
  constructor its rules give from `2`, so Dyn types that share a Lean type share a tag:
  `Hd.Meters` and `Hd.Feet`, both `Int`, are `base.Int`'s.  `Ty.decode` gives a tag's Lean
  type, and reduces by `rfl`.  A semantics that must tell such types apart gives them distinct
  Lean types.
* **The run token.**  Everything a table generates is generic in a token `σ`, as Haskell's
  `ST s` is, and linking instantiates it once, at `Run`.  A ref is a raw ref, a location with
  a proof that the token gives, and its contents' Lean type as a phantom, and a closure is a
  raw closure with its signature as a phantom.  No term generic in the token is a raw ref or a
  raw closure (`no_forge`, `no_forge_fn`).  The token's proofs do not name the contents' type,
  so a datatype may hold a ref or a closure of itself.  `Run` promises nothing, and the
  machine checks every access of a cell and every call of a closure.
* **Tags at the access.**  A ref is its location, and a closure its function and its captures
  cell: neither carries a tag.  A rule that makes, reads or writes a cell takes the tag of its
  contents' type, `[TagOf σ α]`, and one that calls a closure, its signature's, `[SigOf σ as r]`.
  The wrapper builds each at the instruction's concrete types, from the table's decoding,
  which it supplies as `[Decode σ]`, with the proof `rfl`.  `TagCon σ F` gives the tags of
  `F A` from `A`'s, for a rule that reaches cells through a type constructor generically.
* **Type parameters.**  A rule for an instruction with type parameters is polymorphic in
  Lean: one `{α : Type}` per type parameter and one `{cs : List Type}` per list parameter.
  Its wrapper takes the type arguments' tags and instantiates `α := S.interp σ a`.  A generic
  rule takes `[TagOf σ α]` only if it reaches a cell or a call at `α`.  The rule is one Lean
  function, polymorphic in `α`, so one wrapper serves every instantiation.
* **Handles.**  A rule is generic in its requests `ε` and its exits `E`, and takes its targets,
  its `Again`, its regions and its cell and call capabilities as arguments.  The wrapper builds
  each as a closed term, so the machine reads the outcome at the wrapper's type, with no check.
* **Calls and closures.**  A `base.Fn as r` is an `FnRef σ as r`, a closure: a function and the
  location of a write-once captures cell, which a static code pointer lacks.  `base.callCode`
  is the machine's call; a rule calls by `callFn` and binds an argument by `bindFn`, which makes
  a new captures cell.  The machine checks each call, by the function's signature against the
  tags of what the closure captured and the call's tags, and faults with `Fault.badCall` on a
  mismatch.  A language whose functions raise returns a `base.Except`, and its call rule
  inspects it.
* **Cells.**  A ref may be anywhere a value may: in a datatype, a payload, a result, a region's
  or a function's argument.  The machine checks each access, by the cell's bound and its
  contents' tag, and faults with `Fault.badCell` if the check fails.
* **Loops.**  A rule that loops takes `(st : Option S)` and its operation's `Again E S`, for a
  Lean type `S` of its own, such as a comprehension's elements left and results so far.  Its
  first run has `st = none`; a jump to its `Again` with `s` runs it again, on the same
  operands, regions and targets, with `st = some s`, as a step of its own.  The state is the
  rule's: the instruction's declaration, and so the IR, does not mention it.
* **Keys** are the Lean names of types and instructions (`Base.Int`, `Py.add`), resolved
  through the `environment` record, so a misspelt key is an elaboration error.  An
  instruction's key is its own name, which its emitter shares, not its reference
  `Py.add.ref`.  Rules are stored by the declaration's Lean name, and a child environment's
  table uses its ancestors' rules, those that call included.  If two imported modules register
  one key, `@[dyn_sem]`, `#dyn_coverage` and `#dyn_sem_table` report both, for the
  key's environment and those that extend it.
* **Trust.**  Rules are trusted: a rule is what its instruction means.  Registration checks
  its shape and types, listed in `Exec/Rules.lean`, and `implemented_by` and `@[extern]` in a
  rule are flags for review, as in Lean.
-/
