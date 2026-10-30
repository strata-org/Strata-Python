/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDyn.DDMRead
import all StrataDyn.DDMRead
import StrataDyn.Env.WF
import StrataDyn.DSL
-- The checker and the reader run as compiled code below.
meta import StrataDyn.WF
meta import StrataDyn.Build
meta import all StrataDyn.DDMRead
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Checking large inputs in linear time

Each test checks an input of some size `n` and one of size `2n`, and fails if the larger one takes
3 times as long as the smaller one, or longer.  A check in linear time takes about twice as long on
the larger input, and a check in quadratic time about 4 times as long, once the quadratic part of
its time dominates.  The sizes are chosen so that it would dominate.  So the tests do not depend on
how fast the machine is.  The answers are pinned too, a large one by a count.

Lean decides a quantifier over an array's members in time quadratic in its size, so the checker
quantifies over lists.  The reader adds the type of each folded constant to its array in place,
and it collects the instructions and the blocks it reads, and its diagnostics, in lists.  The
checks of contract regions look the targets of failure successors up in a map built once per
region (`Region.failuresToB`), and compiled code checks that a region has no cycle by Kahn's
algorithm (`Body.acyclicFast`, through `@[csimp]`).  These tests fail if the check of a
function's blocks, of a module's functions, ghosts and references, or of a contract's regions
becomes quadratic, or if the reader copies an array for each folded constant, instruction, block
or diagnostic.  The tests of the last section fail if the dominance check takes quadratic time
when many blocks jump to one block: in a chain of blocks, in a contract clause and in a loop.

Heartbeats count small allocations.  The quadratic versions do their extra work without them, by
copying arrays and calling closures, so a heartbeat limit cannot see it.  Each test measures time
instead.
-/

namespace Strata.Dyn.ScaleTest

/-- Fail unless `check` gives `true` on both inputs that `inputs m` gives, one of size `m` and one
of size `2 * m`, and fail if checking the larger one takes 3 times as long as checking the smaller
one, or longer.  It compares the shortest of three times of each input, so one run that a busy
machine slows down does not change the result.  It times the smaller input three times first.  It
then times the larger one up to three times, and stops as soon as the shortest time so far is less
than 3 times the smaller one's.  Run `k` builds the inputs with `m = n + k`.  A computation that
uses no variable is a closed term, and compiled code computes it only once.  The run number makes
each run build and check its inputs again. -/
private def scalesLinearly {α : Type} (what : String) (n : Nat) (inputs : Nat → α × α)
    (check : α → Bool) : IO Unit := do
  let mut small : Nat := 0
  let mut larges : Array α := #[]
  for k in [0:3] do
    let (s, l) ← IO.lazyPure fun _ => inputs (n + k)
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => check s
    let t1 ← IO.monoNanosNow
    unless ok do throw <| IO.userError s!"{what}: the check gives false"
    small := if k = 0 then t1 - t0 else min small (t1 - t0)
    larges := larges.push l
  let mut large : Option Nat := none
  for l in larges do
    let t0 ← IO.monoNanosNow
    let ok ← IO.lazyPure fun _ => check l
    let t1 ← IO.monoNanosNow
    unless ok do throw <| IO.userError s!"{what}: the check gives false"
    let t := (large.map (min (t1 - t0))).getD (t1 - t0)
    if t < 3 * small then return
    large := some t
  throw <| IO.userError s!"{what}: the larger input took \
    {(large.getD 0).toFloat / small.toFloat} times as long as the smaller one"

/-- The inputs of sizes `m` and `2 * m` that `f` builds. -/
private def twice {α : Type} (f : Nat → α) (m : Nat) : α × α := (f m, f (2 * m))

private def nm (s : String) : Name := .str .base s

/-- A function with `n` blocks, each ending in `unreachable`. -/
private def blocksFn (n : Nat) : Func base Unit :=
  { name := nm "f", params := #[], retType := Base.Int, names := #[], info := ()
    blocks := (Array.range n).map fun i =>
      { label := ⟨.num (nm "b") i⟩, params := #[], instrs := #[], term := .unreachable (),
        info := () } }

-- The blocks of a function.
#guard_msgs in
#eval scalesLinearly "the blocks of a function" 15000 (twice blocksFn) fun fn => decide fn.BodyWF

/-- The stubs `@f.0` to `@f.(n-1)`, each checked. -/
private def stubs (n : Nat) : Array {f : Func base Unit // f.WF} :=
  (Array.range n).map fun i => Build.stub (.num (nm "f") i) #[] Base.Int ()

-- A module of checked functions.
#guard_msgs in
#eval scalesLinearly "a module of checked functions" 15000 (twice stubs) fun fs =>
  (Module.ofChecked (nm "m") fs ()).toOption.any (·.raw.funcs.size == fs.size)

/-- The externs `@f.0` to `@f.(n-1)`, without parameters or contracts. -/
private def externs (n : Nat) : Array (Func base Unit) :=
  (Array.range n).filterMap fun i =>
    (Build.buildExtern (.num (nm "f") i) #[] Base.Int () fun _ => pure ()).toOption.map (·.val)

/-- The module `m` of the externs `@f.0` to `@f.(n-1)`, paired with `n`. -/
private def externModule (n : Nat) : Nat × Module.Raw base Unit :=
  (n, { name := nm "m", funcs := externs n, info := () })

-- A module checked whole.
#guard_msgs in
#eval scalesLinearly "a module of externs" 12000 (twice externModule) fun (n, m) =>
  m.funcs.size == n && m.check.toOption.any (·.raw.funcs.size == n)

/-- `@g.0`, which starts at `0`, then the ghosts `@g.1` to `@g.(n-1)`, each of which starts at the
contents of `@g.0`, all checked.  The ghosts after the first are one checked ghost under other
names, since the rules of `Ghost.WF` do not mention a ghost's name. -/
private def ghostFan (n : Nat) : Array {g : Ghost base Unit // g.WF} :=
  let first := Build.ghost (env := base) (.num (nm "g") 0) Base.Int
    (some do Build.finishBlock (.ret () (← Build.emitConst (nm "zero") (.int 0)))) none ()
  let rest := Build.ghost (env := base) (.num (nm "g") 1) Base.Int (some do
    let c ← Build.emitGhost (.num (nm "g") 0) Base.Int
    Build.finishBlock (.ret () (← Build.emitApply (nm "n") Base.Int Base.refGet.ref #[c]
      (typeArgs := ta[Base.Int])))) none ()
  match first, rest with
  | .ok f, .ok r => #[f] ++ (Array.range (n - 1)).map fun i =>
    ⟨{ r.val with name := .num (nm "g") (i + 1) }, by
      obtain ⟨a, b, c, d, e, f, h, i⟩ := r.property
      exact ⟨a, b, c, d, e, f, h, i⟩⟩
  | _, _ => #[]

-- A module of checked ghosts, each initializer naming a ghost before it, so that the order of
-- the initializers is checked.
#guard_msgs in
#eval scalesLinearly "a module of checked ghosts" 20000 (twice fun n => (n, ghostFan n))
  fun (n, gs) => gs.size == n &&
    (Module.ofChecked (nm "m") #[] () (ghosts := gs)).toOption.any (·.raw.ghosts.size == n)

/-- The ghosts `@g.0` to `@g.(n-1)`, each a `base.Int` with neither an initializer nor an
invariant. -/
private def bareGhosts (n : Nat) : Array (Ghost base Unit) :=
  (Array.range n).map fun i => { name := .num (nm "g") i, type := Base.Int, info := () }

/-- The module `m` of the ghosts `@g.0` to `@g.(n-1)`, paired with `n`. -/
private def ghostModule (n : Nat) : Nat × Module.Raw base Unit :=
  (n, { name := nm "m", ghosts := bareGhosts n, funcs := #[], info := () })

-- A module of ghosts checked whole.
#guard_msgs in
#eval scalesLinearly "a module of ghosts" 15000 (twice ghostModule) fun (n, m) =>
  m.check.toOption.any (·.raw.ghosts.size == n)

/-- Define `n` folded constants with `Read.defineConst`, and check that the last one has the id
`n - 1`. -/
private def defineConsts (n : Nat) : Bool :=
  let m : Read.ReadM base Nat := do
    let mut last := 0
    for _ in [0:n] do
      last := (← Read.defineConst Base.Int).id
    return last
  match m.run {} with
  | .ok (k, _) => k + 1 == n
  | .error _ => false

-- Folded constants.
#guard_msgs in
#eval scalesLinearly "folded constants" 100000 (twice id) defineConsts

/-- A name, as the printed form writes it. -/
private def mname (s : String) : DDM.MName StrataDDM.SourceRange := .name .none ⟨.none, s⟩

private abbrev SR := StrataDDM.SourceRange

private def intTy : DDM.MType SR := .tyPrim .none (mname "base.Int")

/-- The constants `%c.0` to `%c.(n-1)`, each `const 0`, as the parser gives them. -/
private def constInsns (n : Nat) : Array (DDM.MInsn SR) :=
  (Array.range n).map fun i =>
    .insnConst .none (.valDecl .none (.valName .none (mname s!"c.{i}")) intTy)
      (.constInt .none (.natInt .none ⟨.none, 0⟩))

/-- The module `m` of one function `@m.f(%x.0 : base.Int) -> base.Int`, whose one block defines
`n` constants, each on a line of its own, and returns `%x.0`: the term that parsing its printed form
gives, up to source ranges, built without the parser. -/
private def constsModule (n : Nat) : DDM.Command SR :=
  let int := intTy
  let x : DDM.MVal SR := .valName .none (mname "x.0")
  let param : DDM.MValDecl SR := .valDecl .none x int
  let consts := constInsns n
  let ret : DDM.MTerm SR :=
    .termRet .none ⟨.none, some (.operands .none ⟨.none, #[.operandVal .none x]⟩)⟩
  let block : DDM.MBlock SR := .block .none (mname "entry.0") ⟨.none, #[param]⟩ ⟨.none, consts⟩ ret
  .moduleDecl .none (mname "m") ⟨.none, #[]⟩
    ⟨.none, #[.func .none (.funcName .none (mname "m.f")) ⟨.none, #[param]⟩ int ⟨.none, none⟩
      ⟨.none, #[block]⟩]⟩

-- The term reads as the module it stands for.
/-- info: module m {
  func @m.f(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Int = const 0
      %c.1 : base.Int = const 0
      ret(%x.0)
  }
} -/
#guard_msgs in
#eval match Module.ofDDM (env := base) (constsModule 2) with
  | .ok m => IO.println (m.format .full)
  | .error ds => IO.println (ds.map ReadDiagnostic.message)

/-- What the reader's walk over the instructions or blocks of a body gives: one completion per
element, and the ids that the completions take, once the walk has defined every value. -/
private def walked {β : Type} (m : Read.ReadM base (List (Read.Late β))) :
    Except String (List (Read.Late β) × (Name → ValId)) := do
  let (l, s) ← (m.run {}).mapError (·.message)
  return (l, fun n => (s.values.get? n).getD ⟨0⟩)

/-- The scope of a body whose exit takes a `base.Int`, with no block to transfer to. -/
private def exitScope : Read.Scope base := ({} : Read.Scope base).insert .base #[Base.Int]

-- Reading the instructions of a block: the walk, then the completion.  Completing alone takes too
-- little time to measure reliably, so the test times the walk and the completion together.  A
-- quadratic completion would still take most of that time.
#guard_msgs in
#eval scalesLinearly "reading the instructions of a block" 24000 (twice constInsns) fun is =>
  match walked (Read.insnList { funcs := NameTable.empty } exitScope is.toList) with
  | .ok (l, ids) => (Read.Late.list l ids).size == is.size
  | .error _ => false

/-- A walk of size `2 * m`, and its first `m` completions with the same ids, each with its size.
One walk gives both inputs, since walking takes much longer than completing. -/
private def halves {β : Type} (m : Nat)
    (w : Except String (List (Read.Late β) × (Name → ValId))) :
    (Nat × Except String (List (Read.Late β) × (Name → ValId))) ×
      (Nat × Except String (List (Read.Late β) × (Name → ValId))) :=
  ((m, w.map fun (l, ids) => (l.take m, ids)), (2 * m, w))

/-- The blocks `b.0` to `b.(n-1)`, each ending in `unreachable`, as the parser gives them. -/
private def unreachableBlocks (n : Nat) : List (DDM.MBlock SR) :=
  (List.range n).map fun i =>
    .block .none (mname s!"b.{i}") ⟨.none, #[]⟩ ⟨.none, #[]⟩
      (.termApply .none (mname "unreachable") ⟨.none, none⟩ ⟨.none, none⟩ ⟨.none, #[]⟩ ⟨.none, #[]⟩)

/-- The walk over the blocks `b.0` to `b.(n-1)`, as `walked` gives it. -/
private def walkedBlocks (n : Nat) :
    Except String (List (Read.Late (Block base StrataDDM.SourceRange)) × (Name → ValId)) := do
  let bs := unreachableBlocks n
  let (scope, _) ← (Read.scopeOf (env := base) .none Base.Int bs).mapError (·.message)
  walked (Read.blockList { funcs := NameTable.empty } scope bs)

-- Completing the blocks of a body, after the walk.
#guard_msgs in
#eval scalesLinearly "completing the blocks of a body" 32000
  (fun m => halves m (walkedBlocks (2 * m))) fun
  | (n, .ok (l, ids)) => (Read.Late.list l ids).size == n
  | (_, .error _) => false

/-- The module `m` of `n` functions, each with an unknown return type, so that reading each one
fails at once. -/
private def failingModule (n : Nat) : DDM.Command SR :=
  let nope : DDM.MType SR := .tyPrim .none (mname "base.Nope")
  .moduleDecl .none (mname "m") ⟨.none, #[]⟩ ⟨.none, (Array.range n).map fun i =>
    .func .none (.funcName .none (mname s!"m.f{i}")) ⟨.none, #[]⟩ nope ⟨.none, none⟩
      ⟨.none, #[]⟩⟩

-- The diagnostics of a module.
#guard_msgs in
#eval scalesLinearly "the diagnostics of a module" 50000 (twice fun n => (n, failingModule n))
  fun (n, c) =>
    match Module.ofDDM (env := base) c with
    | .ok _ => false
    | .error ds => ds.size == n

/-- The module `m` with one function `m.fi` for each type `types[i]`: it takes no arguments,
returns that type and ends in `unreachable`. -/
private def typedModule (types : Array String) : DDM.Command SR :=
  .moduleDecl .none (mname "m") ⟨.none, #[]⟩ ⟨.none, types.mapIdx fun i t =>
    .func .none (.funcName .none (mname s!"m.f{i}")) ⟨.none, #[]⟩ (.tyPrim .none (mname t))
      ⟨.none, none⟩ ⟨.none, (unreachableBlocks 1).toArray⟩⟩

-- The diagnostics come in the order of the functions: those of the first, third and fourth here.
/-- info: #[unknown type base.Nope0, unknown type base.Nope2, unknown type base.Nope3] -/
#guard_msgs in
#eval match Module.ofDDM (env := base)
    (typedModule #["base.Nope0", "base.Int", "base.Nope2", "base.Nope3"]) with
  | .ok _ => IO.println "read"
  | .error ds => IO.println (ds.map ReadDiagnostic.message)

/-! ## The checks of contract regions -/

/-- An operation that may fail, and one that runs a region. -/
public environment Ops extends Base where
  namespace ops
  open base
  /-- `a / b`.  It fails, with an error code, when `b` is zero. -/
  calls insn div (a b : Int) (^err (e : Int)) : Int
  /-- Runs `body`: the value of an `ok`, or a transfer to `err` with the error of an `error`. -/
  pure insn attempt (&body : Except Int Bool) (^err (e : Int)) : Bool
  end ops

/-- `@m.f(%v.0 : base.Int) -> base.Int`, which returns `%v.0`, with two `requires` clauses:

* a chain of the blocks `b.0` to `b.n`: each `b.i` before `b.n` divides `%v.0` by itself, its
  failure going to `fail.0`, which returns `false`, and jumps to `b.(i+1)`; `b.n` returns `true`;
* `ops.attempt` of a region that is a chain of the blocks `c.0` to `c.n` in the same way, whose
  failures go to `stop.0`, which ends in `unreachable`, as `c.n` does.

So the checks of the contract's regions follow `2n + 1` failure successors, and order the `2n + 6`
blocks of the regions. -/
private def chainFn (n : Nat) : Func Ops.env Unit :=
  let intT : TypeExpr Ops.env := Base.Int
  let boolT : TypeExpr Ops.env := Base.Bool
  let d (k : Nat) (t : TypeExpr Ops.env) : ValDecl Ops.env := ⟨⟨k⟩, t⟩
  let lbl (stem : String) (i : Nat) : Label := ⟨.num (nm stem) i⟩
  let block (l : Label) (params : Array (ValDecl Ops.env))
      (instrs : Array (Instruction Ops.env Unit)) (term : Terminator Ops.env Unit) :
      Block Ops.env Unit :=
    { label := l, params, instrs, term, info := () }
  -- The blocks `stem.0` to `stem.(n-1)`, defining the values `first` to `first + n - 1`.
  let chain (stem : String) (first : Nat) (fail : Label) : Array (Block Ops.env Unit) :=
    (Array.range n).map fun i => block (lbl stem i) #[]
      #[.apply () (d (first + i) intT) Ops.div.ref ⟨#[], rfl⟩ #[⟨0⟩, ⟨0⟩] #[⟨fail, #[]⟩] #[]]
      (.jump () ⟨lbl stem (i + 1), #[]⟩)
  let inner : Region Ops.env Unit := ⟨chain "c" (n + 5) (lbl "stop" 0) ++
    #[block (lbl "c" n) #[] #[] (.unreachable ()),
      block (lbl "stop" 0) #[d (2 * n + 5) intT] #[] (.unreachable ())]⟩
  let first : Region Ops.env Unit := ⟨chain "b" 1 (lbl "fail" 0) ++
    #[block (lbl "b" n) #[] #[.const () (d (n + 1) boolT) (.bool true)] (.ret () ⟨n + 1⟩),
      block (lbl "fail" 0) #[d (n + 2) intT] #[.const () (d (n + 3) boolT) (.bool false)]
        (.ret () ⟨n + 3⟩)]⟩
  let second : Region Ops.env Unit := ⟨#[
    block (lbl "pre" 0) #[]
      #[.apply () (d (n + 4) boolT) Ops.attempt.ref ⟨#[], rfl⟩ #[] #[⟨lbl "fail" 1, #[]⟩] #[inner]]
      (.ret () ⟨n + 4⟩),
    block (lbl "fail" 1) #[d (2 * n + 6) intT] #[.const () (d (2 * n + 7) boolT) (.bool false)]
      (.ret () ⟨2 * n + 7⟩)]⟩
  { name := .str (nm "m") "f", params := #[d 0 intT], retType := intT,
    blocks := #[block (lbl "entry" 0) #[d 0 intT] #[] (.ret () ⟨0⟩)],
    contract := { requires := #[{ region := first }, { region := second }] },
    names := (Array.range (2 * n + 8)).map (.num (nm "v")), info := () }

-- At a small size, the function is well formed, and prints as the docstring of `chainFn` says.
#guard decide (chainFn 3).WF

/-- info: module m.f {
  func @m.f(%v.0 : base.Int) -> base.Int
    requires {
      b.0():
        %v.1 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
        jump ^b.1()
      b.1():
        ret(true)
      fail.0(%v.3 : base.Int):
        ret(false)
    }
    requires {
      pre.0():
        %v.5 : base.Bool = ops.attempt ^fail.1() {
          c.0():
            %v.6 : base.Int = ops.div(%v.0, %v.0) ^stop.0()
            jump ^c.1()
          c.1():
            unreachable
          stop.0(%v.7 : base.Int):
            unreachable
        }
        ret(%v.5)
      fail.1(%v.8 : base.Int):
        ret(false)
    }
  {
    entry.0(%v.0 : base.Int):
      ret(%v.0)
  }
} -/
#guard_msgs in
#eval IO.println ((chainFn 1).format {})

-- The checks of a contract's regions, `Func.ContractRegionsWF`.
#guard_msgs in
#eval scalesLinearly "the checks of contract regions" 1000 (twice chainFn) fun fn =>
  decide fn.ContractRegionsWF

/-! ## Dominance where many blocks jump to one block -/

private abbrev intT : TypeExpr Ops.env := Base.Int

private abbrev boolT : TypeExpr Ops.env := Base.Bool

/-- `%v.k : t`. -/
private def v (k : Nat) (t : TypeExpr Ops.env) : ValDecl Ops.env := ⟨⟨k⟩, t⟩

private def lbl (stem : String) (i : Nat) : Label := ⟨.num (nm stem) i⟩

/-- The blocks `b.0` to `b.(n-1)`: each `b.i` defines `%v.(first+i)` as `%v.0` divided by
itself, its failure going to `fail.0`, and jumps to `b.(i+1)`, or to `exit` if it is the last.
`b.0` takes the parameters `params`. -/
private def failChain (n first : Nat) (params : Array (ValDecl Ops.env)) (exit : Label) :
    Array (Block Ops.env Unit) :=
  (Array.range n).map fun i =>
    { label := lbl "b" i, params := if i = 0 then params else #[], info := ()
      instrs := #[.apply () (v (first + i) intT) Ops.div.ref ⟨#[], rfl⟩ #[⟨0⟩, ⟨0⟩]
        #[⟨lbl "fail" 0, #[]⟩] #[]]
      term := .jump () ⟨if i + 1 = n then exit else lbl "b" (i + 1), #[]⟩ }

/-- `@m.f(%v.0 : base.Int) -> base.Int`, whose body is the chain `failChain n 1` from `b.0` to
`b.n`, which returns `%v.0`, and `fail.0`, which returns the error. -/
private def bodyChainFn (n : Nat) : Func Ops.env Unit :=
  { name := .str (nm "m") "f", params := #[v 0 intT], retType := intT, info := ()
    blocks := failChain n 1 #[v 0 intT] (lbl "b" n) ++ #[
      { label := lbl "b" n, params := #[], instrs := #[], term := .ret () ⟨0⟩, info := () },
      { label := lbl "fail" 0, params := #[v (n + 1) intT], instrs := #[], term := .ret () ⟨n + 1⟩,
        info := () }]
    names := (Array.range (n + 2)).map (.num (nm "v")) }

/-- `@m.f(%v.0 : base.Int) -> base.Int`, which returns `%v.0`, with a `requires` clause that is
the chain `failChain n 1` from `b.0` to `b.n`, which returns `true`, and `fail.0`, which returns
`false`. -/
private def clauseChainFn (n : Nat) : Func Ops.env Unit :=
  let clause : Region Ops.env Unit := ⟨failChain n 1 #[] (lbl "b" n) ++ #[
    { label := lbl "b" n, params := #[], instrs := #[.const () (v (n + 1) boolT) (.bool true)],
      term := .ret () ⟨n + 1⟩, info := () },
    { label := lbl "fail" 0, params := #[v (n + 2) intT],
      instrs := #[.const () (v (n + 3) boolT) (.bool false)], term := .ret () ⟨n + 3⟩,
      info := () }]⟩
  { name := .str (nm "m") "f", params := #[v 0 intT], retType := intT, info := ()
    blocks := #[
      { label := lbl "entry" 0, params := #[v 0 intT], instrs := #[], term := .ret () ⟨0⟩,
        info := () }]
    contract := { requires := #[{ region := clause }] }
    names := (Array.range (n + 4)).map (.num (nm "v")) }

/-- `@m.f(%v.0 : base.Int) -> base.Int`, whose body is a loop, as a `for` loop is translated:
`entry.0` jumps to the loop's head `head.0`, which divides `%v.0` by itself, its failure going to
the loop's exit `stop.0`, and jumps to the body, the chain `failChain n 2` from `b.0` back to
`head.0`.  `stop.0` divides too, its failure going to `fail.0`, and returns `%v.0`; `fail.0`
returns the error.  The depth-first search enters `stop.0` before the body, so `stop.0` comes after
the body in its order. -/
private def loopFn (n : Nat) : Func Ops.env Unit :=
  let div (k : Nat) (to : Label) : Instruction Ops.env Unit :=
    .apply () (v k intT) Ops.div.ref ⟨#[], rfl⟩ #[⟨0⟩, ⟨0⟩] #[⟨to, #[]⟩] #[]
  { name := .str (nm "m") "f", params := #[v 0 intT], retType := intT, info := ()
    blocks := #[
      { label := lbl "entry" 0, params := #[v 0 intT], instrs := #[],
        term := .jump () ⟨lbl "head" 0, #[]⟩, info := () },
      { label := lbl "head" 0, params := #[], instrs := #[div 1 (lbl "stop" 0)],
        term := .jump () ⟨lbl "b" 0, #[]⟩, info := () }] ++
      failChain n 2 #[] (lbl "head" 0) ++ #[
      { label := lbl "stop" 0, params := #[v (n + 2) intT], instrs := #[div (n + 3) (lbl "fail" 0)],
        term := .ret () ⟨0⟩, info := () },
      { label := lbl "fail" 0, params := #[v (n + 4) intT], instrs := #[], term := .ret () ⟨n + 4⟩,
        info := () }]
    names := (Array.range (n + 5)).map (.num (nm "v")) }

-- At a small size, the functions are well formed, and print as their docstrings say.
#guard decide (bodyChainFn 3).WF ∧ decide (clauseChainFn 3).WF ∧ decide (loopFn 3).WF

/-- info: module m.f {
  func @m.f(%v.0 : base.Int) -> base.Int {
    b.0(%v.0 : base.Int):
      %v.1 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
      jump ^b.1()
    b.1():
      %v.2 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
      jump ^b.2()
    b.2():
      ret(%v.0)
    fail.0(%v.3 : base.Int):
      ret(%v.3)
  }
}

module m.f {
  func @m.f(%v.0 : base.Int) -> base.Int
    requires {
      b.0():
        %v.1 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
        jump ^b.1()
      b.1():
        %v.2 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
        jump ^b.2()
      b.2():
        ret(true)
      fail.0(%v.4 : base.Int):
        ret(false)
    }
  {
    entry.0(%v.0 : base.Int):
      ret(%v.0)
  }
}

module m.f {
  func @m.f(%v.0 : base.Int) -> base.Int {
    entry.0(%v.0 : base.Int):
      jump ^head.0()
    head.0():
      %v.1 : base.Int = ops.div(%v.0, %v.0) ^stop.0()
      jump ^b.0()
    b.0():
      %v.2 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
      jump ^b.1()
    b.1():
      %v.3 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
      jump ^head.0()
    stop.0(%v.4 : base.Int):
      %v.5 : base.Int = ops.div(%v.0, %v.0) ^fail.0()
      ret(%v.0)
    fail.0(%v.6 : base.Int):
      ret(%v.6)
  }
}
-/
#guard_msgs in
#eval do
  IO.println ((bodyChainFn 2).format {})
  IO.println ((clauseChainFn 2).format {})
  IO.println ((loopFn 2).format {})

-- The dominance check computes each body's dominator tree.  Here every block of the chain has an
-- edge to `fail.0`, whose immediate dominator is the start of `b.0`.
#guard_msgs in
#eval scalesLinearly "a function body whose blocks all jump to one block" 1000
  (twice bodyChainFn) fun fn => decide fn.WF

#guard_msgs in
#eval scalesLinearly "a contract clause whose blocks all jump to one block" 1000
  (twice clauseChainFn) fun fn => decide fn.WF

-- In the loop, the immediate dominator of `fail.0` is the start of `head.0`.  The search's order
-- lists `stop.0` after the body, so `stop.0` comes before the body among the points that jump to
-- `fail.0`.
#guard_msgs in
#eval scalesLinearly "a loop whose blocks all jump to one block" 1000
  (twice loopFn) fun fn => decide fn.WF

end Strata.Dyn.ScaleTest
