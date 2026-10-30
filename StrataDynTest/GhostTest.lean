/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDyn.DDM
public import StrataDyn.DDMRead
import StrataDyn.Build.Typed
import StrataDyn.Env.WF
import StrataDyn.DSL
import StrataDynTest.WFParts
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataDyn.Build
meta import StrataDyn.Build.Typed
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.WF
meta import StrataDyn.Env.WF
meta import StrataDynTest.WFParts

set_option autoImplicit false

/-!
# Ghost state

A ghost is a cell of the module that only contracts can name.  It holds a value of its type, and
may have an initializer, a region that gives its first value, and an invariant, a region that
takes its contents and returns a `base.Bool`.  `const ghost @m.g` is the ghost's cell, a
`base.Ref` of its type.  These rules of `Ghost.WF` apply to a ghost:

* `labels`, `unique names` and `names`: as for a function;
* `regions`: the initializer takes no arguments and returns the ghost's type, the invariant takes
  the ghost's contents and returns a `base.Bool` (G4); each sees only its own values, and applies
  no operation declared `writes` (E1);
* `failures`: a failure successor of their own blocks goes to a block that ends in `unreachable`
  (C2);
* `propagates`, `terminators` and `acyclic`, as in a clause (C3, C5, C4);
* `old`: neither applies `base.old` (O1);
* `invariant ghosts`: the invariant names no ghost, at any depth (G8);
* `func refs`: neither refers to a function, at any depth (G9).

The module's rules for ghosts, in `Module.Raw.WF`:

* `ghost names`: no two ghosts share a name, and no ghost has the name of a function (G1);
* `ghost refs`: each ghost constant names a ghost of the module, at the type of its cell (G2);
* `ghost order`: an initializer names only ghosts declared before its own (G5).

A function's body names no ghost, at any depth (`ghosts`, G3, in `Func.WF`).  A function's
attribute may name a ghost of the module (G7, the reader's rule).

Each module accepted here is built, printed, and read back unchanged.  Each case rejected here
breaks exactly one rule.  It is checked twice: a ghost, function or module that the builder emits
breaks that rule alone, and the reader names the problem in the printed form.  A few cases can be
stated on one side only, and their comments say so:

* the reader alone: a printed form that does not parse, and a second printed form of a case that
  is already built, such as a ghost constant written at its use;
* the builder alone: a value without a name, since reading names every value;
* attributes, which the checker does not look at: the builder prints an attribute that names a
  ghost, any ghost, and the reader rejects one that names no ghost of the module (G7).
-/

namespace Strata.Dyn.GhostTest

open Strata.Dyn.WFParts (broken failing)

/-- A comparison, an operation that may fail, an operation that runs a region, a terminal operation
that may fail, and a terminal operation that runs a region. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- `a / b`.  It fails, with an error code, when `b` is zero. -/
  calls insn div (a b : Int) (^err (e : Int)) : Int
  /-- Runs `body`: the value of an `ok`, or a transfer to `err` with the error of an `error`. -/
  pure insn attempt [a] (&body : Except Int a) (^err (e : Int)) : a
  /-- `a / b`, which ends its block: it continues at `ok` with the quotient, or at `err` when `b`
  is zero. -/
  pure terminal insn tryDiv (a b : Int) (^ok (q : Int)) (^err (e : Int))
  /-- Runs `body`, which ends its block, and continues at `k` with its value. -/
  pure terminal insn run (&body : Bool) (^k (b : Bool))
  end demo

open Strata.Dyn.Build (freshVal startBlock startFreshBlock freshLabel emitConst emitFunc
  emitApply emitGhost finishBlock terminate goto build FailedFunc FailedGhost region
  withFailureBlock withPropagatingBlock)

private abbrev E := Demo.env

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

/-- What `Build.ghost` gives: a checked ghost, or the `FailedGhost`. -/
private abbrev BuiltGhost := Except (FailedGhost E Unit) {g : Ghost E Unit // g.WF}

/-- The rules of `Ghost.WF` that `g` breaks, by name, with the parts of `Ghost.ContractRegionsWF`
each on its own. -/
private def brokenGhost (g : Ghost E Unit) : List String :=
  (if decide (Label.Distinct (Label.exit :: g.labels)) then [] else ["labels"]) ++
  (if decide g.names.toList.Nodup then [] else ["unique names"]) ++
  (if decide (ValDecl.idBound g.defs ≤ g.names.size) then [] else ["names"]) ++
  (if decide g.RegionsWF then [] else ["regions"]) ++
  (if decide (∀ r ∈ g.regions, r.FailsWith none) then [] else ["failures"]) ++
  (if decide (Region.Propagates g.regions) then [] else ["propagates"]) ++
  (if decide (Region.EndsInControl g.regions) then [] else ["terminators"]) ++
  (if decide (Region.Acyclic g.regions) then [] else ["acyclic"]) ++
  (if decide (Region.NoOld g.regions) then [] else ["old"]) ++
  (if decide g.InvariantNamesNoGhost then [] else ["invariant ghosts"]) ++
  (if decide g.NoFuncRefs then [] else ["func refs"])

/-- The rules that the ghost of a failed build breaks, by name, or `misuse` if the build failed
by a misuse. -/
private def ghostFailing (b : BuiltGhost) : List String :=
  match b with
  | .ok _ => []
  | .error e => if !e.misuses.isEmpty then ["misuse"] else brokenGhost e.ghost

/-- The rules of `Module.Raw.WF` that `m` breaks, by name. -/
private def brokenModule (m : Module.Raw E Unit) : List String :=
  (if decide m.funcNames.toList.Nodup then [] else ["func names"]) ++
  (if decide (∀ f ∈ m.funcs, f.WF) then [] else ["funcs"]) ++
  (if decide (∀ f ∈ m.funcs, ∀ u ∈ f.funcRefs, OptHolds (m.codeTypes.find? u.target) u.Fits)
    then [] else ["refs"]) ++
  (if decide (m.ghostNames ++ m.funcNames).toList.Nodup then [] else ["ghost names"]) ++
  (if decide (∀ g ∈ m.ghosts, g.WF) then [] else ["ghosts"]) ++
  (if decide m.GhostRefsWF then [] else ["ghost refs"]) ++
  (if decide m.GhostOrderWF then [] else ["ghost order"])

private def intT : TypeExpr E := Base.Int
private def boolT : TypeExpr E := Base.Bool
private def locT : TypeExpr E := Base.Loc
private def cellT : TypeExpr E := Base.Ref intT
/-- `base.Fn([], base.Int)`, the type of a code pointer to a function that takes no arguments and
returns a `base.Int`. -/
private def fnT : TypeExpr E := Base.Fn (TypeList.ofTypes #[]) intT
/-- `base.Except(base.Int, base.Int)`, what an `old` region or a region of `demo.attempt` of
`base.Int` returns. -/
private def exIntT : TypeExpr E := Base.Except intT intT

private def nm (s : String) : Name := .str .base s

/-- `m.s`, a name of the module `m`. -/
private def mn (s : String) : Name := .str (nm "m") s

/-- The module `m` of the ghosts `gs` and the functions `fs`, as built. -/
private def raw (gs : Array BuiltGhost) (fs : Array Built) : Module.Raw E Unit :=
  { name := nm "m", ghosts := gs.filterMap (·.toOption.map (·.val)),
    funcs := fs.filterMap (·.toOption.map (·.val)), info := () }

/-- The module `m` of the checked ghosts `gs` and functions `fs`, through `Module.ofChecked`, or
the names it gives; or `none` if a ghost or a function was not built. -/
private def checked (gs : Array BuiltGhost) (fs : Array Built) :
    Option (Except (Array Name) (Module E Unit)) := do
  let gs ← gs.mapM (·.toOption)
  let fs ← fs.mapM (·.toOption)
  return Module.ofChecked (nm "m") fs () (ghosts := gs)

/-- What `checked` gives, with names printed. -/
private def checkedText (gs : Array BuiltGhost) (fs : Array Built) : String :=
  match checked gs fs with
  | none => "not built"
  | some (.ok _) => "ok"
  | some (.error bad) => s!"{bad.map ToDDM.nameText}"

/-- Read `text` in `Demo.env`, and print the diagnostics, or the module if it prints otherwise. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-- Check that the module of the built ghosts `gs` and functions `fs` prints as `text`, and that
reading `text` gives it back.  Print the module where it differs, or the diagnostics. -/
private def agrees (gs : Array BuiltGhost) (fs : Array Built) (text : String) : IO Unit := do
  match checked gs fs with
  | none => IO.println "not built"
  | some (.error bad) => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
  | some (.ok m) => unless toString m == text do IO.println m
  readBack text

/-! ## Builders -/

/-- `refGet(ghost @<g>)`, named `n`, for a ghost `g` that holds a `base.Int`. -/
private def readGhostAt (g : Name) : BuildM E Unit ValId := do
  emitApply (nm "n") intT Base.refGet.ref #[← emitGhost g intT] (typeArgs := ta[intT])

/-- `refGet(ghost @m.<g>)`, named `n`, for a ghost that holds a `base.Int`. -/
private def readGhost (g : String) : BuildM E Unit ValId := readGhostAt (mn g)

/-- `x ≥ y`, returned. -/
private def retGe (x y : ValId) : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[x, y]))

/-- `0`, returned. -/
private def retZero : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitConst (nm "zero") (.int 0)))

/-- `v ≥ 0`, returned. -/
private def nonNeg (v : ValId) : BuildM E Unit Unit := do
  retGe v (← emitConst (nm "zero") (.int 0))

/-- `ok(v)`, returned from a region that returns a `base.Except(base.Int, base.Int)`. -/
private def retOk (v : ValId) : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitApply (nm "w") exIntT Base.Except.ok.ref #[v]))

/-- `attempt { body }`, named `n`, whose failure goes to `fail`: a region nested in the region
being emitted. -/
private def attempt (fail : Label) (body : BuildM E Unit Unit) : BuildM E Unit ValId :=
  emitApply (nm "n") intT Demo.attempt.ref #[] (succs := #[goto fail])
    (regions := #[region #[] (base := "body") body])

/-- `@m.<g>`, a `base.Int` with neither part. -/
private def plain (g : String) : BuiltGhost := Build.ghost (mn g) intT none none ()

/-- `@m.f() = 0`, whose contract `contract` emits. -/
private def zeroWith (contract : BuildM E Unit Unit) : Built :=
  build (mn "f") intT () do
    let _ ← startFreshBlock #[] "entry"
    retZero
    contract

/-! ## What the rules accept -/

/-- `@m.count`, a `base.Int` that starts at `0` and is never negative: a ghost with both parts. -/
private def count : BuiltGhost := Build.ghost (mn "count") intT (some retZero) (some nonNeg) ()

/-- `@m.log`, a `base.Int` with neither part. -/
private def log : BuiltGhost := plain "log"

/-- `@m.next`, which starts at the value of `@m.count` and is never negative: a ghost constant in a
later ghost's initializer. -/
private def next : BuiltGhost :=
  Build.ghost (mn "next") intT (some do finishBlock (.ret () (← readGhost "count")))
    (some nonNeg) ()

/-- The extern `@m.tick(x)`, which requires `x` to be at least the value of `@m.count`, promises
that `@m.count` does not decrease, and may change only `@m.count`: ghost constants in a
`requires` clause, in a `free ensures` clause, in an `old` region and in a frame region. -/
private def tick : Built :=
  Build.buildExtern (mn "tick") #[(nm "x", intT)] intT () fun ps => do
    let some x := ps[0]? | return
    Build.requires (do retGe x (← readGhost "count"))
    Build.ensures (nm "r") intT (free := true) fun _ =>
      withFailureBlock #[intT] (some true) fun fail => do
        let o ← Build.old (nm "o") intT intT fail fun _ => do retOk (← readGhost "count")
        retGe (← readGhost "count") o
    Build.writes #[.region do
      finishBlock (.ret () (← emitApply (nm "l") locT Base.cellLoc.ref
        #[← emitGhost (mn "count") intT] (typeArgs := ta[intT])))]

#guard ghostFailing count == [] && ghostFailing log == [] && ghostFailing next == []
#guard failing tick == []

-- The ghosts' values are numbered from `0`, the initializer's first, as `Ghost.defs` lists them.
#guard count.toOption.any (decide ·.val.Canonical)
#guard next.toOption.any (decide ·.val.Canonical)
#guard next.toOption.any fun g => g.val.defs.map (·.id.id) == List.range 5

-- The rules of the module hold.
#guard brokenModule (raw #[count, log, next] #[tick]) == []
#guard checkedText #[count, log, next] #[tick] == "ok"

private def mainText : String := "module m {
  ghost @m.count : base.Int = {
    init.0():
      ret(0)
  } invariant {
    inv.0(%v.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%v.0, 0)
      ret(%ok.0)
  }
  ghost @m.log : base.Int
  ghost @m.next : base.Int = {
    init.0():
      %n.0 : base.Int = base.refGet[base.Int](ghost @m.count)
      ret(%n.0)
  } invariant {
    inv.0(%v.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%v.0, 0)
      ret(%ok.0)
  }
  extern func @m.tick(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %n.0 : base.Int = base.refGet[base.Int](ghost @m.count)
        %ok.0 : base.Bool = demo.ge(%x.0, %n.0)
        ret(%ok.0)
    }
    free ensures {
      post.0(%r.0 : base.Int):
        %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
          old.0():
            %n.1 : base.Int = base.refGet[base.Int](ghost @m.count)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.1)
            ret(%w.0)
        }
        %n.2 : base.Int = base.refGet[base.Int](ghost @m.count)
        %ok.1 : base.Bool = demo.ge(%n.2, %o.0)
        ret(%ok.1)
      fail.0(%e.0 : base.Int):
        ret(true)
    }
    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](ghost @m.count)
        ret(%l.0)
    })
}
"

#guard_msgs in
#eval agrees #[count, log, next] #[tick] mainText

-- The ghosts read come in order, with their types and their parts.
#guard_msgs in
#eval show IO Unit from do
  match ← Module.read E mainText "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    unless m.raw.ghosts.toList.map (fun g => (ToDDM.nameText g.name, g.init.isSome,
        g.invariant.isSome)) ==
        [("m.count", true, true), ("m.log", false, false), ("m.next", true, true)] do
      IO.println "the ghosts differ"
    unless m.raw.ghosts.all (decide ·.Canonical) do IO.println "a ghost is not canonical"

-- `Module.Raw.map` keeps the ghosts: the mapped module prints the same.
#guard (checked #[count, log, next] #[tick]).any fun
  | .ok m => toString (m.raw.map fun _ => ({} : Info)) == toString m.raw
  | .error _ => false

/-- `@m.f() = 0`, which ensures that its result is at most the value of `@m.count`: a ghost
constant in a defined function's `ensures` clause. -/
private def bounded : Built :=
  build (mn "f") intT () do
    let _ ← startFreshBlock #[] "entry"
    retZero
    Build.ensures (nm "r") intT fun r => do retGe (← readGhost "count") r

#guard failing bounded == []

private def boundedText : String := "module m {
  ghost @m.count : base.Int = {
    init.0():
      ret(0)
  } invariant {
    inv.0(%v.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%v.0, 0)
      ret(%ok.0)
  }
  func @m.f() -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %n.0 : base.Int = base.refGet[base.Int](ghost @m.count)
        %ok.0 : base.Bool = demo.ge(%n.0, %r.0)
        ret(%ok.0)
    }
  {
    entry.0():
      ret(0)
  }
}
"

#guard_msgs in
#eval agrees #[count] #[bounded] boundedText

-- In full, a ghost constant is an instruction of its own, and the constants of a ghost are values
-- of the ghost.
/-- info: module m {
  ghost @m.count : base.Int = {
    init.0():
      %c.0 : base.Int = const 0
      ret(%c.0)
  } invariant {
    inv.0(%v.0 : base.Int):
      %c.1 : base.Int = const 0
      %ok.0 : base.Bool = demo.ge(%v.0, %c.1)
      ret(%ok.0)
  }
  func @m.f() -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %c.1 : base.Ref(base.Int) = const ghost @m.count
        %n.0 : base.Int = base.refGet[base.Int](%c.1)
        %ok.0 : base.Bool = demo.ge(%n.0, %r.0)
        ret(%ok.0)
    }
  {
    entry.0():
      %c.0 : base.Int = const 0
      ret(%c.0)
  }
} -/
#guard_msgs in
#eval do
  match ← Module.read E boundedText "t.dyn" with
  | .error e => IO.println e
  | .ok m => IO.println (m.format .full)

-- The full form reads back as printed.
#guard_msgs in
#eval do
  match ← Module.read E boundedText "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    let full := m.format .full
    match ← Module.read E full "t.dyn" with
    | .error e => IO.println e
    | .ok m₁ => unless m₁.format .full == full do IO.println (m₁.format .full)

/-- `@m.b`, which holds the cell of `@m.a`, and whose invariant reads that cell: the contents of
`@m.a` are never negative.  The invariant reads state other than the ghost's contents, which is a
trusted claim about every call that may change that state. -/
private def holder : BuiltGhost :=
  Build.ghost (mn "b") cellT (some do finishBlock (.ret () (← emitGhost (mn "a") intT)))
    (some fun v => do nonNeg (← emitApply (nm "n") intT Base.refGet.ref #[v] (typeArgs := ta[intT])))
    ()

-- A ghost may hold the cell of another ghost, and its invariant may read through its contents.
#guard_msgs in
#eval agrees #[plain "a", holder] #[] "module m {
  ghost @m.a : base.Int
  ghost @m.b : base.Ref(base.Int) = {
    init.0():
      ret(ghost @m.a)
  } invariant {
    inv.0(%v.0 : base.Ref(base.Int)):
      %n.0 : base.Int = base.refGet[base.Int](%v.0)
      %ok.0 : base.Bool = demo.ge(%n.0, 0)
      ret(%ok.0)
  }
}
"

/-- `@m.g`, whose invariant is `10 / v ≥ 0`, with the failure of the division unreachable. -/
private def divInv : BuiltGhost :=
  Build.ghost (mn "g") intT none (some fun v => withFailureBlock #[intT] none fun fail => do
    nonNeg (← emitApply (nm "q") intT Demo.div.ref #[← emitConst (nm "ten") (.int 10), v]
      (succs := #[goto fail]))) ()

/-- `@m.f() = 0`, which requires the contents of `@m.g`, read in a region of `demo.attempt`, to be
non-negative. -/
private def nestedReq : Built :=
  zeroWith (Build.requires (withFailureBlock #[intT] (some false) fun fail => do
    nonNeg (← attempt fail do retOk (← readGhost "g"))))

-- A ghost constant in a region nested in a clause, and an invariant whose failure is unreachable.
#guard_msgs in
#eval agrees #[divInv] #[nestedReq] "module m {
  ghost @m.g : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %q.0 : base.Int = demo.div(10, %v.0) ^fail.0()
      %ok.0 : base.Bool = demo.ge(%q.0, 0)
      ret(%ok.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }
  func @m.f() -> base.Int
    requires {
      pre.0():
        %n.0 : base.Int = demo.attempt[base.Int] ^fail.0() {
          body.0():
            %n.1 : base.Int = base.refGet[base.Int](ghost @m.g)
            %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.1)
            ret(%w.0)
        }
        %ok.0 : base.Bool = demo.ge(%n.0, 0)
        ret(%ok.0)
      fail.0(%e.0 : base.Int):
        ret(false)
    }
  {
    entry.0():
      ret(0)
  }
}
"

-- The labels of a ghost's regions are numbered together when the ghost is finished.  Here the
-- initializer's block `inv`, allocated `bb.0` and labelled by `named`, comes before the
-- invariant, so it is `inv.0`, and the invariant's entry, allocated `inv.0`, is `inv.1`.
#guard_msgs in
#eval agrees #[Build.ghost (mn "g") intT (some do
    let inv ← Build.named "inv" (Emit.freshLabel [] : BuildM E Unit (BlockRef E []))
    finishBlock (.jump () (goto inv.label))
    startBlock inv.label
    retZero) (some nonNeg) ()] #[] "module m {
  ghost @m.g : base.Int = {
    init.0():
      jump ^inv.0()
    inv.0():
      ret(0)
  } invariant {
    inv.1(%v.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%v.0, 0)
      ret(%ok.0)
  }
}
"

/-! ### Attributes may name ghosts (G7) -/

private def attrText (g : String) : String := s!"module m \{
  ghost @m.g : base.Int
  func @m.f() -> base.Int \{
    #[t.g = ghost @m.{g}]
    #[t.inv = [\{fn = @m.f, ghosts = [ghost @m.{g}]}]]

    entry.0():
      ret(0)
  }
}
"

/-- The module of `@m.g`, a `base.Int` with neither part, and `@m.f() = 0`, given the attributes
of `attrText g` after it is built. -/
private def attrModule (g : String) : Except String (Module E Info) := do
  let gh ← (Build.ghost (env := E) (mn "g") intT none none ({} : Info)).mapError toString
  let f ← (Build.build (env := E) (mn "f") intT ({} : Info) do
    let _ ← startFreshBlock #[] "entry"
    finishBlock (.ret {} (← emitConst (nm "zero") (.int 0)))).mapError toString
  let ref : AttrValue := .const (.ghost (mn g))
  let attrs : Array Attr := #[(.str (nm "t") "g", ref),
    (.str (nm "t") "inv", .list #[.record #[(nm "fn", .const (.func (mn "f"))),
      (nm "ghosts", .list #[ref])]])]
  (Module.ofChecked (nm "m") #[Func.setInfo f { attrs }] {} (ghosts := #[gh])).mapError
    fun bad => s!"{bad.map ToDDM.nameText}"

-- An attribute that names a ghost of the module is built, printed and read back.  A ghost named in
-- a fact is not a use under G3, so the body of `@m.f` may carry it.
#guard_msgs in
#eval match attrModule "g" with
  | .error e => IO.println e
  | .ok m => unless toString m == attrText "g" do IO.println m

#guard_msgs in
#eval readBack (attrText "g")

#guard_msgs in
#eval show IO Unit from do
  match ← Module.read E (attrText "g") "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    unless (m.raw.funcs[0]?.map (·.info.attrs.size)) == some 2 do IO.println "the attributes differ"

-- The checker does not look at attributes, so the builder prints one that names a ghost the module
-- lacks.  The reader rejects it.
#guard_msgs in
#eval match attrModule "h" with
  | .error e => IO.println e
  | .ok m => unless toString m == attrText "h" do IO.println m

/-- info: t.dyn:4:12: no ghost @m.h -/
#guard_msgs in
#eval readBack (attrText "h")

/-! ### Names spelled like the new keywords -/

/-- Read `text` in `Demo.env`, and print the diagnostics, or `read`. -/
private def readErrors (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok _ => IO.println "read"

-- `ghost` and `invariant` are keywords, so a one-segment name spelled like one of them reads only
-- pipe-delimited, and prints so.  The reader alone: the first form does not parse.
/-- info: t.dyn:1:6: unexpected token 'ghost'; expected Dyn.MName
t.dyn:1:6: unexpected token 'invariant'; expected Dyn.MName -/
#guard_msgs in
#eval show IO Unit from do
  for k in ["ghost", "invariant"] do
    readErrors s!"module {k} \{\n}\n"

#guard ["ghost", "invariant"].all fun k =>
  (Module.ofChecked (env := E) (α := Unit) (nm k) #[] ()).toOption.any
    (toString · == s!"module |{k}| \{\n}\n")

/-- info: module |ghost| {
}
module |invariant| {
} -/
#guard_msgs in
#eval show IO Unit from do
  for k in ["ghost", "invariant"] do
    match ← Module.read E s!"module |{k}| \{\n}\n" with
    | .error e => IO.println e
    | .ok m => IO.print m

-- A ghost named like a keyword is built, printed and read back, pipe-delimited.
#guard_msgs in
#eval agrees #[Build.ghost (nm "ghost") intT none none (),
    Build.ghost (nm "invariant") intT none (some nonNeg) ()] #[] "module m {
  ghost @|ghost| : base.Int
  ghost @|invariant| : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%v.0, 0)
      ret(%ok.0)
  }
}
"

/-! ## What the rules reject

Each case below has a builder half and a reader half, unless its comment says otherwise. -/

/-- The module `m` with the ghost lines `ghosts`, and the function `@m.f() -> base.Int` with the
contract lines `clauses`, returning `0`. -/
private def withGhosts (ghosts : String) (clauses : String := "") : String :=
  let sig := if clauses.isEmpty then "  func @m.f() -> base.Int {"
    else s!"  func @m.f() -> base.Int\n{clauses}\n  \{"
  s!"module m \{
{ghosts}
{sig}
    entry.0():
      ret(0)
  }
}
"

/-! ### A ghost's labels and value names -/

/-- `r` with its entry block labelled `init.0`. -/
private def asInit (r : Region E Unit) : Region E Unit :=
  ⟨r.blocks.modify 0 fun b => { b with label := ⟨.num (nm "init") 0⟩ }⟩

-- The initializer and the invariant share a label: `count`'s invariant, its entry relabelled
-- `init.0`.
#guard count.toOption.any fun g =>
  brokenGhost { g.val with invariant := g.val.invariant.map asInit } == ["labels"]

/-- info: t.dyn:6:4: block init.0 is defined twice -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      ret(0)
  } invariant {
    init.0(%v.0 : base.Int):
      ret(true)
  }")

-- Two values share a name.
#guard next.toOption.any fun g =>
  brokenGhost { g.val with names := (g.val.names.set! 0 (nm "n")).set! 1 (nm "n") } ==
    ["unique names"]

/-- info: t.dyn:9:10: %x.0 is defined twice -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      %x.0 : base.Int = demo.div(1, 1) ^fail.0()
      ret(%x.0)
    fail.0(%e.0 : base.Int):
      unreachable
  } invariant {
    inv.0(%x.0 : base.Int):
      ret(true)
  }")

-- A value without a name.  The builder alone: reading names every value.
#guard next.toOption.any fun g => brokenGhost { g.val with names := g.val.names.pop } == ["names"]

-- Ghosts come before the functions.  The reader alone: the printer writes the ghosts first.
/-- info: t.dyn:5:3: unexpected token 'ghost'; expected '}' -/
#guard_msgs in
#eval readBack "module m {
  func @m.f() -> base.Int {
    entry.0():
      ret(0)
  }
  ghost @m.g : base.Int
}
"

/-! ### G1: names -/

-- Two ghosts that share a name.
#guard brokenModule (raw #[log, log] #[]) == ["ghost names"]
#guard checkedText #[log, log] #[] == "#[m.log, m.log]"

/-- info: t.dyn:3:2: ghost @m.g is declared twice -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int\n  ghost @m.g : base.Bool")

-- A ghost named like a function.
#guard brokenModule (raw #[plain "f"] #[zeroWith (pure ())]) == ["ghost names"]

/-- info: t.dyn:2:2: @m.f names both a ghost and a function -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.f : base.Int")

/-! ### G2: a ghost constant names a ghost, at the type of its cell -/

-- A ghost that the module does not declare.
#guard brokenModule (raw #[] #[bounded]) == ["ghost refs"]
#guard checkedText #[] #[bounded] == "#[m.f]"

/-- info: t.dyn:6:48: no ghost @m.h -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int" "    requires {
      pre.0():
        %n.0 : base.Int = base.refGet[base.Int](ghost @m.h)
        %ok.0 : base.Bool = demo.ge(%n.0, 0)
        ret(%ok.0)
    }")

-- A ghost of another module.
#guard brokenModule (raw #[plain "g"] #[zeroWith (Build.requires do
  nonNeg (← readGhostAt (.str (nm "n") "g")))]) == ["ghost refs"]

/-- info: t.dyn:6:48: no ghost @n.g -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int" "    requires {
      pre.0():
        %n.0 : base.Int = base.refGet[base.Int](ghost @n.g)
        %ok.0 : base.Bool = demo.ge(%n.0, 0)
        ret(%ok.0)
    }")

-- A ghost constant of a ghost region that names no ghost: G2 only, not G5.
#guard brokenModule (raw #[next] #[]) == ["ghost refs"]

/-- info: t.dyn:4:46: no ghost @m.nope -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int = {
    init.0():
      %n.0 : base.Int = base.refGet[base.Int](ghost @m.nope)
      ret(%n.0)
  }")

-- A ghost constant at the wrong type: `@m.g` holds a `base.Int`, but its constant here is a
-- `base.Int` in the reader's case and a `base.Ref(base.Bool)` in the builder's.
#guard brokenModule (raw #[plain "g"] #[zeroWith (Build.requires do
  let c ← emitGhost (mn "g") boolT
  finishBlock (.ret () (← emitApply (nm "b") boolT Base.refGet.ref #[c] (typeArgs := ta[boolT]))))]) ==
  ["ghost refs"]

/-- info: t.dyn:6:32: ghost @m.g holds base.Int, so its constant has type base.Ref(base.Int), not base.Int -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int" "    requires {
      pre.0():
        %c.0 : base.Int = const ghost @m.g
        %ok.0 : base.Bool = demo.ge(%c.0, 0)
        ret(%ok.0)
    }")

-- The same, with the constant written at its use.  The reader alone: it is the same case in
-- another printed form.
/-- info: t.dyn:6:36: ghost @m.g holds base.Int, so its constant has type base.Ref(base.Int), not base.Int -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int" "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.ge(ghost @m.g, 0)
        ret(%ok.0)
    }")

/-! ### G3: only contracts name ghosts -/

-- A body that names a ghost.
private def bodyGhost : Built :=
  build (mn "k") intT () do
    let _ ← startFreshBlock #[] "entry"
    finishBlock (.ret () (← readGhost "count"))

#guard failing bodyGhost == ["ghosts"]

/-- info: t.dyn:5:40: @m.f uses ghost @m.g outside its contract -/
#guard_msgs in
#eval readBack "module m {
  ghost @m.g : base.Int
  func @m.f() -> base.Int {
    entry.0():
      %c.0 : base.Ref(base.Int) = const ghost @m.g
      %n.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%n.0)
  }
}
"

-- A region of an instruction of the body that names a ghost.
private def nestedBodyGhost : Built :=
  build (mn "k") intT () do
    let _ ← startFreshBlock #[] "entry"
    let fail ← freshLabel "fail"
    finishBlock (.ret () (← attempt fail do retOk (← readGhost "count")))
    let _ ← Build.startBlockWith fail (nm "e") intT
    Build.unreachable

#guard failing nestedBodyGhost == ["ghosts"]

/-- info: t.dyn:7:50: @m.f uses ghost @m.g outside its contract -/
#guard_msgs in
#eval readBack "module m {
  ghost @m.g : base.Int
  func @m.f() -> base.Int {
    entry.0():
      %v.0 : base.Int = demo.attempt[base.Int] ^fail.0() {
        body.0():
          %n.0 : base.Int = base.refGet[base.Int](ghost @m.g)
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.0)
          ret(%w.0)
      }
      ret(%v.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }
}
"

-- A region of a terminator of the body that names a ghost.
private def termBodyGhost : Built :=
  build (mn "k") intT () do
    let _ ← startFreshBlock #[] "entry"
    let k ← freshLabel "k"
    terminate Demo.run.ref (succs := #[goto k])
      (regions := #[region #[] (base := "body") do nonNeg (← readGhost "count")])
    let _ ← Build.startBlockWith k (nm "b") boolT
    retZero

#guard failing termBodyGhost == ["ghosts"]

/-- info: t.dyn:7:50: @m.f uses ghost @m.g outside its contract -/
#guard_msgs in
#eval readBack "module m {
  ghost @m.g : base.Int
  func @m.f() -> base.Int {
    entry.0():
      demo.run ^k.0() {
        body.0():
          %n.0 : base.Int = base.refGet[base.Int](ghost @m.g)
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
    k.0(%b.0 : base.Bool):
      ret(0)
  }
}
"

/-! ### G4: what an initializer and an invariant take and return -/

-- An initializer that returns a `base.Bool` for a ghost that holds a `base.Int`.
#guard ghostFailing (Build.ghost (mn "g") intT
  (some do finishBlock (.ret () (← emitConst (nm "t") (.bool true)))) none ()) == ["regions"]

/-- info: t.dyn:4:6: the initializer of ghost @m.g returns base.Bool, but the ghost holds base.Int -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      ret(true)
  }")

-- An initializer that returns the cell of another ghost, where its ghost holds a `base.Int`.
#guard ghostFailing (Build.ghost (mn "b") intT
  (some do finishBlock (.ret () (← emitGhost (mn "a") intT))) none ()) == ["regions"]

/-- info: t.dyn:5:6: the initializer of ghost @m.b returns base.Ref(base.Int), but the ghost holds base.Int -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int
  ghost @m.b : base.Int = {
    init.0():
      ret(ghost @m.a)
  }")

-- An initializer with an argument: the invariant of a `base.Int` ghost, which returns its
-- argument, in the place of the initializer.
private def withArg : Option (Ghost E Unit) :=
  match Build.ghost (mn "g") intT none (some fun v => finishBlock (.ret () v)) () with
  | .ok _ => none
  | .error e => some { e.ghost with init := e.ghost.invariant, invariant := none }

#guard withArg.any fun g => brokenGhost g == ["regions"]

/-- info: t.dyn:2:26: the initializer of ghost @m.g takes (base.Int), but an initializer takes no arguments -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0(%x.0 : base.Int):
      ret(%x.0)
  }")

-- An invariant with no argument: the initializer of a `base.Bool` ghost, which returns `true`, in
-- the place of the invariant of a `base.Int` ghost.
private def noArg : Option (Ghost E Unit) :=
  (Build.ghost (mn "g") boolT (some do finishBlock (.ret () (← emitConst (nm "t") (.bool true))))
    none ()).toOption.map fun b => { b.val with type := intT, init := none, invariant := b.val.init }

#guard noArg.any fun g => brokenGhost g == ["regions"]

/-- info: t.dyn:2:34: the invariant of ghost @m.g takes (), but an invariant takes the ghost's contents, (base.Int) -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int invariant {
    inv.0():
      ret(true)
  }")

-- An invariant that returns a `base.Int`.
#guard ghostFailing (Build.ghost (mn "g") intT none (some fun v => finishBlock (.ret () v)) ()) ==
  ["regions"]

/-- info: t.dyn:4:6: the invariant of ghost @m.g returns base.Int, but an invariant returns a base.Bool -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int invariant {
    inv.0(%v.0 : base.Int):
      ret(%v.0)
  }")

/-! ### G4: a ghost region sees only its own values -/

-- An invariant that uses a value of the initializer: `%n.0`, value 0.
#guard ghostFailing (Build.ghost (mn "g") intT (some retZero)
  (some fun v => retGe v ⟨0⟩) ()) == ["regions"]

/-- info: t.dyn:10:40: the invariant of ghost @m.g uses %n.0, which is not one of its own values -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      %n.0 : base.Int = demo.div(1, 1) ^fail.0()
      ret(%n.0)
    fail.0(%e.0 : base.Int):
      unreachable
  } invariant {
    inv.0(%v.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%v.0, %n.0)
      ret(%ok.0)
  }")

-- An initializer that uses a value on a path that avoids its definition.
#guard ghostFailing (Build.ghost (mn "g") intT (some (withFailureBlock #[intT] none fun fail => do
    let yes ← freshLabel "yes"
    let no ← freshLabel "no"
    let done ← freshLabel "done"
    let one ← emitConst (nm "one") (.int 1)
    let c ← emitApply (nm "c") boolT Demo.ge.ref #[one, ← emitConst (nm "zero") (.int 0)]
    finishBlock (.branch () c (goto yes) (goto no))
    startBlock yes
    let x ← emitApply (nm "x") intT Demo.div.ref #[one, one] (succs := #[goto fail])
    finishBlock (.jump () (goto done))
    startBlock no
    finishBlock (.jump () (goto done))
    startBlock done
    finishBlock (.ret () x))) none ()) == ["regions"]

/-- info: t.dyn:2:2: ghost @m.g is not well formed
  `%x.0` (defined in `yes.0`) is used in `done.0`, reachable via `init.0 → no.0 → done.0` without it -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      %c.0 : base.Bool = demo.ge(1, 0)
      branch(%c.0) ^yes.0() ^no.0()
    yes.0():
      %x.0 : base.Int = demo.div(1, 1) ^fail.0()
      jump ^done.0()
    no.0():
      jump ^done.0()
    done.0():
      ret(%x.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }")

-- An initializer that uses a value it does not define, such as one of a function.  The builder's
-- initializer returns the value `5`, which no value of the ghost is.
#guard ghostFailing (Build.ghost (mn "g") intT (some (finishBlock (.ret () ⟨5⟩))) none ()) ==
  ["regions"]

/-- info: t.dyn:4:10: %x.0 is not defined in its initializer -/
#guard_msgs in
#eval readBack "module m {
  ghost @m.g : base.Int = {
    init.0():
      ret(%x.0)
  }
  func @m.f(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      ret(%x.0)
  }
}
"

/-! ### G5: an initializer names only the ghosts declared before it -/

-- `@m.next` before `@m.count`, whose value its initializer reads.
#guard brokenModule (raw #[next, count] #[]) == ["ghost order"]
#guard checkedText #[next, count] #[] == "#[m.next]"

/-- info: t.dyn:4:46: the initializer of ghost @m.a names ghost @m.b, which is declared after it -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int = {
    init.0():
      %n.0 : base.Int = base.refGet[base.Int](ghost @m.b)
      ret(%n.0)
  }
  ghost @m.b : base.Int")

-- The same, in a region nested in the initializer.
#guard brokenModule (raw #[Build.ghost (mn "next") intT (some (withFailureBlock #[intT] none
    fun fail => do finishBlock (.ret () (← attempt fail do retOk (← readGhost "count"))))) none (),
  count] #[]) == ["ghost order"]

/-- info: t.dyn:6:50: the initializer of ghost @m.a names ghost @m.b, which is declared after it -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int = {
    init.0():
      %v.0 : base.Int = demo.attempt[base.Int] ^fail.0() {
        body.0():
          %n.0 : base.Int = base.refGet[base.Int](ghost @m.b)
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.0)
          ret(%w.0)
      }
      ret(%v.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }
  ghost @m.b : base.Int")

-- An initializer that reads its own ghost.
#guard brokenModule (raw #[Build.ghost (mn "count") intT
  (some do finishBlock (.ret () (← readGhost "count"))) none ()] #[]) == ["ghost order"]

/-- info: t.dyn:4:46: the initializer of ghost @m.a names its own ghost -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int = {
    init.0():
      %n.0 : base.Int = base.refGet[base.Int](ghost @m.a)
      ret(%n.0)
  }")

/-! ### G6: the rules for contract regions apply to ghost regions -/

-- `base.refSet` in an initializer.
#guard ghostFailing (Build.ghost (mn "b") intT (some do
    let _ ← emitApply (nm "u") Base.Unit Base.refSet.ref
      #[← emitGhost (mn "a") intT, ← emitConst (nm "one") (.int 1)] (typeArgs := ta[intT])
    retZero) none ()) == ["regions"]

/-- info: t.dyn:5:6: a contract region of ghost @m.b may not change state, but base.refSet is declared writes -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int
  ghost @m.b : base.Int = {
    init.0():
      %u.0 : base.Unit = base.refSet[base.Int](ghost @m.a, 1)
      ret(1)
  }")

-- An initializer that calls the code pointer that another ghost holds: `base.callCode` is declared
-- `writes`.
#guard ghostFailing (Build.ghost (mn "g") intT (some do
    let f ← emitApply (nm "f") fnT Base.refGet.ref #[← emitGhost (mn "code") fnT] (typeArgs := ta[fnT])
    finishBlock (.ret () (← emitApply (nm "r") intT Base.callCode.ref #[f]))) none ()) == ["regions"]

/-- info: t.dyn:6:6: a contract region of ghost @m.g may not change state, but base.callCode is declared writes -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.code : base.Fn([], base.Int)
  ghost @m.g : base.Int = {
    init.0():
      %f.0 : base.Fn([], base.Int) = base.refGet[base.Fn([], base.Int)](ghost @m.code)
      %r.0 : base.Int = base.callCode[[], base.Int](%f.0)
      ret(%r.0)
  }")

-- A failure in an invariant that goes to a block that returns `true`.
#guard ghostFailing (Build.ghost (mn "g") intT none (some fun v => do
    let fail ← freshLabel "fail"
    let q ← emitApply (nm "q") intT Demo.div.ref #[← emitConst (nm "ten") (.int 10), v]
      (succs := #[goto fail])
    nonNeg q
    let _ ← Build.startBlockWith fail (nm "e") intT
    finishBlock (.ret () (← emitConst (nm "t") (.bool true)))) ()) == ["failures"]

/-- info: t.dyn:4:6: in the invariant of ghost @m.g, the failure successor of %q.0 goes to fail.0, which returns true; a failure must be unreachable -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %q.0 : base.Int = demo.div(10, %v.0) ^fail.0()
      %ok.0 : base.Bool = demo.ge(%q.0, 0)
      ret(%ok.0)
    fail.0(%e.0 : base.Int):
      ret(true)
  }")

-- A failure in a region nested in an initializer that turns into a value.
#guard ghostFailing (Build.ghost (mn "g") intT (some (withFailureBlock #[intT] none fun fail => do
    let body := region #[] (base := "body") do
      let recover ← freshLabel "recover"
      retOk (← emitApply (nm "q") intT Demo.div.ref
        #[← emitConst (nm "one") (.int 1), ← emitConst (nm "zero") (.int 0)]
        (succs := #[goto recover]))
      let e ← Build.startBlockWith recover (nm "e") intT
      retOk e
    finishBlock (.ret () (← emitApply (nm "v") intT Demo.attempt.ref #[] (succs := #[goto fail])
      (regions := #[body]))))) none ()) == ["propagates"]

/-- info: t.dyn:6:10: in a region nested in a contract of ghost @m.g, the failure successor of %q.0 goes to recover.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      %v.0 : base.Int = demo.attempt[base.Int] ^fail.0() {
        body.0():
          %q.0 : base.Int = demo.div(1, 0) ^recover.0()
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%q.0)
          ret(%w.0)
        recover.0(%e.0 : base.Int):
          %w.1 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%e.0)
          ret(%w.1)
      }
      ret(%v.0)
    fail.0(%e.1 : base.Int):
      unreachable
  }")

-- A terminal operation with successors in an invariant.
#guard ghostFailing (Build.ghost (mn "g") intT none (some fun v => do
    let ok ← freshLabel "ok"
    let no ← freshLabel "no"
    terminate Demo.tryDiv.ref #[← emitConst (nm "ten") (.int 10), v] (succs := #[goto ok, goto no])
    nonNeg (← Build.startBlockWith ok (nm "q") intT)
    let _ ← Build.startBlockWith no (nm "e") intT
    Build.unreachable) ()) == ["terminators"]

/-- info: t.dyn:4:6: a contract region of ghost @m.g ends inv.0 with demo.tryDiv; a contract region may end a block only with ret, jump, branch, unreachable or a case instruction -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int invariant {
    inv.0(%v.0 : base.Int):
      demo.tryDiv(10, %v.0) ^ok.0() ^no.0()
    ok.0(%q.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%q.0, 0)
      ret(%ok.0)
    no.0(%e.0 : base.Int):
      unreachable
  }")

-- An initializer with a loop.
#guard ghostFailing (Build.ghost (mn "g") intT (some do
    let loop ← freshLabel "loop"
    let done ← freshLabel "done"
    finishBlock (.jump () (goto loop #[← emitConst (nm "zero") (.int 0)]))
    let n ← freshVal (nm "n") intT
    startBlock loop #[n]
    let ok ← emitApply (nm "ok") boolT Demo.ge.ref #[n.id, ← emitConst (nm "zero") (.int 0)]
    finishBlock (.branch () ok (goto done) (goto loop #[n.id]))
    startBlock done
    retZero) none ()) == ["acyclic"]

/-- info: t.dyn:5:4: a contract region of ghost @m.g has a cycle through loop.0 -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      jump ^loop.0(0)
    loop.0(%n.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%n.0, 0)
      branch(%ok.0) ^done.0() ^loop.0(%n.0)
    done.0():
      ret(0)
  }")

-- `base.old` in an initializer.
#guard ghostFailing (Build.ghost (mn "g") intT (some (withFailureBlock #[intT] none fun fail => do
    finishBlock (.ret () (← Build.old (nm "o") intT intT fail fun _ => do
      retOk (← emitConst (nm "zero") (.int 0)))))) none ()) == ["old"]

/-- info: t.dyn:4:6: base.old is allowed only in an ensures clause, but ghost @m.g uses it in its initializer -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
        old.0():
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](0)
          ret(%w.0)
      }
      ret(%o.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }")

-- `base.old` in an invariant.
#guard ghostFailing (Build.ghost (mn "g") intT none (some fun v =>
    withFailureBlock #[intT] none fun fail => do
      nonNeg (← Build.old (nm "o") intT intT fail fun _ => retOk v)) ()) == ["old"]

/-- info: t.dyn:4:6: base.old is allowed only in an ensures clause, but ghost @m.g uses it in its invariant -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
        old.0():
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
          ret(%w.0)
      }
      %ok.0 : base.Bool = demo.ge(%o.0, 0)
      ret(%ok.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }")

/-! ### G8: an invariant names no ghost -/

-- An invariant that reads another ghost.
#guard ghostFailing (Build.ghost (mn "b") intT none
  (some fun v => do retGe v (← readGhost "a")) ()) == ["invariant ghosts"]

/-- info: t.dyn:5:46: the invariant of ghost @m.b names ghost @m.a; an invariant receives the ghost's contents as its argument -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int
  ghost @m.b : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %n.0 : base.Int = base.refGet[base.Int](ghost @m.a)
      %ok.0 : base.Bool = demo.ge(%v.0, %n.0)
      ret(%ok.0)
  }")

-- An invariant that reads its own ghost's cell.
#guard ghostFailing (Build.ghost (mn "b") intT none
  (some fun v => do retGe v (← readGhost "b")) ()) == ["invariant ghosts"]

/-- info: t.dyn:4:46: the invariant of ghost @m.b names ghost @m.b; an invariant receives the ghost's contents as its argument -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.b : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %n.0 : base.Int = base.refGet[base.Int](ghost @m.b)
      %ok.0 : base.Bool = demo.ge(%v.0, %n.0)
      ret(%ok.0)
  }")

-- An invariant that reads another ghost in a region nested in it.
#guard ghostFailing (Build.ghost (mn "b") intT none (some fun v =>
    withFailureBlock #[intT] none fun fail => do
      retGe v (← attempt fail do retOk (← readGhost "a"))) ()) == ["invariant ghosts"]

/-- info: t.dyn:7:50: the invariant of ghost @m.b names ghost @m.a; an invariant receives the ghost's contents as its argument -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.a : base.Int
  ghost @m.b : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %n.0 : base.Int = demo.attempt[base.Int] ^fail.0() {
        body.0():
          %n.1 : base.Int = base.refGet[base.Int](ghost @m.a)
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%n.1)
          ret(%w.0)
      }
      %ok.0 : base.Bool = demo.ge(%v.0, %n.0)
      ret(%ok.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }")

/-! ### G9: a ghost region refers to no function -/

-- An initializer that returns a function reference.
#guard ghostFailing (Build.ghost (mn "code") fnT
  (some do finishBlock (.ret () (← emitFunc (mn "f") fnT))) none ()) == ["func refs"]

/-- info: t.dyn:4:10: the initializer of ghost @m.code refers to function @m.f; a ghost region may not refer to a function -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.code : base.Fn([], base.Int) = {
    init.0():
      ret(@m.f)
  }")

-- An invariant that holds a function reference.
#guard ghostFailing (Build.ghost (mn "g") intT none (some fun v => do
    let _ ← emitFunc (mn "f") fnT
    nonNeg v) ()) == ["func refs"]

/-- info: t.dyn:4:43: the invariant of ghost @m.g refers to function @m.f; a ghost region may not refer to a function -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int invariant {
    inv.0(%v.0 : base.Int):
      %c.0 : base.Fn([], base.Int) = const @m.f
      %ok.0 : base.Bool = demo.ge(%v.0, 0)
      ret(%ok.0)
  }")

-- A region nested in an initializer that holds a function reference.
#guard ghostFailing (Build.ghost (mn "g") intT (some (withFailureBlock #[intT] none fun fail => do
    finishBlock (.ret () (← attempt fail do
      let _ ← emitFunc (mn "f") fnT
      retOk (← emitConst (nm "zero") (.int 0)))))) none ()) == ["func refs"]

/-- info: t.dyn:6:47: the initializer of ghost @m.g refers to function @m.f; a ghost region may not refer to a function -/
#guard_msgs in
#eval readBack (withGhosts "  ghost @m.g : base.Int = {
    init.0():
      %v.0 : base.Int = demo.attempt[base.Int] ^fail.0() {
        body.0():
          %c.0 : base.Fn([], base.Int) = const @m.f
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](0)
          ret(%w.0)
      }
      ret(%v.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }")

/-! ## Checking a module

`Module.Raw.check` decides every rule, and gives the names of the ghosts and the functions that
break one.  `Module.ofChecked` decides only the module's own rules.  These tests are about what
`Module.Raw.check` gives, so they are the builder's alone; the reader's halves of their cases are
above. -/

-- A ghost that breaks a rule of `Ghost.WF`.
/-- info: #[m.g] -/
#guard_msgs in
#eval match Module.Raw.check (env := E) (α := Unit)
    { name := nm "m", ghosts := (noArg.map (#[·])).getD #[], funcs := #[], info := () } with
  | .ok _ => IO.println "ok"
  | .error bad => IO.println s!"{bad.map ToDDM.nameText}"

-- A function whose ghost constant names no ghost, and a ghost whose initializer names a later one.
private def stray : Built :=
  zeroWith (Build.requires do retGe (← readGhost "nope") (← emitConst (nm "zero") (.int 0)))

/-- info: #[m.f, m.next] -/
#guard_msgs in
#eval match Module.Raw.check (raw #[next, count] #[stray, tick]) with
  | .ok _ => IO.println "ok"
  | .error bad => IO.println s!"{bad.map ToDDM.nameText}"

#guard (Module.Raw.check (raw #[count, log, next] #[tick, bounded])).isOk

/-! ## The builder

A ghost's initializer and invariant are emitted by `Build.ghost`, which runs each body itself.  A
misuse of the builder is the builder's alone: the printed form cannot state it. -/

-- `emitConst` gives a ghost reference no type, so it records a misuse that names `emitGhost`, as it
-- names `emitFunc` for a function reference.
#guard (match build (mn "f") intT () (do
    let _ ← startFreshBlock #[] "entry"
    let _ ← emitConst (nm "g") (.ghost (mn "count"))
    retZero) with
  | .ok _ => #[]
  | .error e => e.misuses) ==
    #["%0: a ghost reference emitted as a literal, with no type; use emitGhost"]
#guard (match build (mn "f") intT () (do
    let _ ← startFreshBlock #[] "entry"
    let _ ← emitConst (nm "p") (.func (mn "f"))
    retZero) with
  | .ok _ => #[]
  | .error e => e.misuses) ==
    #["%0: a function reference emitted as a literal, with no type; use emitFunc"]

-- An initializer that leaves a block open.
#guard (match Build.ghost (env := E) (α := Unit) (mn "g") intT
    (some do let _ ← emitConst (nm "zero") (.int 0)) none () with
  | .ok _ => #[]
  | .error e => e.misuses) == #["region init ends with block init.0 open"]

/-! A front end in `ExceptT` can throw out of a region nested in an initializer and catch the
error outside it, as in `TypedEmitTest`.  The region is then never closed, and the initializer's
entry block is lost, so `Build.ghost` records a misuse. -/

/-- An initializer, `attempt` of a region that returns `ok(0)`, whose failure goes to `err`.
With `fail`, the region throws, which is caught by returning `1`. -/
private def attemptInit (err : Label) (fail : Bool) : ExceptT String (BuildM E Unit) Unit := do
  try
    let (body, _) ← Build.regionWith #[] (base := "body") do
      if fail then throw "unsupported"
      (do retOk (← emitConst (nm "zero") (.int 0)) : BuildM E Unit Unit)
    let n ← (emitApply (nm "n") intT Demo.attempt.ref #[] (succs := #[goto err])
      (regions := #[pure body]) : BuildM E Unit ValId)
    (finishBlock (.ret () n) : BuildM E Unit Unit)
  catch _ => (do finishBlock (.ret () (← emitConst (nm "one") (.int 1))) : BuildM E Unit Unit)

/-- The module of the ghost `@m.g : base.Int` whose initializer is `attemptInit`, printed, or the
misuses. -/
private def attemptGhost (fail : Bool) : String :=
  match Build.ghost (mn "g") intT
      (some (withFailureBlock #[intT] none fun err => do let _ ← (attemptInit err fail).run))
      none () with
  | .error e => toString e
  | .ok g => match Module.ofChecked (nm "m") #[] () (ghosts := #[g]) with
    | .ok m => toString m
    | .error _ => "the module is not well formed"

/-- info: module m {
  ghost @m.g : base.Int = {
    init.0():
      %n.0 : base.Int = demo.attempt[base.Int] ^fail.0() {
        body.0():
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](0)
          ret(%w.0)
      }
      ret(%n.0)
    fail.0(%e.0 : base.Int):
      unreachable
  }
} -/
#guard_msgs in
#eval IO.print (attemptGhost false)
/-- info: region init.0 is still open when the ghost ends: its body did not return -/
#guard_msgs in
#eval IO.print (attemptGhost true)

end Strata.Dyn.GhostTest
