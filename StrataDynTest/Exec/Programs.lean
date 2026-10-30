/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.TestEnv
public import StrataDyn.IR
public import StrataDyn.WF
public import StrataDyn.DomCompute
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Programs to run

Functions over `Ex`, written as IR terms.  Each section exercises one part of the machine;
`RunTest.lean` runs them.
-/

namespace Strata.Dyn.ExecTest.Programs

@[expose] public section

abbrev E := Ex.env

def intT : TypeExpr E := Base.Int
def boolT : TypeExpr E := Base.Bool
def unitT : TypeExpr E := Base.Unit
def excT : TypeExpr E := Base.Except intT intT
def refT : TypeExpr E := Base.Ref intT

/-- `base.Fn as r`: a code pointer to functions taking `as` and returning `r`. -/
def fnT (as : Array (TypeExpr E)) (r : TypeExpr E) : TypeExpr E := Base.Fn (TypeList.ofTypes as) r

/-- A code pointer from `Int` to `Except Int Int`. -/
def excFnT : TypeExpr E := fnT #[intT] excT

/-- `%n : t`. -/
def d (n : Nat) (t : TypeExpr E) : ValDecl E := ⟨⟨n⟩, t⟩

/-- The block called `s`. -/
def lbl (s : String) : Dyn.Label := ⟨.str .base s⟩

/-- A transfer to `s`, binding `args`. -/
def to (s : String) (args : List Nat := []) : Target.Raw := ⟨lbl s, (args.map ValId.mk).toArray⟩

/-- A transfer to the body's exit, with `x`. -/
def out (x : Nat) : Target.Raw := ⟨Dyn.Label.exit, #[⟨x⟩]⟩

/-- `%n : t = c`. -/
def cst (n : Nat) (t : TypeExpr E) (c : Const) : Instruction E Unit := .const () (d n t) c

/-- `%n : t = r[targs] args succs regions`. -/
def app {isig : InsnSig E} (n : Nat) (t : TypeExpr E) (r : InsnRef E isig)
    (targs : TypeArgs E isig.scope) (args : List Nat)
    (succs : List Target.Raw := []) (regions : List (Dyn.Region E Unit) := []) :
    Instruction E Unit :=
  .apply () (d n t) r targs (args.map ValId.mk).toArray succs.toArray regions.toArray

/-- `ex.goto k`. -/
def goto (k : Target.Raw) : Terminator E Unit := .apply () Ex.goto.ref ⟨#[], rfl⟩ #[] #[k] #[]

/-- Leave the body with `%x`. -/
def ret (x : Nat) : Terminator E Unit := goto (out x)

/-- `ex.br %c t f`. -/
def br (c : Nat) (t f : Target.Raw) : Terminator E Unit :=
  .apply () Ex.br.ref ⟨#[], rfl⟩ #[⟨c⟩] #[t, f] #[]

/-- A block. -/
def blk (s : String) (params : List (ValDecl E)) (instrs : List (Instruction E Unit))
    (t : Terminator E Unit) : Block E Unit :=
  ⟨lbl s, params.toArray, instrs.toArray, t, ()⟩

/-- A region of blocks. -/
def region (bs : List (Block E Unit)) : Dyn.Region E Unit := ⟨bs.toArray⟩

/-- A function of the blocks `bs`, its values named `%v.0`, `%v.1`, …. -/
def fn (s : String) (ret : TypeExpr E) (bs : List (Block E Unit)) : Func E Unit :=
  let f : Func E Unit := ⟨.str .base s, ret, bs.toArray, #[], ()⟩
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- The module of `fs`, checked, or a fault that names the functions that are not well
formed. -/
def mod (fs : List (Func E Unit)) : Except Exec.Fault (Module E Unit) :=
  (Module.Raw.check ⟨.str .base "m", fs.toArray, ()⟩).mapError fun ns =>
    .invalid s!"not well formed: {ns.toList.map Exec.nameStr}"

/-- A function's name. -/
def nm (s : String) : Name := .str .base s

/-! ## Straight-line code

`arith(a, b) = a + b - 1`. -/

def arith : Func E Unit := fn "arith" intT [
  blk "entry" [d 0 intT, d 1 intT] [
    app 2 intT Ex.add.ref ⟨#[], rfl⟩ [0, 1],
    cst 3 intT (.int 1),
    app 4 intT Ex.sub.ref ⟨#[], rfl⟩ [2, 3]]
  (ret 4)]

/-! ## A block loop

`sum(n)`: `0 + 1 + … + (n - 1)`.  The header reads `n` from the entry block, by its scope, and
takes the counter and the total as parameters. -/

def sum : Func E Unit := fn "sum" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 0)] (goto (to "head" [1, 1])),
  blk "head" [d 2 intT, d 3 intT] [app 4 boolT Ex.lt.ref ⟨#[], rfl⟩ [2, 0]] (br 4 (to "body") (to "done")),
  blk "body" [] [
    app 5 intT Ex.add.ref ⟨#[], rfl⟩ [3, 2],
    cst 6 intT (.int 1),
    app 7 intT Ex.add.ref ⟨#[], rfl⟩ [2, 6]]
  (goto (to "head" [7, 5])),
  blk "done" [] [] (ret 3)]

/-! ## A raising operation

`safeDiv(a, b)`: `a / b`, or `-1` from the handler when `b` is `0`. -/

def safeDiv : Func E Unit := fn "safeDiv" intT [
  blk "entry" [d 0 intT, d 1 intT] [app 2 intT Ex.div.ref ⟨#[], rfl⟩ [0, 1] [to "err"]] (ret 2),
  blk "err" [d 3 intT] [cst 4 intT (.int (-1))] (ret 4)]

/-! ## Calls

Functions return `Except Int Int`; `ex.call` raises an `error` along its `^err`.  `chain(n)`
calls `inc`, then `fail`, whose error its handler catches: `chain 5 = 106`.  `fib` calls
itself.  `bad` takes a pointer to `chain` at a signature `chain` does not have, so it is not
well formed. -/

def inc : Func E Unit := fn "inc" excT [
  blk "entry" [d 0 intT] [
    cst 1 intT (.int 1),
    app 2 intT Ex.add.ref ⟨#[], rfl⟩ [0, 1],
    app 3 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [2]]
  (ret 3)]

def fail : Func E Unit := fn "fail" excT [
  blk "entry" [d 0 intT] [app 1 excT Base.Except.error.ref ⟨#[.ty intT, .ty intT], rfl⟩ [0]]
    (ret 1)]

def chain : Func E Unit := fn "chain" intT [
  blk "entry" [d 0 intT] [
    cst 1 excFnT (.func (nm "inc")),
    app 2 intT Ex.call.ref ⟨#[], rfl⟩ [1, 0] [to "err"],
    cst 3 excFnT (.func (nm "fail")),
    app 4 intT Ex.call.ref ⟨#[], rfl⟩ [3, 2] [to "err"]]
  (ret 4),
  blk "err" [d 5 intT] [cst 6 intT (.int 100), app 7 intT Ex.add.ref ⟨#[], rfl⟩ [5, 6]] (ret 7)]

def fib : Func E Unit := fn "fib" excT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 2), app 2 boolT Ex.lt.ref ⟨#[], rfl⟩ [0, 1]]
    (br 2 (to "small") (to "big")),
  blk "small" [] [app 3 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [0]] (ret 3),
  blk "big" [] [
    cst 4 excFnT (.func (nm "fib")),
    cst 5 intT (.int 1),
    app 6 intT Ex.sub.ref ⟨#[], rfl⟩ [0, 5],
    app 7 intT Ex.call.ref ⟨#[], rfl⟩ [4, 6] [to "err"],
    cst 8 intT (.int 2),
    app 9 intT Ex.sub.ref ⟨#[], rfl⟩ [0, 8],
    app 10 intT Ex.call.ref ⟨#[], rfl⟩ [4, 9] [to "err"],
    app 11 intT Ex.add.ref ⟨#[], rfl⟩ [7, 10],
    app 12 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [11]]
  (ret 12),
  blk "err" [d 13 intT] [app 14 excT Base.Except.error.ref ⟨#[.ty intT, .ty intT], rfl⟩ [13]]
    (ret 14)]

def bad : Func E Unit := fn "bad" intT [
  blk "entry" [d 0 intT] [
    cst 1 excFnT (.func (nm "chain")),
    app 2 intT Ex.call.ref ⟨#[], rfl⟩ [1, 0] [to "err"]]
  (ret 2),
  blk "err" [d 3 intT] [] (ret 3)]

/-! ## Static calls

`base.callCode` calls a typed code pointer, which validation checks against its function once.
`fibC` calls itself; `twice` takes a pointer as an argument, and `viaCell` calls one read from a
cell.  `badC` types a constant at a signature its function does not have. -/

/-- `%n : r = base.callCode[[as], r] %f args`. -/
def callC (n : Nat) (as : Array (TypeExpr E)) (r : TypeExpr E) (f : Nat) (args : List Nat) :
    Instruction E Unit :=
  app n r Base.callCode.ref ⟨#[.list (.ofTypes as), .ty r], rfl⟩ (f :: args)

def incI : Func E Unit := fn "incI" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 1), app 2 intT Ex.add.ref ⟨#[], rfl⟩ [0, 1]] (ret 2)]

def fibC : Func E Unit := fn "fibC" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 2), app 2 boolT Ex.lt.ref ⟨#[], rfl⟩ [0, 1]]
    (br 2 (to "small") (to "big")),
  blk "small" [] [] (ret 0),
  blk "big" [] [
    cst 3 (fnT #[intT] intT) (.func (nm "fibC")),
    cst 4 intT (.int 1),
    app 5 intT Ex.sub.ref ⟨#[], rfl⟩ [0, 4],
    callC 6 #[intT] intT 3 [5],
    cst 7 intT (.int 2),
    app 8 intT Ex.sub.ref ⟨#[], rfl⟩ [0, 7],
    callC 9 #[intT] intT 3 [8],
    app 10 intT Ex.add.ref ⟨#[], rfl⟩ [6, 9]]
  (ret 10)]

def twice : Func E Unit := fn "twice" intT [
  blk "entry" [d 0 (fnT #[intT] intT), d 1 intT] [
    callC 2 #[intT] intT 0 [1],
    callC 3 #[intT] intT 0 [2]]
  (ret 3)]

def useTwice : Func E Unit := fn "useTwice" intT [
  blk "entry" [d 0 intT] [
    cst 1 (fnT #[intT] intT) (.func (nm "incI")),
    cst 2 (fnT #[fnT #[intT] intT, intT] intT) (.func (nm "twice")),
    callC 3 #[fnT #[intT] intT, intT] intT 2 [1, 0]]
  (ret 3)]

def viaCell : Func E Unit := fn "viaCell" intT [
  blk "entry" [d 0 intT] [
    cst 1 (fnT #[intT] intT) (.func (nm "incI")),
    app 2 (Base.Ref (fnT #[intT] intT)) Base.refNew.ref ⟨#[.ty (fnT #[intT] intT)], rfl⟩ [1],
    app 3 (fnT #[intT] intT) Base.refGet.ref ⟨#[.ty (fnT #[intT] intT)], rfl⟩ [2],
    callC 4 #[intT] intT 3 [0]]
  (ret 4)]

def badC : Func E Unit := fn "badC" intT [
  blk "entry" [d 0 intT] [cst 1 (fnT #[intT] intT) (.func (nm "inc")), callC 2 #[intT] intT 1 [0]]
  (ret 2)]

/-! ## Closures

A rule calls a closure by `ex.callInt`, and the machine checks the call's tags against the
function's signature and what the closure captured: `typed` calls `incI`.  `closure(n)` binds a
ref holding `n` as the first argument of `addRef`, calls the closure by the rule and by
`base.callCode`, writes `n + 1` to the ref and calls it again, which sees the write:
`closure 5 = 6 + 6 + 7`. -/

def typed : Func E Unit := fn "typed" intT [
  blk "entry" [d 0 intT] [
    cst 1 (fnT #[intT] intT) (.func (nm "incI")),
    app 2 intT Ex.callInt.ref ⟨#[], rfl⟩ [1, 0]]
  (ret 2)]

/-- `addRef(c, x) = *c + x`. -/
def addRef : Func E Unit := fn "addRef" intT [
  blk "entry" [d 0 refT, d 1 intT] [
    app 2 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [0],
    app 3 intT Ex.add.ref ⟨#[], rfl⟩ [2, 1]]
  (ret 3)]

def closure : Func E Unit := fn "closure" intT [
  blk "entry" [d 0 intT] [
    app 1 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [0],
    cst 2 (fnT #[refT, intT] intT) (.func (nm "addRef")),
    app 3 (fnT #[intT] intT) Ex.bind.ref ⟨#[.ty refT, .ty intT, .ty intT], rfl⟩ [2, 1],
    cst 4 intT (.int 1),
    app 5 intT Ex.callInt.ref ⟨#[], rfl⟩ [3, 4],
    callC 6 #[intT] intT 3 [4],
    app 7 intT Ex.add.ref ⟨#[], rfl⟩ [0, 4],
    app 8 unitT Base.refSet.ref ⟨#[.ty intT], rfl⟩ [1, 7],
    app 9 intT Ex.callInt.ref ⟨#[], rfl⟩ [3, 4],
    app 10 intT Ex.add.ref ⟨#[], rfl⟩ [5, 6],
    app 11 intT Ex.add.ref ⟨#[], rfl⟩ [10, 9]]
  (ret 11)]

/-- `callsClo(n)`: count to `n` by a closure that adds the `1` its ref holds, called by the
rule. -/
def callsClo : Func E Unit := fn "callsClo" intT [
  blk "entry" [d 0 intT] [
    cst 1 intT (.int 0),
    cst 9 intT (.int 1),
    app 2 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [9],
    cst 3 (fnT #[refT, intT] intT) (.func (nm "addRef")),
    app 4 (fnT #[intT] intT) Ex.bind.ref ⟨#[.ty refT, .ty intT, .ty intT], rfl⟩ [3, 2]]
    (goto (to "head" [1])),
  blk "head" [d 5 intT] [app 6 boolT Ex.lt.ref ⟨#[], rfl⟩ [5, 0]] (br 6 (to "body") (to "done")),
  blk "body" [] [app 8 intT Ex.callInt.ref ⟨#[], rfl⟩ [4, 5]] (goto (to "head" [8])),
  blk "done" [] [] (ret 5)]

/-- `twiceAt(f, x)`: `f` called twice by `base.callCode`, on a closure it is given. -/
def twiceAt : Func E Unit := fn "twiceAt" intT [
  blk "entry" [d 0 (fnT #[intT] intT), d 1 intT] [
    callC 2 #[intT] intT 0 [1],
    callC 3 #[intT] intT 0 [2]]
  (ret 3)]

/-! ## The heap

A cell may be anywhere a value may.  `mkRef(x)` makes a cell holding `x`, or raises `1` when `x`
is `0`, and returns it in an `ok`; `useRef(x)` takes it out with `base.Except.case` and reads
it: the running example.  `slotRead(x)` puts a cell a rule made into a generated datatype and
reads it back; `bump(x)` reads and writes a machine cell through rules; `regionCell(x)` runs a
region on a cell a rule made; `cloCall(x)` calls a typed code pointer kept in a datatype.
`readInt(c)` and `readAfterBool(c)` read a cell they are given after making one of `Int` and one
of `Bool`, the machine's check; `ruleRead(c)` and `ruleReadAfterBool(c)` do the same through a
rule; `setInt(c)` and `setAfterBool(c)` write instead. -/

def refExcT : TypeExpr E := Base.Except intT refT
def slotT : TypeExpr E := Ex.Slot
def cloT : TypeExpr E := Ex.Clo

def mkRef : Func E Unit := fn "mkRef" refExcT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 0), app 2 boolT Ex.ne.ref ⟨#[], rfl⟩ [0, 1]]
    (br 2 (to "ok") (to "zero")),
  blk "ok" [] [
    app 3 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [0],
    app 4 refExcT Base.Except.ok.ref ⟨#[.ty intT, .ty refT], rfl⟩ [3]] (ret 4),
  blk "zero" [] [
    cst 5 intT (.int 1),
    app 6 refExcT Base.Except.error.ref ⟨#[.ty intT, .ty refT], rfl⟩ [5]] (ret 6)]

def useRef : Func E Unit := fn "useRef" excT [
  blk "entry" [d 0 intT] [cst 1 (fnT #[intT] refExcT) (.func (nm "mkRef")), callC 2 #[intT] refExcT 1 [0]]
    (.apply () Base.Except.case.ref ⟨#[.ty intT, .ty refT], rfl⟩ #[⟨2⟩] #[to "ok", to "err"] #[]),
  blk "ok" [d 3 refT] [
    app 4 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [3],
    app 5 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [4]] (ret 5),
  blk "err" [d 6 intT] [app 7 excT Base.Except.error.ref ⟨#[.ty intT, .ty intT], rfl⟩ [6]] (ret 7)]

def slotRead : Func E Unit := fn "slotRead" intT [
  blk "entry" [d 0 intT] [app 1 refT Ex.cellNew.ref ⟨#[], rfl⟩ [0], app 2 slotT Ex.Slot.slot.ref ⟨#[], rfl⟩ [1]]
    (.apply () Ex.Slot.case.ref ⟨#[], rfl⟩ #[⟨2⟩] #[to "got"] #[]),
  blk "got" [d 3 refT] [app 4 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [3]] (ret 4)]

def bump : Func E Unit := fn "bump" intT [
  blk "entry" [d 0 intT] [
    app 1 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [0],
    app 2 intT Ex.cellGet.ref ⟨#[], rfl⟩ [1],
    cst 3 intT (.int 1),
    app 4 intT Ex.add.ref ⟨#[], rfl⟩ [2, 3],
    app 5 unitT Ex.cellSet.ref ⟨#[], rfl⟩ [1, 4],
    app 6 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [1]] (ret 6)]

def regionCell : Func E Unit := fn "regionCell" intT [
  blk "entry" [d 0 intT] [
    app 1 intT Ex.withCell.ref ⟨#[], rfl⟩ [0] [] [
      region [blk "body" [d 2 refT] [
        app 3 intT Ex.cellGet.ref ⟨#[], rfl⟩ [2],
        cst 4 intT (.int 2),
        app 5 intT Ex.mul.ref ⟨#[], rfl⟩ [3, 4],
        app 6 unitT Ex.cellSet.ref ⟨#[], rfl⟩ [2, 5]] (ret 3)]]] (ret 1)]

def cloCall : Func E Unit := fn "cloCall" intT [
  blk "entry" [d 0 intT] [cst 1 (fnT #[intT] intT) (.func (nm "incI")), app 2 cloT Ex.Clo.clo.ref ⟨#[], rfl⟩ [1]]
    (.apply () Ex.Clo.case.ref ⟨#[], rfl⟩ #[⟨2⟩] #[to "got"] #[]),
  blk "got" [d 3 (fnT #[intT] intT)] [callC 4 #[intT] intT 3 [0]] (ret 4)]

/-- A cell of `Bool` and one of `Except Int Int`, made and read by the generic rules at their
types. -/
def genericCells : Func E Unit := fn "genericCells" intT [
  blk "entry" [d 0 intT] [
    cst 1 boolT (.bool true),
    app 2 (Base.Ref boolT) Ex.newAt.ref ⟨#[.ty boolT], rfl⟩ [1],
    app 3 boolT Ex.getAt.ref ⟨#[.ty boolT], rfl⟩ [2],
    app 4 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [0],
    app 5 (Base.Ref excT) Ex.newAt.ref ⟨#[.ty excT], rfl⟩ [4],
    app 6 excT Ex.getAt.ref ⟨#[.ty excT], rfl⟩ [5]]
    (.apply () Base.Except.case.ref ⟨#[.ty intT, .ty intT], rfl⟩ #[⟨6⟩] #[to "ok", to "err"] #[]),
  blk "ok" [d 7 intT] [] (ret 7),
  blk "err" [d 8 intT] [] (ret 8)]

/-- A cell `ex.cellNew` made, at `Int`, read by the generic rule at `Int`: one tag for both. -/
def genericInt : Func E Unit := fn "genericInt" intT [
  blk "entry" [d 0 intT] [
    app 1 refT Ex.cellNew.ref ⟨#[], rfl⟩ [0],
    app 2 intT Ex.getAt.ref ⟨#[.ty intT], rfl⟩ [1]] (ret 2)]

def boxT : TypeExpr E := Ex.Box intT
def twoT : TypeExpr E := Ex.Two intT

/-- `boxes(x)`: a box of a cell holding `x`, its `dup`, the original written to `0`, and the
copy read: `x`. -/
def boxes : Func E Unit := fn "boxes" intT [
  blk "entry" [d 0 intT] [
    app 1 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [0],
    app 2 boxT Ex.Box.box.ref ⟨#[.ty intT], rfl⟩ [1],
    app 3 boxT Ex.dup.ref ⟨#[.ty intT], rfl⟩ [2],
    cst 4 intT (.int 0),
    app 5 unitT Base.refSet.ref ⟨#[.ty intT], rfl⟩ [1, 4]]
    (.apply () Ex.Box.case.ref ⟨#[.ty intT], rfl⟩ #[⟨3⟩] #[to "got"] #[]),
  blk "got" [d 6 refT] [app 7 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [6]] (ret 7)]

/-- `swapped(x)`: two cells, holding `x` and `0`, swapped by `ex.swap`, and the first read:
`0`. -/
def swapped : Func E Unit := fn "swapped" intT [
  blk "entry" [d 0 intT] [
    cst 1 intT (.int 0),
    app 2 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [0],
    app 3 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [1],
    app 4 twoT Ex.Two.two.ref ⟨#[.ty intT], rfl⟩ [2, 3],
    app 5 twoT Ex.swap.ref ⟨#[.ty intT], rfl⟩ [4]]
    (.apply () Ex.Two.case.ref ⟨#[.ty intT], rfl⟩ #[⟨5⟩] #[to "got"] #[]),
  blk "got" [d 6 refT, d 7 refT] [app 8 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [6]] (ret 8)]

/-- `boxed(x)`: a cell holding a box of a cell holding `x`, made by a generic rule through
`Box`'s tag, read back: `x`. -/
def boxed : Func E Unit := fn "boxed" intT [
  blk "entry" [d 0 intT] [
    app 1 (Base.Ref boxT) Ex.boxCell.ref ⟨#[.ty intT], rfl⟩ [0],
    app 2 boxT Base.refGet.ref ⟨#[.ty boxT], rfl⟩ [1]]
    (.apply () Ex.Box.case.ref ⟨#[.ty intT], rfl⟩ #[⟨2⟩] #[to "got"] #[]),
  blk "got" [d 3 refT] [app 4 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [3]] (ret 4)]

/-- `name(c)`: make a cell holding `v`, of type `t`, then `use` the cell `c`. -/
def afterNew (name : String) (t : TypeExpr E) (v : Const) (use : Instruction E Unit) :
    Func E Unit := fn name intT [
  blk "entry" [d 0 refT] [cst 1 t v, app 2 (Base.Ref t) Base.refNew.ref ⟨#[.ty t], rfl⟩ [1], use]
    (ret 3)]

def readInt := afterNew "readInt" intT (.int 5) (app 3 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [0])
def readAfterBool :=
  afterNew "readAfterBool" boolT (.bool true) (app 3 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [0])
def ruleRead := afterNew "ruleRead" intT (.int 5) (app 3 intT Ex.cellGet.ref ⟨#[], rfl⟩ [0])
def ruleReadAfterBool :=
  afterNew "ruleReadAfterBool" boolT (.bool true) (app 3 intT Ex.cellGet.ref ⟨#[], rfl⟩ [0])

/-- `name(c)`: make a cell holding `v`, of type `t`, then write `7` to the cell `c` and read
it back. -/
def setAfterNew (name : String) (t : TypeExpr E) (v : Const) : Func E Unit := fn name intT [
  blk "entry" [d 0 refT] [
    cst 1 t v, app 2 (Base.Ref t) Base.refNew.ref ⟨#[.ty t], rfl⟩ [1],
    cst 3 intT (.int 7), app 4 unitT Base.refSet.ref ⟨#[.ty intT], rfl⟩ [0, 3],
    app 5 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [0]] (ret 5)]

def setInt := setAfterNew "setInt" intT (.int 5)
def setAfterBool := setAfterNew "setAfterBool" boolT (.bool true)

/-! ## Regions and cells

`count(n)` counts a cell up to `n` with `ex.loop`, whose condition and body are regions that
read the cell and `n` from the enclosing frame.  The loop runs again by a jump to its `Again`,
with the state `()`. -/

def count : Func E Unit := fn "count" intT [
  blk "entry" [d 0 intT] [
    cst 1 intT (.int 0),
    app 2 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [1],
    app 3 unitT Ex.loop.ref ⟨#[], rfl⟩ [] [] [
      region [blk "cond" [] [app 4 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [2], app 5 boolT Ex.lt.ref ⟨#[], rfl⟩ [4, 0]]
        (ret 5)],
      region [blk "body" [] [
        app 6 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [2],
        cst 7 intT (.int 1),
        app 8 intT Ex.add.ref ⟨#[], rfl⟩ [6, 7],
        app 9 unitT Base.refSet.ref ⟨#[.ty intT], rfl⟩ [2, 8]] (ret 9)]],
    app 10 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [2]]
  (ret 10)]

/-! ## Comprehensions

`squares(n, k)` squares `0, …, n - 1` with `ex.mapList`, whose body prints each element; it
returns the squares `ex.pack`ed, or, if the body raises at the element `k`, `-k`.
`squaresR(n, k)` is the same with `ex.mapRange`, whose first run only sets its state up.
`tables(n)` nests one comprehension in another's body: row `x` of `x * y` for `y` below `n`,
each row packed.  Each body reads the function's values, and the inner body the outer one's
element.  Each comprehension's state, the elements left and the results so far, is its
rule's, so the IR names none. -/

def seqT : TypeExpr E := Base.Sequence intT

/-- A comprehension's body on `%x`, with `%k` in scope: print `%x`, then `ok (x * x)`, or
`error x` if `x` is `k`.  It defines `%(x + 1)` to `%(x + 5)`. -/
def squareBody (x k : Nat) : Dyn.Region E Unit := region [
  blk "sq" [d x intT] [
    app (x + 1) unitT Ex.print.ref ⟨#[], rfl⟩ [x],
    app (x + 2) boolT Ex.ne.ref ⟨#[], rfl⟩ [x, k]]
    (br (x + 2) (to "sqOk") (to "sqErr")),
  blk "sqOk" [] [
    app (x + 3) intT Ex.mul.ref ⟨#[], rfl⟩ [x, x],
    app (x + 4) excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [x + 3]] (ret (x + 4)),
  blk "sqErr" [] [app (x + 5) excT Base.Except.error.ref ⟨#[.ty intT, .ty intT], rfl⟩ [x]]
    (ret (x + 5))]

/-- The handler of a comprehension's `^err`: `-code`. -/
def caught : Block E Unit :=
  blk "caught" [d 30 intT] [cst 31 intT (.int (-1)), app 32 intT Ex.mul.ref ⟨#[], rfl⟩ [30, 31]]
    (ret 32)

def squares : Func E Unit := fn "squares" intT [
  blk "entry" [d 0 intT, d 1 intT] [
    app 3 seqT Ex.range.ref ⟨#[], rfl⟩ [0],
    app 5 seqT Ex.mapList.ref ⟨#[], rfl⟩ [3] [to "caught"] [squareBody 10 1],
    app 6 intT Ex.pack.ref ⟨#[], rfl⟩ [5]]
  (ret 6),
  caught]

def squaresR : Func E Unit := fn "squaresR" intT [
  blk "entry" [d 0 intT, d 1 intT] [
    app 3 seqT Ex.mapRange.ref ⟨#[], rfl⟩ [0] [to "caught"] [squareBody 10 1],
    app 4 intT Ex.pack.ref ⟨#[], rfl⟩ [3]]
  (ret 4),
  caught]

def tables : Func E Unit := fn "tables" intT [
  blk "entry" [d 0 intT] [
    app 2 seqT Ex.range.ref ⟨#[], rfl⟩ [0],
    app 4 seqT Ex.mapList.ref ⟨#[], rfl⟩ [2] [to "caught"] [region [
      blk "row" [d 10 intT] [
        app 11 seqT Ex.mapList.ref ⟨#[], rfl⟩ [2] [to "rowErr"] [region [
          blk "cell" [d 20 intT] [
            app 21 intT Ex.mul.ref ⟨#[], rfl⟩ [10, 20],
            app 22 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [21]] (ret 22)]],
        app 12 intT Ex.pack.ref ⟨#[], rfl⟩ [11],
        app 13 excT Base.Except.ok.ref ⟨#[.ty intT, .ty intT], rfl⟩ [12]] (ret 13),
      blk "rowErr" [d 14 intT] [app 15 excT Base.Except.error.ref ⟨#[.ty intT, .ty intT], rfl⟩ [14]]
        (ret 15)]],
    app 5 intT Ex.pack.ref ⟨#[], rfl⟩ [4]]
  (ret 5),
  caught]

/-! ## A fold

`powAbove(n)` folds with `ex.fold` from `1`, doubling the accumulator while it is below `n`
and printing each one it doubles: the least power of two that is at least `n`.  The fold's
state is its accumulator. -/

def powAbove : Func E Unit := fn "powAbove" intT [
  blk "entry" [d 0 intT] [
    cst 1 intT (.int 1),
    app 2 intT Ex.fold.ref ⟨#[], rfl⟩ [1] [] [
      region [blk "cond" [d 10 intT] [app 11 boolT Ex.lt.ref ⟨#[], rfl⟩ [10, 0]] (ret 11)],
      region [blk "double" [d 20 intT] [
        app 21 unitT Ex.print.ref ⟨#[], rfl⟩ [20],
        cst 22 intT (.int 2),
        app 23 intT Ex.mul.ref ⟨#[], rfl⟩ [20, 22]] (ret 23)]]]
  (ret 2)]

/-! ## The world and the oracle

`noisy(n)` prints `n`, ticks twice, and adds the second tick to a number the oracle picks
from `0` to `n`. -/

def noisy : Func E Unit := fn "noisy" intT [
  blk "entry" [d 0 intT] [
    app 1 unitT Ex.print.ref ⟨#[], rfl⟩ [0],
    app 2 intT Ex.tick.ref ⟨#[], rfl⟩ [],
    app 3 intT Ex.tick.ref ⟨#[], rfl⟩ [],
    app 4 intT Ex.pick.ref ⟨#[], rfl⟩ [0],
    app 5 intT Ex.add.ref ⟨#[], rfl⟩ [3, 4]]
  (ret 5)]

/-- `coins()`: three choices from `0` to `9`, as the digits of the result. -/
def coins : Func E Unit := fn "coins" intT [
  blk "entry" [] [
    cst 0 intT (.int 9),
    app 1 intT Ex.pick.ref ⟨#[], rfl⟩ [0],
    app 2 intT Ex.pick.ref ⟨#[], rfl⟩ [0],
    app 3 intT Ex.pick.ref ⟨#[], rfl⟩ [0],
    cst 4 intT (.int 10),
    app 5 intT Ex.mul.ref ⟨#[], rfl⟩ [1, 4],
    app 6 intT Ex.add.ref ⟨#[], rfl⟩ [5, 2],
    app 7 intT Ex.mul.ref ⟨#[], rfl⟩ [6, 4],
    app 8 intT Ex.add.ref ⟨#[], rfl⟩ [7, 3]]
  (ret 8)]

/-! ## Faults

`gapAfter(x)` prints and then reaches a gap; `halts()` reaches `ex.halt`; `deep` calls `fib`
inside a region, so a fault there leaves a frame waiting. -/

def gapAfter : Func E Unit := fn "gapAfter" intT [
  blk "entry" [d 0 intT] [app 1 unitT Ex.print.ref ⟨#[], rfl⟩ [0], app 2 intT Ex.gap.ref ⟨#[], rfl⟩ [0]] (ret 2)]

def halts : Func E Unit := fn "halts" intT [
  blk "entry" [] [] (.apply () Ex.halt.ref ⟨#[], rfl⟩ #[] #[] #[])]

/-- The module of every function above. -/
def all : Except Exec.Fault (Module E Unit) :=
  mod [arith, sum, safeDiv, inc, fail, chain, fib, bad, count, noisy, coins, gapAfter, halts]

/-! ## Blocks out of dominator order

`sumLate` is `sum` with its loop header listed last, after the body and the exit, which it
dominates.  It is well formed, since `Func.WF` computes the dominator tree, whatever the
order. -/

def sumLate : Func E Unit := fn "sumLate" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 0)] (goto (to "head" [1, 1])),
  blk "done" [] [] (ret 3),
  blk "body" [] [
    app 5 intT Ex.add.ref ⟨#[], rfl⟩ [3, 2],
    cst 6 intT (.int 1),
    app 7 intT Ex.add.ref ⟨#[], rfl⟩ [2, 6]]
  (goto (to "head" [7, 5])),
  blk "head" [d 2 intT, d 3 intT] [app 4 boolT Ex.lt.ref ⟨#[], rfl⟩ [2, 0]]
    (br 4 (to "body") (to "done"))]

/-! ## Assumptions and unbounded choices

`assumePos(x) = x` on the path where `0 < x`, and no behaviour otherwise.  `pickN` returns the
oracle's number and `pickI` the integer it numbers, both unbounded; `pick2` a number from `0`
to `2`. -/

def assumePos : Func E Unit := fn "assumePos" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 0), app 2 boolT Ex.lt.ref ⟨#[], rfl⟩ [1, 0],
    app 3 unitT Ex.assume.ref ⟨#[], rfl⟩ [2]] (ret 0)]

def pickN : Func E Unit := fn "pickN" intT [
  blk "entry" [] [app 0 intT Ex.pickNat.ref ⟨#[], rfl⟩ []] (ret 0)]

def pickI : Func E Unit := fn "pickI" intT [
  blk "entry" [] [app 0 intT Ex.pickInt.ref ⟨#[], rfl⟩ []] (ret 0)]

def pick2 : Func E Unit := fn "pick2" intT [
  blk "entry" [] [cst 0 intT (.int 2), app 1 intT Ex.pick.ref ⟨#[], rfl⟩ [0]] (ret 1)]

/-! ## Cells updated in place, retyped, and of their own type

`cellAdds(x) = x + 1 + 2`, by two updates of one cell.  `pushes(n)` pushes `0, …, n - 1` onto a
sequence in a cell and packs it.  `retyped(x)` reads, at `Bool`, a cell holding `x`, through a
ref that `ex.retype` gave another contents' type; `retypedTwin(x)` reads the cell through its
own ref.  `links` makes a chain of two links, each in a cell, and follows it: `1`.  `thunks(x)`
stores, in a cell, a thunk whose closure returns a thunk, and calls through it twice: `x`. -/

def chainT : TypeExpr E := Ex.Chain
def thunkT : TypeExpr E := Ex.Thunk

def cellAdds : Func E Unit := fn "cellAdds" intT [
  blk "entry" [d 0 intT] [app 1 refT Ex.cellNew.ref ⟨#[], rfl⟩ [0], cst 2 intT (.int 1),
    app 3 unitT Ex.cellAdd.ref ⟨#[], rfl⟩ [1, 2], cst 4 intT (.int 2),
    app 5 unitT Ex.cellAdd.ref ⟨#[], rfl⟩ [1, 4], app 6 intT Ex.cellGet.ref ⟨#[], rfl⟩ [1]] (ret 6)]

def pushes : Func E Unit := fn "pushes" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 0), app 2 seqT Ex.range.ref ⟨#[], rfl⟩ [1],
    app 3 (Base.Ref seqT) Base.refNew.ref ⟨#[.ty seqT], rfl⟩ [2]] (goto (to "head" [1])),
  blk "head" [d 4 intT] [app 5 boolT Ex.lt.ref ⟨#[], rfl⟩ [4, 0]] (br 5 (to "body") (to "done")),
  blk "body" [] [app 6 unitT Ex.cellPush.ref ⟨#[], rfl⟩ [3, 4], cst 7 intT (.int 1),
    app 8 intT Ex.add.ref ⟨#[], rfl⟩ [4, 7]] (goto (to "head" [8])),
  blk "done" [] [app 9 seqT Base.refGet.ref ⟨#[.ty seqT], rfl⟩ [3], app 10 intT Ex.pack.ref ⟨#[], rfl⟩ [9]]
    (ret 10)]

def retyped : Func E Unit := fn "retyped" boolT [
  blk "entry" [d 0 intT] [app 1 refT Ex.cellNew.ref ⟨#[], rfl⟩ [0],
    app 2 (Base.Ref boolT) Ex.retype.ref ⟨#[], rfl⟩ [1],
    app 3 boolT Base.refGet.ref ⟨#[.ty boolT], rfl⟩ [2]] (ret 3)]

def retypedTwin : Func E Unit := fn "retypedTwin" intT [
  blk "entry" [d 0 intT] [app 1 refT Ex.cellNew.ref ⟨#[], rfl⟩ [0],
    app 2 (Base.Ref boolT) Ex.retype.ref ⟨#[], rfl⟩ [1],
    app 3 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [1]] (ret 3)]

def links : Func E Unit := fn "links" intT [
  blk "entry" [] [app 0 chainT Ex.Chain.done.ref ⟨#[], rfl⟩ [],
    app 1 (Base.Ref chainT) Base.refNew.ref ⟨#[.ty chainT], rfl⟩ [0],
    app 2 chainT Ex.Chain.link.ref ⟨#[], rfl⟩ [1],
    app 3 (Base.Ref chainT) Base.refNew.ref ⟨#[.ty chainT], rfl⟩ [2],
    app 4 chainT Base.refGet.ref ⟨#[.ty chainT], rfl⟩ [3]]
    (.apply () Ex.Chain.case.ref ⟨#[], rfl⟩ #[⟨4⟩] #[to "end0", to "next"] #[]),
  blk "end0" [] [cst 5 intT (.int 0)] (ret 5),
  blk "next" [d 6 (Base.Ref chainT)] [app 7 chainT Base.refGet.ref ⟨#[.ty chainT], rfl⟩ [6]]
    (.apply () Ex.Chain.case.ref ⟨#[], rfl⟩ #[⟨7⟩] #[to "end1", to "more"] #[]),
  blk "end1" [] [cst 8 intT (.int 1)] (ret 8),
  blk "more" [d 9 (Base.Ref chainT)] [cst 10 intT (.int 2)] (ret 10)]

def self : Func E Unit := fn "self" thunkT [
  blk "entry" [d 0 intT] [cst 1 (fnT #[intT] thunkT) (.func (nm "self")),
    app 2 thunkT Ex.Thunk.thunk.ref ⟨#[], rfl⟩ [1]] (ret 2)]

def thunks : Func E Unit := fn "thunks" intT [
  blk "entry" [d 0 intT] [cst 1 (fnT #[intT] thunkT) (.func (nm "self")),
    callC 2 #[intT] thunkT 1 [0],
    app 3 (Base.Ref thunkT) Base.refNew.ref ⟨#[.ty thunkT], rfl⟩ [2],
    app 4 thunkT Base.refGet.ref ⟨#[.ty thunkT], rfl⟩ [3]]
    (.apply () Ex.Thunk.case.ref ⟨#[], rfl⟩ #[⟨4⟩] #[to "got"] #[]),
  blk "got" [d 5 (fnT #[intT] thunkT)] [callC 6 #[intT] thunkT 5 [0]]
    (.apply () Ex.Thunk.case.ref ⟨#[], rfl⟩ #[⟨6⟩] #[to "got2"] #[]),
  blk "got2" [d 7 (fnT #[intT] thunkT)] [] (ret 0)]

/-! ## A closure over a list of cells

`addCells(c₁, c₂, x) = c₁ + c₂ + x`, reading two cells.  `twoCells(x)` makes cells holding `10`
and `20`, binds `addCells` to them with `ex.mkClo[[Ref Int, Ref Int]]`, writes `100` to the first,
and calls the closure on `x`: `100 + 20 + x`, since the closure holds the cells.  `noCells(x)`
binds no cell, so its closure is `incI`'s code pointer. -/

def addCells : Func E Unit := fn "addCells" intT [
  blk "entry" [d 0 refT, d 1 refT, d 2 intT] [
    app 3 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [0], app 4 intT Base.refGet.ref ⟨#[.ty intT], rfl⟩ [1],
    app 5 intT Ex.add.ref ⟨#[], rfl⟩ [3, 4], app 6 intT Ex.add.ref ⟨#[], rfl⟩ [5, 2]] (ret 6)]

def twoCells : Func E Unit := fn "twoCells" intT [
  blk "entry" [d 0 intT] [
    cst 1 intT (.int 10), app 2 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [1],
    cst 3 intT (.int 20), app 4 refT Base.refNew.ref ⟨#[.ty intT], rfl⟩ [3],
    cst 5 (fnT #[refT, refT, intT] intT) (.func (nm "addCells")),
    app 6 (fnT #[intT] intT) Ex.mkClo.ref ⟨#[.list (.ofTypes #[refT, refT])], rfl⟩ [5, 2, 4],
    cst 7 intT (.int 100), app 8 unitT Base.refSet.ref ⟨#[.ty intT], rfl⟩ [2, 7],
    callC 9 #[intT] intT 6 [0]] (ret 9)]

def noCells : Func E Unit := fn "noCells" intT [
  blk "entry" [d 0 intT] [
    cst 1 (fnT #[intT] intT) (.func (nm "incI")),
    app 2 (fnT #[intT] intT) Ex.mkClo.ref ⟨#[.list (.ofTypes #[])], rfl⟩ [1],
    callC 3 #[intT] intT 2 [0]] (ret 3)]

/-! ## Rejected before the first step -/

/-- Uses `ex.nope`, which has no rule. -/
def missing : Except Exec.Fault (Module E Unit) :=
  mod [fn "f" intT [blk "entry" [] [cst 0 intT (.int 1), app 1 intT Ex.nope.ref ⟨#[], rfl⟩ [0]] (ret 1)]]

/-- Reads `%1` in a block that it does not reach. -/
def unscoped : Except Exec.Fault (Module E Unit) := mod [fn "f" intT [
  blk "entry" [d 0 boolT] [] (br 0 (to "a") (to "b")),
  blk "a" [] [cst 1 intT (.int 1)] (goto (to "b")),
  blk "b" [] [] (ret 1)]]

end

end Strata.Dyn.ExecTest.Programs
