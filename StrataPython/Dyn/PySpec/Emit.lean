/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Clause
public import StrataPython.Dyn.Build
public import StrataDyn.Attr
public import StrataPython.Dyn.Shape
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Emitting clauses

`value` and `cond` write a checked clause (`CExpr`) as blocks of a clause region of
`docs/PythonToDyn.md` §12, by the rules of §12.4. Every raising operation's failure goes to
the enclosing handler: the clause's failure block, or the propagating block of a quantifier's
or an `old`'s region. Nothing here can fail: the checker has made every decision.
-/

namespace StrataPython.Dyn.PySpec

open Strata.Dyn
open StrataPython.Dyn.PyBuild

public section

/-- What a clause's emission sees. -/
structure EmitCtx where
  /-- The extern's parameters `%args.0` and `%kwargs.0`. -/
  args : ValId
  kwargs : ValId
  /-- The `ok` value of a post-state clause's result. -/
  result : Option ValId := none
  /-- The binders in scope, and a predicate's parameters. -/
  binders : List (String × ValId) := []
  /-- The ghosts that an invariant predicate receives as parameters, by module and name. -/
  ghostParams : List ((String × String) × ValId) := []
  /-- Whether this is a `requires` clause, so that §12.4's stricter tests apply. -/
  requires : Bool := true
  /-- Whether this is a post-state clause, so that a parameter is read inside `base.old`. -/
  post : Bool := false
  /-- Whether the emission is inside a `base.old` region. -/
  inOld : Bool := false
  /-- The `strong` of `cond` at the condition that holds the value being emitted, which a
      condition in a value's position, such as `OLD(x != "A")`, takes on. -/
  strong : Bool := true
deriving Inhabited

abbrev EM := ReaderT EmitCtx (PyM Info)

/-- A value named after `s`. -/
def nm (s : String) : Name := .str .base s

/-- Run a generic builder step. -/
def buildPy {β : Type} (m : BuildM Py.env Info β) : EM β :=
  liftPy (α := Info) (monadLift m : PyM Info β)

/-- A string constant. -/
def strC (s : String) : EM ValId := liftPy (emitConst (nm "s") (.str s))

/-- A Boolean constant. -/
def boolC (b : Bool) : EM ValId := liftPy (emitConst (nm "b") (.bool b))

/-- The name of ghost `name` of module `module`: `module.<ghost>.name`. -/
def ghostName (module name : String) : Name :=
  let m := (module.splitOn ".").foldl (init := Name.base) fun n s => n.str s
  (m.str "<ghost>").str name

/-- Open a fresh block, labelled `base.n`, run `body` there, and give its result. -/
def inBlock {β : Type} (label : BlockRef Py.env []) (body : EM β) : EM β := do
  liftPy (startBlock label)
  body

/-- A fresh Python value, named after `stem`, to bind in a region. -/
def freshPyVal (stem : Name) : EM (ValDecl Py.env) :=
  liftPy (α := Info) (monadLift (Build.freshVal (α := Info) stem Py.Value) : PyM Info _)

/-- Join two branches on `c`, each giving a value of type `ty`, a base `Bool` by default: the
result, as the parameter `name` of a join block. -/
def branchJoin (c : ValId) (thenK elseK : EM ValId) (ty : TypeExpr Py.env := Base.Bool)
    (name : Name := nm "b") : EM ValId := do
  let t ← liftPy (freshLabel [] "then")
  let e ← liftPy (freshLabel [] "else")
  let j ← liftPy (freshLabel [ty] "join")
  liftPy (branch c t.goto e.goto)
  let a ← inBlock t thenK
  liftPy (jump (j.goto.bind (Val.ofId ty a)))
  let b ← inBlock e elseK
  liftPy (jump (j.goto.bind (Val.ofId ty b)))
  Val.id <$> liftPy (startBlockWith j name)

/-- Run `body` in a new region whose failures propagate: the region's propagating block
returns them as `base.error`, so that the operation that owns the region raises them. `ok`
wraps the body's result of type `a`. -/
def raisingRegion (params : Array (ValDecl Py.env)) (a : TypeExpr Py.env)
    (body : EM ValId) : EM (Region Py.env Info) := do
  let _ : MonadLiftT (BuildM Py.env Info) EM := ⟨fun x => liftPy (α := Info) (monadLift x)⟩
  Prod.fst <$> Build.regionWith params (base := "body") do
    let propagate ← liftPy (freshLabel [Py.Value] "propagate")
    let v ← withHandler propagate body
    liftPy (α := Info) do
      let ok ← Build.emitApply (env := Py.env) (α := Info) (nm "res") (Py.raising a)
        Base.Except.ok.ref #[v]
      Build.Raw.ret (env := Py.env) (α := Info) ok
      let exc ← startBlockWith propagate (nm "exc")
      let e ← Build.emitApply (env := Py.env) (α := Info) (nm "err") (Py.raising a)
        Base.Except.error.ref #[exc.id]
      Build.Raw.ret (env := Py.env) (α := Info) e

/-- A raising operation that gives a base `Bool`: its `err` successor is the enclosing
handler. -/
def emitFailingBool {isig : InsnSig Py.env} (name : String) (r : InsnRef Py.env isig)
    (args : Array ValId)
    (typeArgs : TypeArgsOf r (some Base.Bool) := by infer_type_args) : EM ValId :=
  do
    let h ← liftPy (α := Info) checkedHandler
    liftPy (α := Info) (Build.emitApply (env := Py.env) (nm name) Base.Bool r args #[h]
      (typeArgs := typeArgs) : BuildM Py.env Info ValId)

/-- Whether `e` is a value, a `py.Value`, rather than a condition. -/
def CExpr.isValue : CExpr → Bool
  | .reSearch .. | .enum .. | .notEnum .. | .isInstance .. | .typeTest .. | .subclassOf ..
  | .strIsOneOf ..
  | .intIsOneOf .. | .kwargsWithin _ | .isDefined _ | .bindsTo .. | .and .. | .or .. | .not _
  | .implies .. | .quant .. | .const _ => false
  | _ => true

/-- The class `c`, read when the clause runs: `py.stdClass`, or a model class from its module's
global cell, a nested one through its outer classes (§12.3, *Class identity*). -/
def classValue (c : ClassRef) : EM ValId := do
  match c with
  | .std m n => liftPy (emitTotal (nm "cls") Py.stdClass.ref #[← strC m, ← strC n])
  | .model mc =>
    let outer := mc.path[0]!
    let v ← liftPy (requireGlobal mc.module outer)
    mc.path.toList.drop 1 |>.foldlM (init := v) fun acc seg => liftPy (getAttr acc seg)

/-- One class, or a tuple of them. -/
def classesValue (cs : Array ClassRef) : EM ValId := do
  let vs ← cs.mapM classValue
  if h : vs.size = 1 then return vs[0] else liftPy (emitTotal (nm "tuple") Py.mkTuple.ref vs)

/-- A binary operator of `Py.env`, named as `CExpr.arith` and `CExpr.cmp` name it. -/
def binary (op : String) (a b : ValId) : EM ValId := liftPy do
  let n := nm op
  match op with
  | "add" => emitFailing n Py.add.ref #[a, b]
  | "sub" => emitFailing n Py.sub.ref #[a, b]
  | "mult" => emitFailing n Py.mult.ref #[a, b]
  | "floorDiv" => emitFailing n Py.floorDiv.ref #[a, b]
  | "mod" => emitFailing n Py.mod.ref #[a, b]
  | "pow" => emitFailing n Py.pow.ref #[a, b]
  | "eq" => emitFailing n Py.eq.ref #[a, b]
  | "notEq" => emitFailing n Py.notEq.ref #[a, b]
  | "lt" => emitFailing n Py.lt.ref #[a, b]
  | "ltE" => emitFailing n Py.ltE.ref #[a, b]
  | "gt" => emitFailing n Py.gt.ref #[a, b]
  | "gtE" => emitFailing n Py.gtE.ref #[a, b]
  | "in_" => emitFailing n Py.in_.ref #[a, b]
  | _ => emitFailing n Py.notIn.ref #[a, b]

/-- The value that the parameter `p` has: `py.argOf`, with `py.undef` or `None` as its
default. -/
def argOf (p : ParamRef) : EM ValId := do
  let ctx ← read
  let d ← if p.noneDefault then liftPy noneLit
    else liftPy (emitTotal (nm "undef") Py.undef.ref #[← strC p.name])
  let pos ← liftPy (emitConst (nm "pos") (.int p.pos))
  liftPy (emitTotal (nm p.name) Py.argOf.ref #[ctx.args, ctx.kwargs, pos, ← strC p.name, d])

/-- `body`'s value, read in the state at the call: inside a `base.old` region in a post-state
clause, as §12.2 reads a parameter. -/
def atCall (body : EM ValId) : EM ValId := do
  let ctx ← read
  if !ctx.post || ctx.inOld then body
  else
    let _ : MonadLiftT (BuildM Py.env Info) EM := ⟨fun x => liftPy (α := Info) (monadLift x)⟩
    let h ← liftPy (α := Info) checkedHandler
    let r ← raisingRegion #[] Py.Value (withReader ({ · with inOld := true }) body)
    Build.emitApplyWith (nm "old") Py.Value Base.old.ref #[] #[h] #[pure r]
      (typeArgs := ta[Py.Value, Py.Value])

/-- `v == l₁ or v == l₂ or …`, in order. -/
def eqChain (v : ValId) : List String → EM ValId
  | [] => boolC false
  | l :: rest => do
    let lv ← liftPy (strLit l)
    let b ← liftPy (truthy (← binary "eq" v lv))
    branchJoin b (boolC true) (eqChain v rest)

/-- Record that `what` is read where nothing binds it, which `checkExpr` rules out; the
function then fails to build. The value returned stands in for it. -/
def unbound (what : String) : EM ValId := do
  liftPy (liftM (m := BuildM Py.env Info)
    (Build.error s!"internal: {what} is read where nothing binds it") : PyM Info Unit)
  return (← read).args

mutual

/-- The value of `e`, a `py.Value`. A condition is turned into a Python bool. -/
def value (e : CExpr) : EM ValId := do
  if h : e.isValue = false then
    -- A condition in a value's position: a Python bool.
    let b ← cond e (← read).strong
    return ← liftPy (emitTotal (nm "bool") Py.boolLit.ref #[b])
  let ctx ← read
  match e with
  | .param p => atCall (argOf p)
  | .extraKwargs names =>
    atCall do
      let ns ← names.mapM strC
      liftPy (emitTotal (nm "kw") Py.extraKwargs.ref (#[ctx.kwargs] ++ ns))
  | .ghost m n =>
    match ctx.ghostParams.find? (·.1 == (m, n)) with
    | some (_, v) => return v
    | none =>
      let cell ← liftPy (liftM (m := BuildM Py.env Info)
        (Build.emitGhost (ghostName m n) Py.Value) : PyM Info ValId)
      liftPy (readCell cell (nm n))
  -- `checkExpr` gives a binder only inside its quantifier, and `result` only in a post-state
  -- clause, where the emitter has bound them. Otherwise the function fails to build, and the
  -- model is rejected.
  | .binder n =>
    match ctx.binders.find? (·.1 == n) with
    | some (_, v) => return v
    | none => unbound s!"the binder '{n}'"
  | .result =>
    match ctx.result with
    | some v => return v
    | none => unbound "result"
  | .int i => liftPy (intLit i)
  | .float f => liftPy (floatLit f)
  | .bool b => liftPy (boolLit b)
  | .none => liftPy noneLit
  | .str s => liftPy (strLit s)
  | .attr a f => do liftPy (getAttr (← value a) f)
  | .item a k => do
    let av ← value a
    let kv ← value k
    liftPy (emitFailing (nm "item") Py.getItem.ref #[av, kv])
  | .len a => do liftPy (emitFailing (nm "len") Py.len.ref #[← value a])
  | .arith op a b => do binary op (← value a) (← value b)
  | .neg a => do liftPy (emitFailing (nm "neg") Py.uSub.ref #[← value a])
  | .cmp op a b => do binary op (← value a) (← value b)
  | .isNone a positive => do
    let v ← value a
    let n ← liftPy noneLit
    if positive then liftPy (emitTotal (nm "is") Py.is_.ref #[v, n])
    else liftPy (emitTotal (nm "isNot") Py.isNot.ref #[v, n])
  | .contains k c => do
    let kv ← liftPy (strLit k)
    let cv ← value c
    liftPy (emitFailing (nm "in") Py.in_.ref #[kv, cv])
  | .old a => oldPart a
  -- The conditions, handled above.
  | _ => liftPy noneLit
termination_by (sizeOf e, if e.isValue then 1 else 3)
decreasing_by all_goals first
  | (apply Prod.Lex.left; first | decreasing_trivial | (simp; omega) | (simp; done))
  | (apply Prod.Lex.right; first | (simp_all; done) | (split <;> decide))

/-- The `base.old` part `e`: its value at the call, if that value is an immutable scalar;
otherwise `base.old` fails, so the clause assumes nothing (§12.4, *`OLD(e)`*). -/
def oldPart (e : CExpr) : EM ValId := do
  let _ : MonadLiftT (BuildM Py.env Info) EM := ⟨fun x => liftPy (α := Info) (monadLift x)⟩
  let h ← liftPy (α := Info) checkedHandler
  let r ← (do
    Prod.fst <$> Build.regionWith #[] (base := "old") do
      let propagate ← liftPy (freshLabel [Py.Value] "propagate")
      let v ← withHandler propagate (withReader ({ · with inOld := true }) (value e))
      liftPy (α := Info) do
        let scalar ← emitTest (nm "scalar") Py.isImmutableScalar.ref #[v]
        let s ← freshLabel [] "scalar"
        let mutable ← freshLabel [] "mutable"
        branch scalar s.goto mutable.goto
        startBlock s
        let ok ← Build.emitApply (env := Py.env) (α := Info) (nm "res") (Py.raising Py.Value)
          Base.Except.ok.ref #[v]
        Build.Raw.ret (env := Py.env) (α := Info) ok
        startBlock mutable
        let err ← Build.emitApply (env := Py.env) (α := Info) (nm "res")
          (Py.raising Py.Value) Base.Except.error.ref #[v]
        Build.Raw.ret (env := Py.env) (α := Info) err
        let exc ← startBlockWith propagate (nm "exc")
        let e ← Build.emitApply (env := Py.env) (α := Info) (nm "err")
          (Py.raising Py.Value) Base.Except.error.ref #[exc.id]
        Build.Raw.ret (env := Py.env) (α := Info) e : EM (Region Py.env Info))
  Build.emitApplyWith (nm "old") Py.Value Base.old.ref #[] #[h] #[pure r]
      (typeArgs := ta[Py.Value, Py.Value])
termination_by (sizeOf e, 4)
decreasing_by all_goals first
  | (apply Prod.Lex.left; first | decreasing_trivial | (simp; omega) | (simp; done))
  | (apply Prod.Lex.right; first | (simp_all; done) | (split <;> decide))

/-- The condition `e`, a base `Bool`. `strong` says whether this position may be stronger
than the source: a `requires` clause's positive positions and a `free ensures` clause's
negative ones. A negation flips it. -/
def cond (e : CExpr) (strong : Bool) : EM ValId := do
  if h : e.isValue = true then
    return ← liftPy (truthy (← withReader ({ · with strong }) (value e)))
  let ctx ← read
  match e with
  | .const b => boolC b
  | .reSearch p a => do
    let pv ← strC p
    emitFailingBool "match" Py.reSearch.ref #[pv, ← value a]
  | .enum a vals =>
    let v ← value a
    if ctx.requires && strong then
      liftPy (emitTest (nm "oneOf") Py.strIsOneOf.ref (#[v] ++ (← vals.mapM strC)))
    else
      eqChain v vals.toList
  | .notEnum a lit =>
    let v ← value a
    let l ← liftPy (strLit lit)
    let eqV ← binary "eq" v l
    let neV ← binary "notEq" v l
    let eqB ← liftPy (truthy eqV)
    let neB ← liftPy (truthy neV)
    -- `not (v == lit)` and `v != lit`: both where the position may be stronger, either one
    -- where it may be weaker.
    if strong then branchJoin eqB (boolC false) (pure neB)
    else branchJoin eqB (pure neB) (boolC true)
  | .isInstance a c => do
    let v ← value a
    let cls ← classValue c
    emitFailingBool "inst" Py.isInstance.ref #[v, cls]
  | .typeTest a cs => do
    let v ← value a
    let cls ← classesValue cs
    let sub ← emitFailingBool "sub" Py.typeIsSubclass.ref #[v, cls]
    branchJoin sub (emitFailingBool "inst" Py.isInstance.ref #[v, cls]) (boolC false)
  | .subclassOf a c => do
    let v ← value a
    emitFailingBool "sub" Py.typeIsSubclass.ref #[v, ← classValue c]
  | .strIsOneOf a lits => do
    let v ← value a
    liftPy (emitTest (nm "oneOf") Py.strIsOneOf.ref (#[v] ++ (← lits.mapM strC)))
  | .intIsOneOf a lits => do
    let v ← value a
    let ls ← lits.mapM fun i => liftPy (emitConst (nm "i") (.int i))
    liftPy (emitTest (nm "oneOf") Py.intIsOneOf.ref (#[v] ++ ls))
  | .kwargsWithin keys => do
    liftPy (emitTest (nm "within") Py.dictKeysWithin.ref (#[ctx.kwargs] ++ (← keys.mapM strC)))
  | .isDefined a => do liftPy (emitTest (nm "defined") Py.isDefined.ref #[← value a])
  | .bindsTo nPos varKw names => do
    let n ← liftPy (emitConst (nm "nPos") (.int nPos))
    let k ← boolC varKw
    liftPy (emitTest (nm "binds") Py.bindsTo.ref (#[ctx.args, ctx.kwargs, n, k] ++ (← names.mapM strC)))
  | .and a b => do branchJoin (← cond a strong) (cond b strong) (boolC false)
  | .or a b => do branchJoin (← cond a strong) (boolC true) (cond b strong)
  | .not a => do branchJoin (← cond a (!strong)) (boolC false) (boolC true)
  | .implies a b => do branchJoin (← cond a (!strong)) (cond b strong) (boolC true)
  | .quant q c body => do
    let _ : MonadLiftT (BuildM Py.env Info) EM := ⟨fun x => liftPy (α := Info) (monadLift x)⟩
    let cv ← value c
    let h ← liftPy (α := Info) checkedHandler
    match q with
    | .members all x =>
      let item ← freshPyVal (nm x)
      let r ← raisingRegion #[item] Base.Bool
        (withReader (fun ctx => { ctx with binders := (x, item.id) :: ctx.binders })
          (cond body strong))
      if all then Build.emitApplyWith (nm "all") Base.Bool Py.allIn.ref #[cv] #[h] #[pure r]
      else Build.emitApplyWith (nm "any") Base.Bool Py.anyIn.ref #[cv] #[h] #[pure r]
    | .entries all k v =>
      let kd ← freshPyVal (nm (k.getD "key"))
      let vd ← freshPyVal (nm (v.getD "value"))
      let bs := (match k with | some n => [(n, kd.id)] | none => []) ++
        (match v with | some n => [(n, vd.id)] | none => [])
      let r ← raisingRegion #[kd, vd] Base.Bool
        (withReader (fun ctx => { ctx with binders := bs ++ ctx.binders }) (cond body strong))
      if all then Build.emitApplyWith (nm "all") Base.Bool Py.allItems.ref #[cv] #[h] #[pure r]
      else Build.emitApplyWith (nm "any") Base.Bool Py.anyItems.ref #[cv] #[h] #[pure r]
  -- The values, handled above.
  | _ => boolC false
termination_by (sizeOf e, if e.isValue then 2 else 0)
decreasing_by all_goals first
  | (apply Prod.Lex.left; first | decreasing_trivial | (simp; omega) | (simp; done))
  | (apply Prod.Lex.right; first | (simp_all; done) | (split <;> decide))


end

end -- public section

end StrataPython.Dyn.PySpec
