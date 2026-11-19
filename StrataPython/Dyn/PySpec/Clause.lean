/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Resolve
public import StrataPython.Dyn.OldSplit

set_option autoImplicit false

/-!
# Checked clauses

The translation reads a PySpec clause in two steps. The checker (`Check.lean`) turns a
`SpecExpr` into a `CExpr`, in which every decision of `docs/PythonToDyn.md` §12.4 is made:
what each name is, whether `s.f` is an attribute or an item, which class a type names, and
which part of a post-state clause `base.old` covers. A model that §12 can't represent is
rejected there. The emitter (`Emit.lean`) then writes each `CExpr` as blocks of a clause
region, and can't fail.
-/

namespace StrataPython.Dyn.PySpec

open StrataPython.Specs

public section

/-- A class that a clause tests against. -/
inductive ClassRef where
  /-- The class `name` of the standard module `module`, read with `py.stdClass`. -/
  | std (module name : String)
  /-- A class of a model module, read from its module's global cell when the clause runs; a
  nested class through its outer classes. -/
  | model (c : ModelClass)
deriving Inhabited

/-- How a parameter's value is read: `py.argOf` with its position and name, and its default:
`None` or none. -/
structure ParamRef where
  name : String
  /-- Its position, or `-1` for a keyword-only parameter. -/
  pos : Int
  noneDefault : Bool
deriving Inhabited, BEq

/-- A quantifier: `allIn` or `anyIn` over a collection's members, or `allItems` or `anyItems`
over a dict's entries. -/
inductive Quant where
  | members (all : Bool) (binder : String)
  /-- A dict's entries, binding the key, the value, or both; a missing name is `none`. -/
  | entries (all : Bool) (key value : Option String)
deriving Inhabited

/-- A checked clause expression. A *value* is a `py.Value`; a *condition* is a base `Bool`.
The emitter tests a value with `py.truthy` where a condition is needed. -/
inductive CExpr where
  /-- A parameter, read with `py.argOf`. -/
  | param (p : ParamRef)
  /-- The `**kw` parameter's dict: `py.extraKwargs` of `%kwargs` less the named parameters. -/
  | extraKwargs (names : Array String)
  /-- The contents of the module ghost `name` of the module `module`. -/
  | ghost (module name : String)
  /-- A quantifier's binder. -/
  | binder (name : String)
  /-- The `ok` value of a post-state clause's result. -/
  | result
  /-- The exception of a raising-exit clause's `error` result, bound as `exc`. -/
  | raised
  | int (i : Int)
  | float (f : Float)
  | bool (b : Bool)
  | none
  | str (s : String)
  /-- `e.f`, with `py.attr`. -/
  | attr (e : CExpr) (f : String)
  /-- `e[k]`, with `py.getItem`. -/
  | item (e k : CExpr)
  /-- `len(e)`, with `py.len`. -/
  | len (e : CExpr)
  /-- An arithmetic operator of `Py.env` (`add`, `sub`, `mult`, `floorDiv`, `mod`, `pow`). -/
  | arith (op : String) (a b : CExpr)
  | neg (e : CExpr)
  /-- A comparison of `Py.env` (`eq`, `notEq`, `lt`, `ltE`, `gt`, `gtE`, `in_`, `notIn`): a
  value. -/
  | cmp (op : String) (a b : CExpr)
  /-- `e is None`, or `e is not None` when `positive` is false: a value. -/
  | isNone (e : CExpr) (positive : Bool)
  /-- `"k" in c`, with `py.in`: a value. -/
  | contains (key : String) (c : CExpr)
  /-- `re.search(pattern, e) is not None`: a condition. -/
  | reSearch (pattern : String) (e : CExpr)
  /-- `e == v₁ or …`: a condition. `py.strIsOneOf` where §12.4's position rule allows it,
  else a chain of `py.eq`. -/
  | enum (e : CExpr) (vals : Array String)
  /-- PySpec's reading of `e != v`, which stands for both `not (e == v)` and `e != v`: a
  condition (§3.3 of the design). -/
  | notEnum (e : CExpr) (v : String)
  /-- `isinstance(e, C)`, with `py.isInstance`: a condition. -/
  | isInstance (e : CExpr) (cls : ClassRef)
  /-- A declared-type test of §12.3, `py.typeIsSubclass` and then `py.isInstance`, on a tuple
  of classes when there are several: a condition. -/
  | typeTest (e : CExpr) (classes : Array ClassRef)
  /-- `py.typeIsSubclass(e, C)` alone: the receiver's test (§12.3): a condition. -/
  | subclassOf (e : CExpr) (cls : ClassRef)
  /-- `py.strIsOneOf(e, lits)` or `py.intIsOneOf(e, lits)`: a condition. -/
  | strIsOneOf (e : CExpr) (lits : Array String)
  | intIsOneOf (e : CExpr) (lits : Array Int)
  /-- `py.dictKeysWithin(%kwargs, keys)`: a condition. -/
  | kwargsWithin (keys : Array String)
  /-- `py.isDefined(e)`: a condition. -/
  | isDefined (e : CExpr)
  /-- `py.bindsTo(%args, %kwargs, nPos, varKw, names)`: a condition. -/
  | bindsTo (nPos : Nat) (varKw : Bool) (names : Array String)
  | and (a b : CExpr)
  | or (a b : CExpr)
  | not (e : CExpr)
  | implies (a b : CExpr)
  /-- A quantifier over `coll`, whose body is a condition. -/
  | quant (q : Quant) (coll : CExpr) (body : CExpr)
  /-- `base.old` of a value, which holds only if the value is an immutable scalar. The part
  holds no `result`. -/
  | old (e : CExpr)
  /-- `false` or `true`. -/
  | const (b : Bool)
deriving Inhabited

/-- Whether `e` mentions the call's outcome: `result`, or the raised exception `exc`. Neither
exists in the state at the call. -/
@[expose] def CExpr.mentionsResult : CExpr → Bool
  | .result | .raised => true
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e | .old e => e.mentionsResult
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.mentionsResult || b.mentionsResult
  | _ => false

/-- The names of the ghosts that `e` reads. -/
def CExpr.ghostsRead : CExpr → List String
  | .ghost _ n => [n]
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e | .old e => e.ghostsRead
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.ghostsRead ++ b.ghostsRead
  | _ => []

/-- The children that the old-part rule looks into: the operands of every constructor but
`old`. -/
@[expose] def CExpr.oldChildren : CExpr → List CExpr
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e => [e]
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => [a, b]
  | _ => []

/-- `e` with each of its `oldChildren` replaced by `f`'s result. -/
@[expose] def CExpr.mapOldChildren : (e : CExpr) → ((c : CExpr) → c ∈ e.oldChildren → CExpr) → CExpr
  | .attr e f', g => .attr (g e (by simp [CExpr.oldChildren])) f'
  | .len e, g => .len (g e (by simp [CExpr.oldChildren]))
  | .neg e, g => .neg (g e (by simp [CExpr.oldChildren]))
  | .isNone e p, g => .isNone (g e (by simp [CExpr.oldChildren])) p
  | .contains k e, g => .contains k (g e (by simp [CExpr.oldChildren]))
  | .reSearch p e, g => .reSearch p (g e (by simp [CExpr.oldChildren]))
  | .enum e vs, g => .enum (g e (by simp [CExpr.oldChildren])) vs
  | .notEnum e v, g => .notEnum (g e (by simp [CExpr.oldChildren])) v
  | .isInstance e c, g => .isInstance (g e (by simp [CExpr.oldChildren])) c
  | .typeTest e cs, g => .typeTest (g e (by simp [CExpr.oldChildren])) cs
  | .subclassOf e c, g => .subclassOf (g e (by simp [CExpr.oldChildren])) c
  | .strIsOneOf e l, g => .strIsOneOf (g e (by simp [CExpr.oldChildren])) l
  | .intIsOneOf e l, g => .intIsOneOf (g e (by simp [CExpr.oldChildren])) l
  | .isDefined e, g => .isDefined (g e (by simp [CExpr.oldChildren]))
  | .not e, g => .not (g e (by simp [CExpr.oldChildren]))
  | .item a b, g => .item (g a (by simp [CExpr.oldChildren])) (g b (by simp [CExpr.oldChildren]))
  | .arith op a b, g =>
    .arith op (g a (by simp [CExpr.oldChildren])) (g b (by simp [CExpr.oldChildren]))
  | .cmp op a b, g => .cmp op (g a (by simp [CExpr.oldChildren])) (g b (by simp [CExpr.oldChildren]))
  | .and a b, g => .and (g a (by simp [CExpr.oldChildren])) (g b (by simp [CExpr.oldChildren]))
  | .or a b, g => .or (g a (by simp [CExpr.oldChildren])) (g b (by simp [CExpr.oldChildren]))
  | .implies a b, g =>
    .implies (g a (by simp [CExpr.oldChildren])) (g b (by simp [CExpr.oldChildren]))
  | .quant q a b, g =>
    .quant q (g a (by simp [CExpr.oldChildren])) (g b (by simp [CExpr.oldChildren]))
  | e, _ => e

/-- A clause's syntax for the old-part rule (§12.4, *`OLD(e)`*). A parameter, a quantifier's
binder, `**kw`, `result`, `exc`, a ghost, `py.bindsTo` and `py.dictKeysWithin` read state after
the call: a parameter or a binder outside `OLD` is an object after the call, and `len(xs)` reads
its contents then. `result` and `exc` don't exist before the call. So `len(OLD(xs))` can move into
`base.old`, and `OLD(xs) == xs` can't. -/
instance : OldSyntax CExpr where
  oldArg? | .old e => some e | _ => none
  mkOld := .old
  wrappable _ := true
  readsState
    | .param _ | .binder _ | .extraKwargs _ | .result | .raised | .ghost .. | .bindsTo .. |
      .kwargsWithin _ => true
    | _ => false
  children := CExpr.oldChildren
  children_lt e c h := by
    cases e <;> simp only [CExpr.oldChildren, List.mem_cons, List.mem_nil_iff, or_false] at h <;>
      (try rcases h with h | h) <;> (try exact absurd h id) <;> subst_vars <;>
      simp only [CExpr.attr.sizeOf_spec, CExpr.item.sizeOf_spec, CExpr.len.sizeOf_spec,
        CExpr.arith.sizeOf_spec, CExpr.neg.sizeOf_spec, CExpr.cmp.sizeOf_spec,
        CExpr.isNone.sizeOf_spec, CExpr.contains.sizeOf_spec, CExpr.reSearch.sizeOf_spec,
        CExpr.enum.sizeOf_spec, CExpr.notEnum.sizeOf_spec, CExpr.isInstance.sizeOf_spec,
        CExpr.typeTest.sizeOf_spec, CExpr.subclassOf.sizeOf_spec, CExpr.strIsOneOf.sizeOf_spec,
        CExpr.intIsOneOf.sizeOf_spec, CExpr.isDefined.sizeOf_spec, CExpr.and.sizeOf_spec,
        CExpr.or.sizeOf_spec, CExpr.not.sizeOf_spec, CExpr.implies.sizeOf_spec,
        CExpr.quant.sizeOf_spec, Bool.sizeOf_eq_one, Nat.lt_add_left_iff_pos, Nat.lt_add_one] <;>
      omega
  oldArg_lt e a h := by
    cases e <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [CExpr.old.sizeOf_spec]
    omega
  mapChildren := CExpr.mapOldChildren
  children_mapChildren e f := by cases e <;> simp [CExpr.mapOldChildren, CExpr.oldChildren]

/-- Whether `e` reads, outside its `OLD`s, nothing but constants, so that the whole of `e` can be
read in the state at the call (`OldSplit.readsOnlyOld`). -/
@[expose] def CExpr.readsOnlyOld (e : CExpr) : Bool := OldSplit.readsOnlyOld e

/-- Whether `e` holds an `old` part. -/
@[expose] def CExpr.hasOld (e : CExpr) : Bool := OldSplit.hasOld e

/-- `e` with every `old` marker removed: the expression inside a `base.old` region. -/
@[expose] def CExpr.unOld (e : CExpr) : CExpr := OldSplit.unOld e

/-- The old parts of a post-state clause: each largest subexpression that holds an `OLD` and
reads only state at the call, outside its `OLD`s, becomes one `old` part (§12.4, *`OLD(e)`*).
`len(OLD(xs)) == len(xs) + 1` gives `old(len(xs)) == len(xs) + 1`, and `allocated ==
OLD(allocated) + 1` gives `allocated == old(allocated + 1)`. -/
@[expose] def CExpr.splitOld (e : CExpr) : CExpr := OldSplit.splitOld e

/-- Whether `e` contains `false`: the constant, or the literal `False`, which lowers to it. -/
@[expose] def CExpr.hasFalse : CExpr → Bool
  | .const b | .bool b => !b
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e | .old e => e.hasFalse
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.hasFalse || b.hasFalse
  | _ => false

/-- Whether `e` reads the call's arguments, a ghost or the state at the call: a parameter, the
`**kw` dict, the binding or keyword test of the arguments, a ghost, or an `OLD`. -/
@[expose] def CExpr.readsCallState : CExpr → Bool
  | .param _ | .extraKwargs _ | .ghost .. | .old _ | .bindsTo .. | .kwargsWithin _ => true
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e => e.readsCallState
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.readsCallState || b.readsCallState
  | _ => false

/-- Whether `e` uses an `and`, an `or`, an implication, a regex search, `x == "A" or x == "B"`
or `x != "A"` where a value is needed, as in `(x or 3) == result` or
`compile(p).search(s) == False`: CPython gives an operand, a match object or the result of
`__ne__` there, while the IR's form is a condition. `asValue` says whether `e` itself stands
where a value is needed. `inValue` says whether a `not`, an `and`, an `or`, an implication or a
quantifier around `e` gives that value, as in `(not (x != "A")) == result`: there the bool is
exact only if `x == "A" or x == "B"` and `x != "A"` have one reading, which they don't. -/
@[expose] def CExpr.condAsValue (e : CExpr) (asValue : Bool := false) (inValue : Bool := false) :
    Bool :=
  match e with
  | .and a b | .or a b | .implies a b =>
    asValue || a.condAsValue false inValue || b.condAsValue false inValue
  | .not a => a.condAsValue false (asValue || inValue)
  | .old a => a.condAsValue asValue inValue
  | .quant _ c b => c.condAsValue true || b.condAsValue false (asValue || inValue)
  | .enum a _ | .notEnum a _ => asValue || inValue || a.condAsValue true
  | .reSearch _ a => asValue || a.condAsValue true
  | .attr a _ | .len a | .neg a | .isNone a _ | .contains _ a | .isInstance a _ | .typeTest a _ | .subclassOf a _ | .strIsOneOf a _
  | .intIsOneOf a _ | .isDefined a => a.condAsValue true
  | .item a b | .arith _ a b | .cmp _ a b => a.condAsValue true || b.condAsValue true
  | _ => false

/-- Whether no `OLD` part of `e` mentions `result` or the raised exception. The checker rejects
`OLD(result)` and `OLD(exc)`, so every checked clause has this property. -/
@[expose] def CExpr.oldsWithoutResult : CExpr → Bool
  | .old e => !e.mentionsResult
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e => e.oldsWithoutResult
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.oldsWithoutResult && b.oldsWithoutResult
  | _ => true

/-- The old parts of `e`: the contents of each `old`, outermost first. -/
@[expose] def CExpr.oldContents : CExpr → List CExpr
  | .old e => [e]
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e => e.oldContents
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.oldContents ++ b.oldContents
  | _ => []

/-- A location set of a frame (§12.5). -/
inductive FrameLoc where
  /-- `py.instanceState`. -/
  | instanceState
  /-- `py.reachLoc` of the call's arguments tuple, `%args.0`. -/
  | args
  /-- `py.reachLoc` of the call's keyword arguments dict, `%kwargs.0`. -/
  | kwargs
  /-- `py.objLoc` of a value. -/
  | obj (e : CExpr)
  /-- `py.attrLoc` of a value's attribute. -/
  | attr (e : CExpr) (f : String)
  /-- `py.itemLoc` of a dict's entry. -/
  | item (e : CExpr) (key : String)
  /-- `base.cellLoc` of a ghost's cell. -/
  | ghostCell (module name : String)
  /-- `py.reachLoc` of a value: every location of it and of what it reaches. -/
  | reach (e : CExpr)
  /-- `inner` where the condition `test` holds, and `py.instanceState` elsewhere. The test must
  be exact at every call that meets the `requires` clauses, as `v == lit` is after an overload
  set's dispatch clause: a test that fails more often makes the frame smaller. -/
  | guarded (test : CExpr) (inner : FrameLoc)
deriving Inhabited

end -- public section

end StrataPython.Dyn.PySpec
