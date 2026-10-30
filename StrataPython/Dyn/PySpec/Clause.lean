/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Resolve

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

/-- Whether `e` mentions `result`. -/
@[expose] def CExpr.mentionsResult : CExpr → Bool
  | .result => true
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

/-- Whether `e` reads, outside its `OLD`s, nothing but constants, so that the whole of `e` can be
read in the state at the call. A parameter or a quantifier's binder outside `OLD` is an object
after the call: `len(xs)` reads its contents then. So `len(OLD(xs))` can move into `base.old`,
and `OLD(xs) == xs` can't. -/
@[expose] def CExpr.readsOnlyOld : CExpr → Bool
  | .int _ | .float _ | .bool _ | .none | .str _ | .const _ | .old _ => true
  | .param _ | .binder _ | .extraKwargs _ | .result | .ghost .. | .bindsTo .. | .kwargsWithin _ =>
    false
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e => e.readsOnlyOld
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.readsOnlyOld && b.readsOnlyOld

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

/-- Whether `e` holds an `old` part. -/
@[expose] def CExpr.hasOld : CExpr → Bool
  | .old _ => true
  | .attr e _ | .len e | .neg e | .isNone e _ | .contains _ e | .reSearch _ e | .enum e _
  | .notEnum e _ | .isInstance e _ | .typeTest e _ | .subclassOf e _ | .strIsOneOf e _
  | .intIsOneOf e _ | .isDefined e | .not e => e.hasOld
  | .item a b | .arith _ a b | .cmp _ a b | .and a b | .or a b | .implies a b
  | .quant _ a b => a.hasOld || b.hasOld
  | _ => false

/-- `e` with every `old` marker removed: the expression inside a `base.old` region. -/
@[expose] def CExpr.unOld : CExpr → CExpr
  | .old e => e.unOld
  | .attr e f => .attr e.unOld f
  | .item a b => .item a.unOld b.unOld
  | .len e => .len e.unOld
  | .arith op a b => .arith op a.unOld b.unOld
  | .neg e => .neg e.unOld
  | .cmp op a b => .cmp op a.unOld b.unOld
  | .isNone e p => .isNone e.unOld p
  | .contains k e => .contains k e.unOld
  | .reSearch p e => .reSearch p e.unOld
  | .enum e vs => .enum e.unOld vs
  | .notEnum e v => .notEnum e.unOld v
  | .isInstance e c => .isInstance e.unOld c
  | .typeTest e cs => .typeTest e.unOld cs
  | .subclassOf e c => .subclassOf e.unOld c
  | .strIsOneOf e l => .strIsOneOf e.unOld l
  | .intIsOneOf e l => .intIsOneOf e.unOld l
  | .isDefined e => .isDefined e.unOld
  | .and a b => .and a.unOld b.unOld
  | .or a b => .or a.unOld b.unOld
  | .not e => .not e.unOld
  | .implies a b => .implies a.unOld b.unOld
  | .quant q c b => .quant q c.unOld b.unOld
  | e => e

/-- The old parts of a post-state clause: each largest subexpression that holds an `OLD` and
reads only state at the call, outside its `OLD`s, becomes one `old` part (§12.4, *`OLD(e)`*).
`len(OLD(xs)) == len(xs) + 1` gives `old(len(xs)) == len(xs) + 1`, and `allocated ==
OLD(allocated) + 1` gives `allocated == old(allocated + 1)`. -/
@[expose] def CExpr.splitOld (e : CExpr) : CExpr :=
  if e.hasOld && e.readsOnlyOld then .old e.unOld
  else match e with
  | .attr a f => .attr a.splitOld f
  | .item a b => .item a.splitOld b.splitOld
  | .len a => .len a.splitOld
  | .arith op a b => .arith op a.splitOld b.splitOld
  | .neg a => .neg a.splitOld
  | .cmp op a b => .cmp op a.splitOld b.splitOld
  | .isNone a p => .isNone a.splitOld p
  | .contains k a => .contains k a.splitOld
  | .reSearch p a => .reSearch p a.splitOld
  | .enum a vs => .enum a.splitOld vs
  | .notEnum a v => .notEnum a.splitOld v
  | .isInstance a c => .isInstance a.splitOld c
  | .typeTest a cs => .typeTest a.splitOld cs
  | .subclassOf a c => .subclassOf a.splitOld c
  | .strIsOneOf a l => .strIsOneOf a.splitOld l
  | .intIsOneOf a l => .intIsOneOf a.splitOld l
  | .isDefined a => .isDefined a.splitOld
  | .and a b => .and a.splitOld b.splitOld
  | .or a b => .or a.splitOld b.splitOld
  | .not a => .not a.splitOld
  | .implies a b => .implies a.splitOld b.splitOld
  | .quant q c b => .quant q c.splitOld b.splitOld
  | .old a => .old a.unOld
  | e => e

/-- Whether no `OLD` part of `e` mentions `result`. The checker rejects `OLD(result)`, so
every checked clause has this property. -/
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
