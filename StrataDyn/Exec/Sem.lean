/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Name
public import StrataDyn.Util.NameMap

set_option autoImplicit false

/-!
# Semantic rules: the interface

What a rule is written against, and what the engine consumes.  A rule is written at Lean types
only.  The engine tags each value with a code, a `Ty`; a rule takes the tags it needs as
instances, which the wrapper builds.

* **Tags.**  A `Ty` names a Lean type of a table: a head applied to tags.  Heads `0` and `1`
  are the engine's, a ref and a code pointer, and every other head is a Lean type
  constructor of the table, one per constructor, so Dyn types that share a Lean type share
  their tag.  `Ty.decode` gives a tag's Lean type.
* **The run token.**  `Store σ` is what a token `σ` says of locations and functions, `Ref σ α`
  a ref to a cell holding an `α`, and `FnRef σ as r` a closure taking `as` and returning `r`.
  Each is a raw ref or closure, `Ref.Raw σ` or `FnRef.Raw σ`, which holds a proof that the
  token gives, so no term generic in `σ` is one (`no_forge`, `no_forge_fn`).  The machine runs
  at the token `Run`, which promises nothing, and checks every access and every call.
* **Tags of Lean types.**  `Decode σ` holds the table's decoding at `σ`.  `TagOf σ α` is a tag
  of `α`, `SigOf σ as r` a signature's, and `TagCon σ F` and `TagCon₂ σ F` give tags of
  `F A` from those of `A`.  A rule takes one wherever it makes, reads or writes a cell or calls
  a closure; the wrapper builds each at the concrete types, with a proof by `rfl`.
* **Rules**: `Sem ε E α`, a free monad, with `Target E ts` exits, the operation's own entry
  `Again E S` with the rule's state `S`, `Region ε ts α` handles, `HasPart` parts of the
  world, `HasHeap σ ε`, the machine's cells, and `HasCall σ ε`, calls of closures and their
  partial application.  `jump`, `semanticGap`, `semanticFailure`, `assume`, `chooseNat`,
  `choose`, `chooseInt`, `runRegion`, `newRef`, `readRef`, `writeRef`, `modifyRef`, `callFn`
  and `bindFn` build its terms.
* **The engine boundary**: `Args`, `Exit`, `Out`, `Fn`, the machine's requests
  `MReq` and `MEff`, and the handles the wrappers build, `Region.slot`, `HasHeap.mreq` and
  `HasCall.mreq`.
* **The table**: `Shape`, `Impl`, `OpImpl`, `Table`, `Model`, and `RunModel`, a model at the
  token, which linking and the machine see.  `Table.stateOf` gives each operation's state
  type, by its position and its type arguments' tags, so that the machine's states
  name a rule's state type with no type among their data.

## Requests

A rule's tree has two kinds of inner node, kept apart so that each reading of a rule treats
them separately:

* **world requests**, `choose` and `update`, which the machine answers in place: a number from
  its oracle, or an update of the world `ε.W`, which takes the world and gives back the new
  world with the rule's continuation;
* **machine requests**, `vis`, which runs a body, a region of the operation or a closure's
  function, and resumes the rule with its result, or asks for a new cell, a read, a write or
  an update of a cell, or a new closure, which the machine answers in place.

A rule's leaves return a value or stop: with a fault, or with a jump along one of its targets
or to its `Again`, which runs the operation again, on the same operands, regions and targets, with
the state the jump passes, as a loop's back edge whose state is the rule's own.

A rule is generic in `ε` and `E`, and takes its handles, its targets and its `Again` as
arguments.  The world `ε.W` is abstract in a rule, so the rule reads the world through the
`HasPart` instances it takes, and through them only the parts they name.  `update` is a
constructor of `Sem` like any other, so a rule can also put back a world it read earlier, in
whole.  A rule that takes refs or closures is generic in the token `σ` too.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-! ## Tags -/

/-- A tag: head `head` applied to `args`, or a list of tags, the argument of a code pointer's
parameters.  Head `0` is a ref's and head `1` a code pointer's; a table numbers its Lean type
constructors from `2`. -/
inductive Ty where
  | app (head : Nat) (args : List Ty)
  | list (elems : List Ty)
  deriving Repr, Inhabited

mutual
/-- Decide `s = t`. -/
def Ty.decEq : (s t : Ty) → Decidable (s = t)
  | .app h as, .app k bs =>
    if hh : h = k then
      match Ty.decEqList as bs with
      | isTrue ha => isTrue (by rw [hh, ha])
      | isFalse ha => isFalse (fun he => by injection he with _ hargs; exact ha hargs)
    else isFalse (fun he => by injection he with hhead; exact hh hhead)
  | .list as, .list bs =>
    match Ty.decEqList as bs with
    | isTrue ha => isTrue (by rw [ha])
    | isFalse ha => isFalse (fun he => by injection he with hargs; exact ha hargs)
  | .app .., .list _ => isFalse (fun he => nomatch he)
  | .list _, .app .. => isFalse (fun he => nomatch he)

/-- Decide `as = bs`. -/
def Ty.decEqList : (as bs : List Ty) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun he => nomatch he)
  | _ :: _, [] => isFalse (fun he => nomatch he)
  | a :: as, b :: bs =>
    match Ty.decEq a b with
    | isTrue hab => match Ty.decEqList as bs with
      | isTrue hs => isTrue (by rw [hab, hs])
      | isFalse hs => isFalse (fun he => by injection he with _ htail; exact hs htail)
    | isFalse hab => isFalse (fun he => by injection he with hhead; exact hab hhead)
end

instance : DecidableEq Ty := Ty.decEq

/-- The elements of a list of tags, and none of any other tag: the tags a list-kinded type
argument stands for. -/
def Ty.elems : Ty → List Ty
  | .list ts => ts
  | .app .. => []

/-- `n`, dotted, for a message. -/
def nameStr : Name → String
  | .base => "_"
  | .str .base s => s
  | .num .base i => toString i
  | .str p s => s!"{nameStr p}.{s}"
  | .num p i => s!"{nameStr p}.{i}"

/-- A value with its tag. -/
abbrev Dyn (I : Ty → Type) : Type := Sigma I

/-! ## The run token

A run token `σ` stands for one run's heap and module, as the `s` of Haskell's `ST s` does.  A
raw ref holds a location and the token's proof that it is a cell, and a raw closure a function
and the token's proof that it is the module's.  A ref and a closure are raw ones with their Lean
types as a phantom.  A rule is generic in the token, and `no_forge` and `no_forge_fn` state that
no term generic in it is a raw ref or a raw closure.

The proofs name no Lean type, so a datatype may hold a ref or a closure of itself.  Lean's types
let a rule give a raw ref another contents' type, but a table rejects such a rule (`Ref.mk`); the
machine's tag check at every access still catches a ref that no rule made, such as one from a
hand-made snapshot.  A loop that skips the check cannot cast through a ref's proof, so its certificate has
to type the heap instead: every location holds a value of the type it was made at. -/

/-- What the token `σ` says: which locations are cells, and which functions are the module's.
Neither names a Lean type, so a datatype may hold a ref or a closure of itself. -/
class Store (σ : Type) : Type where
  Valid : Nat → Prop
  FnValid : Nat → Prop

/-- A raw ref to a cell of the heap `σ` names: a location with `σ`'s proof that it is one.  At
run time it is its location. -/
structure Ref.Raw (σ : Type) [Store σ] : Type where
  loc : Nat
  valid : Store.Valid σ loc

/-- A ref to a cell holding an `α`: a raw ref, with the contents' Lean type as a phantom.  What
`base.Ref a` is at `σ`.  The machine checks the cell's tag against `α`'s at every access. -/
structure Ref (σ : Type) [Store σ] (α : Type) : Type where
  raw : Ref.Raw σ

/-- A raw closure of the module `σ` names: function `idx`, with the values a partial application
captured, in the machine's captures cell at `captured`, or none if `captured` is `0`. -/
structure FnRef.Raw (σ : Type) [Store σ] : Type where
  idx : Nat
  captured : Nat
  valid : Store.FnValid σ idx

/-- A closure taking `as` and returning `r`: a raw closure, with its signature's Lean types as a
phantom.  A static code pointer is a closure with no captures.  What `base.Fn as r` is at `σ`.
The machine checks the function's signature at every call and bind. -/
structure FnRef (σ : Type) [Store σ] (as : List Type) (r : Type) : Type where
  raw : FnRef.Raw σ

section
variable {σ : Type} [Store σ]

/-- The location a ref names. -/
abbrev Ref.loc {α : Type} (c : Ref σ α) : Nat := c.raw.loc

/-- The function a closure names. -/
abbrev FnRef.idx {as : List Type} {r : Type} (f : FnRef σ as r) : Nat := f.raw.idx

/-- A closure's captures cell, or `0` for none. -/
abbrev FnRef.captured {as : List Type} {r : Type} (f : FnRef σ as r) : Nat :=
  f.raw.captured

instance {α : Type} : DecidableEq (Ref σ α) := fun ⟨⟨l₁, _⟩⟩ ⟨⟨l₂, _⟩⟩ =>
  if h : l₁ = l₂ then isTrue (by subst h; rfl) else isFalse fun he => h (congrArg Ref.loc he)

instance {α : Type} : Repr (Ref σ α) := ⟨fun c _ => .text s!"ref#{c.loc}"⟩

instance {as : List Type} {r : Type} : DecidableEq (FnRef σ as r) :=
  fun ⟨⟨i₁, c₁, _⟩⟩ ⟨⟨i₂, c₂, _⟩⟩ =>
  if h : i₁ = i₂ ∧ c₁ = c₂ then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
  else isFalse fun he => h ⟨congrArg FnRef.idx he, congrArg FnRef.captured he⟩

instance {as : List Type} {r : Type} : Repr (FnRef σ as r) :=
  ⟨fun f _ => .text s!"fn#{f.idx}@{f.captured}"⟩

end

/-- No term generic in the token is a raw ref: at a token whose cells are `False`, a raw ref
holds a proof of `False`.  So no such term is a `Ref` at any type. -/
theorem no_forge (f : (σ : Type) → [Store σ] → Ref.Raw σ) : False :=
  letI : Store Empty := ⟨fun _ => False, fun _ => False⟩
  (f Empty).valid

/-- No term generic in the token is a raw closure, so none is an `FnRef` at any signature. -/
theorem no_forge_fn (f : (σ : Type) → [Store σ] → FnRef.Raw σ) : False :=
  letI : Store Empty := ⟨fun _ => False, fun _ => False⟩
  (f Empty).valid

/-- The machine's token. -/
structure Run : Type where
  deriving DecidableEq, Repr

/-- `Run` promises nothing of a location or a function, so every access of a cell and every
call of a closure is checked. -/
instance instStoreRun : Store Run := ⟨fun _ => True, fun _ => True⟩

/-! ## Decoding tags -/

mutual
/-- The Lean type of tag `t` at the token `σ`, where Lean type constructor `h` applied to
`as` is `H h as`.  Heads `0` and `1` are a ref's and a code pointer's; a list of tags is no
value's type, and stands for `Unit`.  Reducible, so that a tag of a closed Lean type decodes to
it by `rfl`. -/
@[reducible] def Ty.decode (σ : Type) [Store σ] (H : Nat → List Type → Type) : Ty → Type
  | .app 0 [a] => Ref σ (Ty.decode σ H a)
  | .app 1 [.list as, r] => FnRef σ (Ty.decodeList σ H as) (Ty.decode σ H r)
  | .app h args => H h (Ty.decodeList σ H args)
  | .list _ => Unit

/-- `Ty.decode` of each tag. -/
@[reducible] def Ty.decodeList (σ : Type) [Store σ] (H : Nat → List Type → Type) :
    List Ty → List Type
  | [] => []
  | t :: ts => Ty.decode σ H t :: Ty.decodeList σ H ts
end

/-- `Ty.decodeList` decodes each tag of the list. -/
theorem Ty.decodeList_eq_map (σ : Type) [Store σ] (H : Nat → List Type → Type) :
    ∀ ts : List Ty, Ty.decodeList σ H ts = ts.map (Ty.decode σ H)
  | [] => rfl
  | t :: ts => congrArg (Ty.decode σ H t :: ·) (Ty.decodeList_eq_map σ H ts)

/-- A code pointer's tag decodes to a closure of its parameters' and result's Lean types. -/
theorem Ty.decode_fn (σ : Type) [Store σ] (H : Nat → List Type → Type) (ts : List Ty) (r : Ty) :
    Ty.decode σ H (.app 1 [.list ts, r]) = FnRef σ (ts.map (Ty.decode σ H)) (Ty.decode σ H r) :=
  congrArg (FnRef σ · _) (Ty.decodeList_eq_map σ H ts)

/-- A table's decoding of tags at the token `σ`.  A rule takes it, so that it may state the
tags its capabilities carry; the wrapper supplies its table's. -/
class Decode (σ : Type) [Store σ] : Type 1 where
  decode : Ty → Type

section
variable (σ : Type) [Store σ] [Decode σ]

/-- A tag of the Lean type `α`, at the token `σ`: what the machine checks a cell's contents
against.  The proof is erased: at run time a `TagOf` is its tag. -/
class TagOf (α : Type) where
  tag : Ty
  ok : Decode.decode σ tag = α

/-- The tags of a signature taking `as` and returning `r`: what the machine checks a closure's
function against. -/
class SigOf (as : List Type) (r : Type) where
  sig : List Ty × Ty
  ok : sig.1.map (Decode.decode σ) = as ∧ Decode.decode σ sig.2 = r

/-- Tags of `F A` from tags of `A`: a type constructor a rule makes cells or calls through
generically. -/
class TagCon (F : Type → Type) where
  tagOf : {A : Type} → TagOf σ A → TagOf σ (F A)

/-- Tags of `F A B` from tags of `A` and `B`. -/
class TagCon₂ (F : Type → Type → Type) where
  tagOf : {A B : Type} → TagOf σ A → TagOf σ B → TagOf σ (F A B)

/-- Tags of the Lean types `as`, one each: what a rule over a list-kinded type variable takes
to reach cells and calls at the list's types. -/
class TagsOf (as : List Type) where
  tags : List Ty
  ok : tags.map (Decode.decode σ) = as

end

section
variable {σ : Type} [Store σ] [Decode σ]

instance {F : Type → Type} {A : Type} [c : TagCon σ F] [a : TagOf σ A] : TagOf σ (F A) :=
  c.tagOf a

instance {F : Type → Type → Type} {A B : Type} [c : TagCon₂ σ F] [a : TagOf σ A]
    [b : TagOf σ B] : TagOf σ (F A B) :=
  c.tagOf a b

instance SigOf.nil {r : Type} [t : TagOf σ r] : SigOf σ [] r := ⟨([], t.tag), ⟨rfl, t.ok⟩⟩

instance SigOf.cons {a r : Type} {as : List Type} [t : TagOf σ a] [s : SigOf σ as r] :
    SigOf σ (a :: as) r :=
  ⟨(t.tag :: s.sig.1, s.sig.2), ⟨by rw [List.map_cons, t.ok, s.ok.1], s.ok.2⟩⟩

/-- The signature that takes `cs` and then `as`, from the tags of `cs` and the signature that
takes `as`. -/
instance SigOf.append {cs as : List Type} {r : Type} [c : TagsOf σ cs] [s : SigOf σ as r] :
    SigOf σ (cs ++ as) r :=
  ⟨(c.tags ++ s.sig.1, s.sig.2), ⟨by rw [List.map_append, c.ok, s.ok.1], s.ok.2⟩⟩

instance TagsOf.nil : TagsOf σ [] := ⟨[], rfl⟩

instance TagsOf.cons {a : Type} {as : List Type} [t : TagOf σ a] [ts : TagsOf σ as] :
    TagsOf σ (a :: as) :=
  ⟨t.tag :: ts.tags, by rw [List.map_cons, t.ok, ts.ok]⟩

/-- The tag of the first of `a :: as`. -/
@[instance_reducible] def TagsOf.head {a : Type} {as : List Type} : TagsOf σ (a :: as) → TagOf σ a
  | ⟨t :: _, h⟩ => ⟨t, (List.cons.inj h).1⟩
  | ⟨[], h⟩ => nomatch h

/-- The tags of the rest of `a :: as`. -/
@[instance_reducible] def TagsOf.tail {a : Type} {as : List Type} : TagsOf σ (a :: as) → TagsOf σ as
  | ⟨_ :: ts, h⟩ => ⟨ts, (List.cons.inj h).2⟩
  | ⟨[], h⟩ => nomatch h

end

/-! ## Faults -/

/-- Why a run stopped without a result. -/
inductive Fault where
  /-- A case the semantics deliberately does not cover (`semanticGap`). -/
  | gap (msg : String)
  /-- A case the rule's author holds impossible (`semanticFailure`). -/
  | failure (msg : String)
  /-- The path is infeasible (`assume`): a run reports it, and it stands for no behaviour, not
  for an error. -/
  | blocked (msg : String)
  /-- A call or a partial application of a closure whose function, with what it captured,
  does not take the arguments or return the result the call's tags say. -/
  | badCall (f : Name)
  /-- An access found no value of the ref's tag at its location: a location past the heap's
  end, or one holding another tag.  A ref is checked at every access. -/
  | badCell (loc : Nat)
  /-- The fuel ran out.  The machine returns the state; `run` reports this. -/
  | outOfFuel
  /-- Operations the module uses that the table has no rule for, reported before the first
  step. -/
  | missingRules (ops : Array Name)
  /-- The module fails validation, or the arguments do not fit the entry function, reported
  before the first step. -/
  | invalid (msg : String)
  | noFunction (name : Name)
  deriving Repr, Inhabited, DecidableEq

/-! ## Rules: a free monad -/

/-- A payload of values of the Lean types `ts`: `Unit`, the one value, or a tuple.  It is an
`abbrev` by `List.rec` rather than by structural recursion: `vcgen` (v4.35) fails on a spec
binder whose type is a structurally recursive `abbrev`, and a `def` would hide the tuple from
numerals and instances. -/
abbrev Payload (ts : List Type) : Type :=
  List.rec (motive := fun _ => Type) Unit (fun t rest T => match rest with
    | [] => t
    | _ :: _ => t × T) ts

/-- The target of a successor of the operation a rule implements, whose payload has the Lean
types `ts`: the rule jumps along it with the payload.  A rule takes one per successor, after its
operands and regions, and is generic in `E`: its values of `E` come from its targets and its
`Again`. -/
structure Target (E : Type) (ts : List Type) where
  /-- The exit along this successor with a payload. -/
  exit : Payload ts → E

/-- The operation's own entry, with the rule's state, of a Lean type `S` the rule chooses.
Jumping to it runs the operation again, on the same operands, regions and targets, with the
state `some s`, as a loop's back edge.  A rule that loops takes `(st : Option S)` and then one,
after its targets: its first run has `st = none`.  It is no `Target`: it fills no successor. -/
structure Again (E : Type) (S : Type) where
  /-- The exit back into the operation, with a new state. -/
  exit : S → E

/-- A handle `H` a rule jumps along, with a payload of the Lean type `P`: a `Target` or its
`Again`. -/
class Jump (H : Type) (E : outParam Type) (P : outParam Type) where
  exit : H → P → E

instance {E : Type} {ts : List Type} : Jump (Target E ts) E (Payload ts) := ⟨Target.exit⟩

instance {E S : Type} : Jump (Again E S) E S := ⟨Again.exit⟩

/-- Why a rule stopped without a result. -/
inductive Stop (E : Type) where
  /-- An exit along one of its targets, or to its `Again`. -/
  | jump (e : E)
  | fault (f : Fault)

/-- What a rule may ask for: machine requests `I`, with `O i` the answer to `i`, and the world
`W` it may read and update. -/
structure Eff where
  I : Type
  O : I → Type
  W : Type

/-- A rule's computation, with requests `ε` and exits `E`, returning an `α`: a finite tree
whose leaves return or stop, and whose inner nodes are requests. -/
inductive Sem (ε : Eff) (E α : Type) where
  | ret (a : α)
  | stop (s : Stop E)
  /-- Choose a number, and continue with it. -/
  | choose (k : Nat → Sem ε E α)
  /-- Run a body, or ask the machine for a cell or a closure, and continue with the answer. -/
  | vis (i : ε.I) (k : ε.O i → Sem ε E α)
  /-- Update the world: `f` takes the world and gives the new world and the continuation, so
  that one request reads and writes it. -/
  | update (f : ε.W → ε.W × Sem ε E α)

section
variable {ε : Eff} {E α β γ : Type}

mutual
/-- `x`, then `f` on its result. -/
def Sem.bind : Sem ε E α → (α → Sem ε E β) → Sem ε E β
  | .ret a, f => f a
  | .stop s, _ => .stop s
  | .choose k, f => .choose fun c => (k c).bind f
  | .vis i k, f => .vis i fun o => (k o).bind f
  | .update u, f => .update fun w => Sem.bindAfter (u w) f

/-- An update's new world and continuation, the continuation followed by `f`. -/
def Sem.bindAfter : ε.W × Sem ε E α → (α → Sem ε E β) → ε.W × Sem ε E β
  | (w, k), f => (w, k.bind f)
end

instance : Monad (Sem ε E) where
  pure := .ret
  bind := Sem.bind

/-- `pure` returns its value at once. -/
@[simp] theorem Sem.pure_eq (a : α) : (pure a : Sem ε E α) = .ret a := rfl

/-- Binding `pure a` runs the continuation on `a`. -/
@[simp] theorem Sem.pure_bind (a : α) (f : α → Sem ε E β) : (pure a >>= f) = f a := rfl

/-- Binding a returned value runs the continuation on it. -/
@[simp] theorem Sem.ret_bind (a : α) (f : α → Sem ε E β) :
    ((Sem.ret a : Sem ε E α) >>= f) = f a := rfl

/-- Binding a stopped computation stops it the same way. -/
@[simp] theorem Sem.stop_bind (s : Stop E) (f : α → Sem ε E β) :
    ((Sem.stop s : Sem ε E α) >>= f) = .stop s := rfl

/-- Binding a computation to `ret` leaves it unchanged. -/
theorem Sem.bind_pure (x : Sem ε E α) : x.bind (fun a => .ret a) = x :=
  Sem.rec (motive_1 := fun x => x.bind (fun a => .ret a) = x)
    (motive_2 := fun p => Sem.bindAfter p (fun a => .ret a) = p)
    (fun _ => rfl) (fun _ => rfl)
    (fun _ ih => congrArg Sem.choose (funext ih))
    (fun i _ ih => congrArg (Sem.vis i) (funext ih))
    (fun _ ih => congrArg Sem.update (funext ih))
    (fun w _ ih => congrArg (w, ·) ih) x

/-- Binding is associative: binding `f` and then `g` is binding, once, `f` followed by `g`. -/
theorem Sem.bind_assoc (x : Sem ε E α) (f : α → Sem ε E β) (g : β → Sem ε E γ) :
    (x.bind f).bind g = x.bind fun a => (f a).bind g :=
  Sem.rec (motive_1 := fun x => (x.bind f).bind g = x.bind fun a => (f a).bind g)
    (motive_2 := fun p => Sem.bindAfter (Sem.bindAfter p f) g =
      Sem.bindAfter p fun a => (f a).bind g)
    (fun _ => rfl) (fun _ => rfl)
    (fun _ ih => congrArg Sem.choose (funext ih))
    (fun i _ ih => congrArg (Sem.vis i) (funext ih))
    (fun _ ih => congrArg Sem.update (funext ih))
    (fun w _ ih => congrArg (w, ·) ih) x

/-- `Sem` satisfies the monad laws. -/
instance : LawfulMonad (Sem ε E) :=
  LawfulMonad.mk' (Sem ε E) (id_map := Sem.bind_pure) (pure_bind := fun _ _ => rfl)
    (bind_assoc := Sem.bind_assoc)

/-- Take successor `l` with payload `args`, or, if `l` is its `Again`, run the operation again
with the state `args`. -/
@[inline] def jump {H P : Type} [Jump H E P] (l : H) (args : P) : Sem ε E α :=
  .stop (.jump (Jump.exit l args))

/-- Stop with `Fault.gap`: the semantics deliberately does not cover this case. -/
@[inline] def semanticGap (msg : String) : Sem ε E α := .stop (.fault (.gap msg))

/-- Stop with `Fault.failure`: a case the rule's author holds impossible. -/
@[inline] def semanticFailure (msg : String) : Sem ε E α := .stop (.fault (.failure msg))

/-- Stop with `Fault.blocked` unless `b` holds: the path is infeasible. -/
@[inline] def assume (b : Bool) (msg : String) : Sem ε E Unit :=
  if b then .ret () else .stop (.fault (.blocked msg))

/-- A number chosen by the semantics: by an oracle when running, and any number in a relational
reading. -/
@[inline] def chooseNat : Sem ε E Nat := .choose .ret

/-- The oracle's answer `k`, reduced below `n + 1`. -/
def pickBelow (k n : Nat) : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- A number below `n + 1`, chosen by the semantics: `chooseNat`, reduced. -/
@[inline] def choose (n : Nat) : Sem ε E (Fin (n + 1)) := .choose fun k => .ret (pickBelow k n)

/-- The integer that the natural number `k` numbers: `0, -1, 1, -2, 2, …`, a bijection. -/
def intOfNat (k : Nat) : Int := if k % 2 = 0 then ↑(k / 2) else -↑((k + 1) / 2)

/-- An integer chosen by the semantics: `chooseNat`, numbered by `intOfNat`. -/
@[inline] def chooseInt : Sem ε E Int := .choose fun k => .ret (intOfNat k)

/-- A jump ends the computation, so nothing bound after it runs. -/
@[simp] theorem jump_bind {H P : Type} [Jump H E P] (l : H) (args : P)
    (f : α → Sem ε E β) : ((jump l args : Sem ε E α) >>= f) = jump l args := rfl

/-- A semantic gap ends the computation, so nothing bound after it runs. -/
@[simp] theorem semanticGap_bind (msg : String) (f : α → Sem ε E β) :
    ((semanticGap msg : Sem ε E α) >>= f) = semanticGap msg := rfl

/-- A semantic failure ends the computation, so nothing bound after it runs. -/
@[simp] theorem semanticFailure_bind (msg : String) (f : α → Sem ε E β) :
    ((semanticFailure msg : Sem ε E α) >>= f) = semanticFailure msg := rfl

end

/-! ## The world, in parts

An environment's world is a Lean type of its own, which the machine threads through a run.  A
rule names the parts it touches by `HasPart W P`, a getter and a setter of part `P`, and reads
and writes them with `getThe P`, `modifyThe P` and `modifyGetThe P`.  `HasPart` states no laws.
An environment that extends another builds a world with its parent's parts as fields, so its
parent's rules run on it unchanged. -/

/-- The world `W` has a part `P`. -/
class HasPart (W : Type) (P : Type) where
  get : W → P
  set : W → P → W

set_option synthInstance.checkSynthOrder false in
/-- A part is state: `getThe P`, `modifyThe P`.  A rule names the part, so the instance is
chosen by `P`. -/
instance Sem.instMonadStateOf {ε : Eff} {E P : Type} [HasPart ε.W P] :
    MonadStateOf P (Sem ε E) where
  get := .update fun w => (w, .ret (HasPart.get w))
  set p := .update fun w => (HasPart.set w p, .ret ())
  modifyGet f := .update fun w =>
    let (a, p) := f (HasPart.get w)
    (HasPart.set w p, .ret a)

/-! ## Handles -/

/-- A region of the operation, with parameters of the Lean types `ts`, yielding an `α`: the
request that runs it on its arguments, and how its answer is the value. -/
structure Region (ε : Eff) (ts : List Type) (α : Type) where
  req : Payload ts → ε.I
  ans : (a : Payload ts) → ε.O (req a) → α

/-- Run region `r` on `args`. -/
@[inline] def runRegion {ε : Eff} {E : Type} {ts : List Type} {α : Type} (r : Region ε ts α)
    (args : Payload ts) : Sem ε E α :=
  .vis (r.req args) fun o => .ret (r.ans args o)

/-- **A rule may make, read and write the machine's cells**: it asks the machine for a new cell
holding a value of a Lean type, or for a read or a write through a ref, each by a tag of the
contents' type.  The wrapper builds the handle, and the machine checks every read and
write. -/
class HasHeap (σ : Type) [Store σ] [Decode σ] (ε : outParam Eff) : Type 1 where
  newReq : {α : Type} → TagOf σ α → α → ε.I
  newAns : {α : Type} → (t : TagOf σ α) → (v : α) → ε.O (newReq t v) → Ref σ α
  getReq : {α : Type} → TagOf σ α → Ref σ α → ε.I
  getAns : {α : Type} → (t : TagOf σ α) → (c : Ref σ α) → ε.O (getReq t c) → α
  setReq : {α : Type} → TagOf σ α → Ref σ α → α → ε.I
  modifyReq : {α : Type} → TagOf σ α → Ref σ α → (α → α) → ε.I

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasHeap σ ε] {α : Type}
  [t : TagOf σ α]

/-- A new cell holding `v`. -/
@[inline] def newRef (v : α) : Sem ε E (Ref σ α) :=
  .vis (HasHeap.newReq t v) fun o => .ret (HasHeap.newAns t v o)

/-- The contents of the cell `c` names. -/
@[inline] def readRef (c : Ref σ α) : Sem ε E α :=
  .vis (HasHeap.getReq t c) fun o => .ret (HasHeap.getAns t c o)

/-- Replace the contents of the cell `c` names with `v`. -/
@[inline] def writeRef (c : Ref σ α) (v : α) : Sem ε E Unit :=
  .vis (HasHeap.setReq t c v) fun _ => .ret ()

/-- Replace the contents `x` of the cell `c` names with `f x`, in one request: the machine takes
the contents out of the cell before it applies `f`, so the cell does not share them. -/
@[inline] def modifyRef (c : Ref σ α) (f : α → α) : Sem ε E Unit :=
  .vis (HasHeap.modifyReq t c f) fun _ => .ret ()

end

/-- **A rule may call closures and bind their arguments**: it asks the machine to run a
closure's function on what it captured and the call's arguments, or for a new closure that has
captured one more argument.  The machine checks the function's signature against the tags of
what it captured and the signature's tags. -/
class HasCall (σ : Type) [Store σ] [Decode σ] (ε : outParam Eff) : Type 1 where
  callReq : {as : List Type} → {r : Type} → SigOf σ as r → FnRef σ as r → Payload as → ε.I
  callAns : {as : List Type} → {r : Type} → (s : SigOf σ as r) → (f : FnRef σ as r) →
    (a : Payload as) → ε.O (callReq s f a) → r
  bindReq : {a : Type} → {as : List Type} → {r : Type} → TagOf σ a → SigOf σ as r →
    FnRef σ (a :: as) r → a → ε.I
  bindAns : {a : Type} → {as : List Type} → {r : Type} → (t : TagOf σ a) → (s : SigOf σ as r) →
    (f : FnRef σ (a :: as) r) → (x : a) → ε.O (bindReq t s f x) → FnRef σ as r

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasCall σ ε]

/-- Call the closure `f` on `args`. -/
@[inline] def callFn {as : List Type} {r : Type} [s : SigOf σ as r] (f : FnRef σ as r)
    (args : Payload as) : Sem ε E r :=
  .vis (HasCall.callReq s f args) fun o => .ret (HasCall.callAns s f args o)

/-- The closure `f` with its first argument bound to `x`: a new closure, whose captures cell
holds `f`'s captures and `x`.  The machine checks that `f`'s function takes them. -/
@[inline] def bindFn {a r : Type} {as : List Type} [t : TagOf σ a] [SigOf σ (a :: as) r]
    [s : SigOf σ as r] (f : FnRef σ (a :: as) r) (x : a) : Sem ε E (FnRef σ as r) :=
  .vis (HasCall.bindReq t s f x) fun o => .ret (HasCall.bindAns t s f x o)

/-- The closure `f` with its first arguments bound to `xs`, of the types `cs`: one `bindFn`
each, first to last. -/
def bindAll {as : List Type} {r : Type} [s : SigOf σ as r] :
    (cs : List Type) → [TagsOf σ cs] → FnRef σ (cs ++ as) r → Payload cs →
      Sem ε E (FnRef σ as r)
  | [], _, f, () => .ret f
  | [a], t, f, x =>
    @bindFn σ _ _ ε E _ a r as t.head (@SigOf.cons σ _ _ a r as t.head s) s f x
  | a :: b :: cs, t, f, (x, xs) =>
    letI : TagsOf σ (b :: cs) := t.tail
    let s₁ : SigOf σ ((b :: cs) ++ as) r := SigOf.append
    .bind (@bindFn σ _ _ ε E _ a r ((b :: cs) ++ as) t.head (@SigOf.cons σ _ _ a r _ t.head s₁) s₁
      f x) fun g => bindAll (b :: cs) g xs

end

/-! ## The engine boundary -/

section
variable (I : Ty → Type)

/-- One value per tag in `ts`, each at its own type. -/
inductive Args : List Ty → Type where
  | nil : Args []
  | cons {t : Ty} {ts : List Ty} (x : I t) (xs : Args ts) : Args (t :: ts)

/-- One of the successors whose payloads have the tags `ps`, by position, with its payload. -/
inductive Exit : List (List Ty) → Type where
  | here {ts : List Ty} {ps : List (List Ty)} (payload : Args I ts) : Exit (ts :: ps)
  | there {ts : List Ty} {ps : List (List Ty)} (e : Exit ps) : Exit (ts :: ps)

/-- Where a rule's tree exits, for an operation with successors whose payloads have the tags
`ps` and a rule whose state is an `S`: along a successor, or back into the operation with the
state `s`. -/
inductive Out (ps : List (List Ty)) (S : Type) where
  | exit (e : Exit I ps)
  | again (s : S)

/-- A curried function of one operand per tag in `ts`, each at its own type, to `R`. -/
abbrev Fn (R : Type) : List Ty → Type
  | [] => R
  | t :: ts => I t → Fn R ts

variable {I} in
/-- The curried function of one operand per tag in `ts` that applies `k` to their payload. -/
def Fn.ofPayload {R : Type} : (ts : List Ty) → (Payload (ts.map I) → R) → Fn I R ts
  | [], k => k ()
  | [_], k => fun x => k x
  | _ :: t :: ts, k => fun x => Fn.ofPayload (t :: ts) fun p => k (x, p)

/-- What an operation with result tag `ret` returns: a value of that tag, or nothing if it is
terminal. -/
abbrev Res : Option Ty → Type
  | some r => I r
  | none => Empty

/-- A request of a rule whose operation has regions with the signatures `rs`:
a body to run, region `slot` on `args` or the function of the closure `(idx, captured)` on
`args`, expecting a value of tag `sig.2`; or a request the machine answers in place: a new cell
of tag `t` holding `v`, the contents of a cell, a write, an update of a cell's contents by `f`,
or a new closure that binds `v` as the
next argument of the closure `(idx, captured)`, at the signature `sig` of what is left.  One
inductive, so that a request is one object. -/
inductive MReq (rs : List (List Ty × Ty)) where
  | region (slot : Fin rs.length) (args : Args I (rs.get slot).1)
  | call (sig : List Ty × Ty) (idx captured : Nat) (args : Payload (sig.1.map I))
  | new (t : Ty) (v : I t)
  | get (t : Ty) (loc : Nat)
  | set (t : Ty) (loc : Nat) (v : I t)
  | modify (t : Ty) (loc : Nat) (f : I t → I t)
  | bind (t : Ty) (v : I t) (sig : List Ty × Ty) (idx captured : Nat)

variable (σ : Type) [Store σ]

variable {I} in
/-- A request's answer, at the token `σ`. -/
@[reducible] def MReq.Out {rs : List (List Ty × Ty)} : MReq I rs → Type
  | .region slot _ => I (rs.get slot).2
  | .call sig .. => I sig.2
  | .new t _ => Ref σ (I t)
  | .get t _ => I t
  | .set .. | .modify .. => Unit
  | .bind _ _ sig .. => FnRef σ (sig.1.map I) (I sig.2)

variable {I} in
/-- Whether a request writes a cell: `set` and `modify`.  It reads only the request's constructor,
never a location, so the check trusts it.  It names every constructor, so that a new one must be
given its value. -/
@[reducible] def MReq.writesCell {rs : List (List Ty × Ty)} : MReq I rs → Bool
  | .set .. | .modify .. => true
  | .region .. | .call .. | .new .. | .get .. | .bind .. => false

/-- The machine's requests for an operation with regions `rs`, at the token `σ`, over the world
`W`. -/
@[reducible] def MEff (W : Type) (rs : List (List Ty × Ty)) : Eff where
  I := MReq I rs
  O q := q.Out σ
  W := W

/-- A rule's tree at the engine boundary: the machine's requests for regions `rs` at the token
`σ`, exits along the successors whose payloads have the tags `ps` or back into the operation
with a state `S`, and a result of type `R`. -/
abbrev Tree (W : Type) (rs : List (List Ty × Ty)) (ps : List (List Ty)) (S R : Type) : Type :=
  Sem (MEff I σ W rs) (Out I ps S) R

end

section
variable {σ : Type} [Store σ] {I : Ty → Type} {W : Type} {rs : List (List Ty × Ty)}

/-- Region `slot` of an operation, as a rule's handle. -/
@[inline] def Region.slot (slot : Fin rs.length) {ts : List Type}
    (args : Payload ts → Args I (rs.get slot).1) :
    Region (MEff I σ W rs) ts (I (rs.get slot).2) :=
  ⟨fun a => .region slot (args a), fun _ x => x⟩

/-- The machine's cells, as a rule's handle, at the decoding `I`.  The tag rides in the
request; the casts are the tags' proofs, and cost nothing at run time. -/
@[reducible] def HasHeap.mreq : @HasHeap σ _ ⟨I⟩ (MEff I σ W rs) :=
  @HasHeap.mk σ _ ⟨I⟩ (MEff I σ W rs)
    (fun t v => .new t.tag (cast t.ok.symm v))
    (fun t _ c => cast (congrArg (Ref σ) t.ok) c)
    (fun t c => .get t.tag c.loc)
    (fun t _ v => cast t.ok v)
    (fun t c v => .set t.tag c.loc (cast t.ok.symm v))
    (fun t c f => .modify t.tag c.loc fun v => cast t.ok.symm (f (cast t.ok v)))

/-- The machine's calls, as a rule's handle, at the decoding `I`. -/
@[reducible] def HasCall.mreq : @HasCall σ _ ⟨I⟩ (MEff I σ W rs) :=
  @HasCall.mk σ _ ⟨I⟩ (MEff I σ W rs)
    (fun s f a => .call s.sig f.idx f.captured (cast (congrArg Payload s.ok.1.symm) a))
    (fun s _ _ x => cast s.ok.2 x)
    (fun t s f x => .bind t.tag (cast t.ok.symm x) s.sig f.idx f.captured)
    (fun _ s _ _ g => cast (congr (congrArg (FnRef σ) s.ok.1) s.ok.2) g)

end

section
variable {I : Ty → Type}

/-- The payload of Lean values, as the machine's arguments. -/
def Args.ofPayload : (ts : List Ty) → Payload (ts.map I) → Args I ts
  | [], _ => .nil
  | [_], x => .cons x .nil
  | _ :: t :: ts, (x, xs) => .cons x (Args.ofPayload (t :: ts) xs)

end

/-! ## The table -/

/-- An operation at fixed type arguments, by tags: its operands, its variadic's element, its
result (`none` if it is terminal), its successors' payloads and its regions' entry parameters
and results. -/
structure Shape where
  args : List Ty
  variadic : Option Ty := none
  ret : Option Ty
  succs : List (List Ty) := []
  regions : List (List Ty × Ty) := []
  deriving Repr, DecidableEq

/-- What a wrapper takes after its operands, to `X`: the variadic's array, if it has one. -/
abbrev VarFn (I : Ty → Type) (variadic : Option Ty) (X : Type) : Type :=
  match variadic with
  | none => X
  | some v => Array (I v) → X

/-- A wrapper's outcome type `X`, after the variadic operands as an array if `s` has a
variadic. -/
abbrev Shape.Var (I : Ty → Type) (s : Shape) (X : Type) : Type := VarFn I s.variadic X

/-- What a pure wrapper of shape `s` returns: its result, or the exit a case instruction
takes. -/
abbrev Shape.Pure (I : Ty → Type) (s : Shape) : Type :=
  match s.ret with
  | some r => I r
  | none => Exit I s.succs

/-- The tree of a rule of shape `s` at the token `σ`, with a state `S`. -/
abbrev Shape.Tree (σ : Type) [Store σ] (I : Ty → Type) (W : Type) (s : Shape) (S : Type) : Type :=
  Exec.Tree I σ W s.regions s.succs S (Res I s.ret)

/-- The wrapper of an operation of shape `s` at the token `σ`, whose rule's state is an `S`: a
pure function of its operands, for a rule outside `Sem`, a constructor or a case instruction;
a rule's tree; or, for a rule that loops, its tree on its first run and its tree on a run
again with a state. -/
inductive Impl (σ : Type) [Store σ] (I : Ty → Type) (W : Type) (s : Shape) (S : Type) where
  | pure (f : Fn I (s.Var I (s.Pure I)) s.args)
  | sem (f : Fn I (s.Var I (s.Tree σ I W S)) s.args)
  | loop (f : Fn I (s.Var I (s.Tree σ I W S)) s.args) (again : Fn I (s.Var I (S → s.Tree σ I W S)) s.args)

/-- A decoding of tags at every token. -/
abbrev Interp : Type 1 := (σ : Type) → [Store σ] → Ty → Type

/-- A world at every token: a world may hold refs, so it may depend on `σ`. -/
abbrev World : Type 1 := (σ : Type) → [Store σ] → Type

/-- An operation's implementation: for each choice of its `typeArgc` type arguments' tags, a
wrapper of that instance's shape, and its rule's state type, `Empty` if the rule does not loop,
at every token. -/
structure OpImpl (I : Interp) (W : World) where
  typeArgc : Nat
  shape : Vector Ty typeArgc → Shape
  St : (σ : Type) → [Store σ] → Vector Ty typeArgc → Type := fun _ _ _ => Empty
  fn : (σ : Type) → [Store σ] → (targs : Vector Ty typeArgc) →
    Impl σ (I σ) (W σ) (shape targs) (St σ targs)

/-- What a name links to: an operation, by its position in the table's `ops`, or one of the
machine's instructions, on its heap or calling a closure. -/
inductive LinkOp where
  | impl (i : Nat)
  | refNew
  | refGet
  | refSet
  | callCode
  deriving Repr, DecidableEq

/-- What `#dyn_sem_table` generates: the decoding of tags, the world and its initial value,
and every operation it implements, by environment name, each at every token. -/
structure Table where
  /-- A name for each head, for messages: the first Dyn type whose Lean type it is. -/
  typeNames : Array Name
  interp : Interp
  W : World
  /-- The initial world, at every token: so it holds no ref (`no_forge`). -/
  w0 : (σ : Type) → [Store σ] → W σ
  ops : Array (Name × OpImpl interp W)

/-- The state type of operation `k` of the table at the type arguments' tags `ts`, at the token
`σ`: its rule's, or `Empty` if there is no such operation.  A type, so it costs nothing at run
time. -/
def Table.stateOf (T : Table) (σ : Type) [Store σ] (k : Nat) (ts : Array Ty) : Type :=
  match T.ops[k]? with
  | some (_, o) => if h : ts.size = o.typeArgc then o.St σ ⟨ts, h⟩ else Empty
  | none => Empty

/-- The state type of operation `k`, found at `k`, at the type arguments `ts` is its rule's. -/
theorem Table.stateOf_eq (T : Table) (σ : Type) [Store σ] {k : Nat} {n : Name}
    {o : OpImpl T.interp T.W} (hk : T.ops[k]? = some (n, o)) (ts : Vector Ty o.typeArgc) :
    T.stateOf σ k ts.toArray = o.St σ ts := by
  unfold Table.stateOf
  rw [hk]
  exact dite_eq_left ts.size_toArray

/-! ## Models -/

/-- The tag of a ref to a cell holding values of tag `t`. -/
abbrev Ty.ref (t : Ty) : Ty := .app 0 [t]

/-- The tag of a code pointer taking tags `ts` and returning tag `r`. -/
abbrev Ty.fn (ts : List Ty) (r : Ty) : Ty := .app 1 [.list ts, r]

/-- A table with what the engine needs: that the decoding is the engine's on refs and code
pointers, and the literals' types' tags.  `#dyn_sem_table` generates one for every
environment that extends `Base`. -/
structure Model extends Table where
  refEq : ∀ (σ : Type) [Store σ] (t : Ty), interp σ t.ref = Ref σ (interp σ t)
  fnEq : ∀ (σ : Type) [Store σ] (ts : List Ty) (r : Ty),
    interp σ (Ty.fn ts r) = FnRef σ (ts.map (interp σ)) (interp σ r)
  /-- `base.Unit`'s tag and value, which `refSet` returns. -/
  unit : Ty
  unitVal : (σ : Type) → [Store σ] → interp σ unit
  /-- The tags of the other literals' types, and their values. -/
  bool : Ty
  ofBool : (σ : Type) → [Store σ] → Bool → interp σ bool
  int : Ty
  ofInt : (σ : Type) → [Store σ] → Int → interp σ int
  float : Ty
  ofFloat : (σ : Type) → [Store σ] → Float → interp σ float
  str : Ty
  ofStr : (σ : Type) → [Store σ] → String → interp σ str
  /-- What linking resolves names to: every operation of the table and the base's machine
  instructions, and every Dyn type's head.  Dyn types with one Lean type share a head.
  The generator builds both trees, so that linking computes only the keys of the names a
  module uses. -/
  index : NameMap LinkOp
  typeIndex : NameMap Nat
  /-- The decoding, as the instance at which the model's tags of Lean types are found: a
  `TagOf σ α` at `decode σ` is `α`'s tag in this model.  Each table has its own constant, so
  that one model's tags are not found at another's. -/
  decode : (σ : Type) → [Store σ] → Decode σ
  decode_eq : ∀ (σ : Type) [Store σ], (decode σ).decode = interp σ

/-- A tag of `α` in `M` decodes, in `M`, to `α`. -/
theorem Model.tag_ok {M : Model} {σ : Type} [Store σ] {α : Type}
    (t : @TagOf σ _ (M.decode σ) α) : M.interp σ t.tag = α :=
  (congrFun (M.decode_eq σ) t.tag).symm.trans t.ok

/-- A start argument: a value at every token, so it holds no ref and no closure. -/
abbrev Model.Arg (M : Model) : Type 1 := (σ : Type) → [Store σ] → Dyn (M.interp σ)

/-- The argument `x`, at its Lean type's tag in `M`, which is found at every token, as the
tags a rule takes are. -/
def Model.arg (M : Model) {α : Type} (x : α)
    [t : ∀ (σ : Type) [Store σ], @TagOf σ _ (M.decode σ) α] : M.Arg :=
  fun σ _ => ⟨(t σ).tag, cast (Model.tag_ok (t σ)).symm x⟩

/-- A model at the machine's token: what a linked module and the machine see. -/
structure RunModel where
  typeNames : Array Name
  interp : Ty → Type
  W : Type
  w0 : W
  /-- The state type of an operation's rule, by the operation's position in the table and its
  type arguments' tags. -/
  St : Nat × Array Ty → Type
  refEq : ∀ t, interp t.ref = Ref Run (interp t)
  fnEq : ∀ ts r, interp (Ty.fn ts r) = FnRef Run (ts.map interp) (interp r)
  unit : Ty
  unitVal : interp unit
  bool : Ty
  ofBool : Bool → interp bool
  int : Ty
  ofInt : Int → interp int
  float : Ty
  ofFloat : Float → interp float
  str : Ty
  ofStr : String → interp str

/-- The model at the machine's token: every part instantiated once. -/
abbrev Model.at (M : Model) : RunModel where
  typeNames := M.typeNames
  interp := M.interp Run
  W := M.W Run
  w0 := M.w0 Run
  St := fun key => M.stateOf Run key.1 key.2
  refEq := M.refEq Run
  fnEq := M.fnEq Run
  unit := M.unit
  unitVal := M.unitVal Run
  bool := M.bool
  ofBool := M.ofBool Run
  int := M.int
  ofInt := M.ofInt Run
  float := M.float
  ofFloat := M.ofFloat Run
  str := M.str
  ofStr := M.ofStr Run

namespace RunModel

variable (M : RunModel)

/-- The location a ref value of contents `t` names. -/
@[inline] def locOf {t : Ty} (x : M.interp t.ref) : Nat := (cast (M.refEq t) x).loc

/-- The ref value of contents `t` at location `l`: at the machine's token, any location is one,
and an access checks it. -/
@[inline] def cellAt (t : Ty) (l : Nat) : M.interp t.ref :=
  cast (M.refEq t).symm (⟨⟨l, trivial⟩⟩ : Ref Run (M.interp t))

/-- The ref value at location `l` names location `l`. -/
theorem locOf_cellAt (t : Ty) (l : Nat) : M.locOf (M.cellAt t l) = l := by
  rw [locOf, cellAt, cast_cast, cast_eq]

/-- A code pointer value, as the token's closure. -/
@[inline] def fnOf {ts : List Ty} {r : Ty} (x : M.interp (Ty.fn ts r)) :
    FnRef Run (ts.map M.interp) (M.interp r) :=
  cast (M.fnEq ts r) x

/-- The closure of function `i` with no captures, as a code pointer value of tags `ts` and
`r`. -/
@[inline] def fnAt (ts : List Ty) (r : Ty) (i : Nat) : M.interp (Ty.fn ts r) :=
  cast (M.fnEq ts r).symm (⟨⟨i, 0, trivial⟩⟩ : FnRef Run (ts.map M.interp) (M.interp r))

/-- The code pointer value of function `i` is the token's closure of `i` with no captures. -/
theorem fnOf_fnAt (ts : List Ty) (r : Ty) (i : Nat) :
    M.fnOf (M.fnAt ts r i) = ⟨⟨i, 0, trivial⟩⟩ := by
  rw [fnOf, fnAt, cast_cast, cast_eq]

end RunModel

end

end Strata.Dyn.Exec
