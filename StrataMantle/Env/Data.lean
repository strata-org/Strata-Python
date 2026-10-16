/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Name

set_option autoImplicit false

/-!
# Common datatypes for Mantle.
-/

namespace Strata.Mantle

public section

/-! ## Positivity -/

/-- Flags whether a mutual group of datatypes may recurse through a type constructor's parameter. -/
inductive Positivity where
  /-- Positive: a recursive occurrence here is allowed. -/
  | pos
  /-- Not positive: a group may not recurse through it. -/
  | non
deriving DecidableEq, Repr

/-! ## Kinds -/

/-- What a type parameter ranges over: types, or lists of types. -/
inductive Kind where
  | type
  | list
deriving DecidableEq, Repr

/-- Why arguments do not fit the parameters they are passed to: the wrong number of them, or
argument `i`, counted from 0, of the wrong kind.  Each caller words it for its own messages. -/
inductive KindError where
  | count (given expected : Nat)
  | kind (i : Nat) (given expected : Kind)
deriving DecidableEq, Repr

/-- The first argument of `given`, counted from `i`, whose kind is not its parameter's in
`expected`. -/
private def KindError.firstKind? (i : Nat) : List Kind → List Kind → Option KindError
  | g :: gs, e :: es => if g = e then firstKind? (i + 1) gs es else some (.kind i g e)
  | _, _ => none

/-- The first way arguments of kinds `given` fail to fit parameters of kinds `expected`: a count
that differs, else the first argument of the wrong kind.  `none` exactly when they fit
(`check?_eq_none_iff`), so a caller decides the fit and words the failure with this one check. -/
def KindError.check? (expected given : Array Kind) : Option KindError :=
  if given.size ≠ expected.size then some (.count given.size expected.size)
  else firstKind? 0 given.toList expected.toList

/-- Kinds of the same length have no argument of the wrong kind exactly when they are equal. -/
private theorem KindError.firstKind?_eq_none_iff :
    ∀ {i : Nat} {gs es : List Kind}, gs.length = es.length →
      (firstKind? i gs es = none ↔ gs = es)
  | _, [], [], _ => by simp [firstKind?]
  | _, [], _ :: _, h => absurd h (by simp)
  | _, _ :: _, [], h => absurd h (by simp)
  | i, g :: gs, e :: es, h => by
    have ih := firstKind?_eq_none_iff (i := i + 1) (gs := gs) (es := es) (by simpa using h)
    by_cases hge : g = e
    · simp [firstKind?, hge, ih]
    · simp [firstKind?, hge]

/-- The arguments fit exactly when their kinds are the parameters'. -/
theorem KindError.check?_eq_none_iff {expected given : Array Kind} :
    check? expected given = none ↔ given = expected := by
  unfold check?
  by_cases hs : given.size = expected.size
  · rw [if_neg (fun h => h hs), firstKind?_eq_none_iff (by simpa using hs), Array.toList_inj]
  · rw [if_pos hs]
    exact ⟨fun h => absurd h (by simp), fun h => absurd (h ▸ rfl) hs⟩

/-! ## Annotations

Every declaration carries an annotation `α` that could be any type.  The
environment layers are polymorphic in it and never read it.
-/

/-! ## Declarations -/

namespace Name

/-- The name of the case instruction of the datatype named `n`: `case` under `n`. -/
@[expose] def caseName (n : Name) : Name := .str n "case"

/-- The last string component of a name, or `""` if it does not end in one.  A case
instruction names the successor of each constructor so. -/
@[expose] def lastString : Name → String
  | .str _ s => s
  | _ => ""

end Name

-- Exposed so that `decide` can compare parameters in other modules.
@[expose] section

/-- A named parameter. -/
structure Param (τ : Type) where
  name : String
  type : τ
deriving DecidableEq

-- Through `List.map`, so that `decide` and `rfl` evaluate it: `Array.map` does not reduce.
/-- The kinds of an instruction's type parameters, each a name and a kind, in order: the scope
the instruction's type expressions are written in. -/
@[reducible] def Param.kinds (ps : Array (Param Kind)) : Array Kind :=
  ⟨ps.toList.map (·.type)⟩

/-- A type parameter of a `type` or `data`: its positivity and its kind.  A list parameter's
positivity is its elements'. -/
structure TyParam where
  polarity : Positivity
  kind : Kind := .type
deriving DecidableEq

/-- A positive type parameter. -/
abbrev TyParam.pos : TyParam := ⟨.pos, .type⟩

/-- A non-positive type parameter. -/
abbrev TyParam.non : TyParam := ⟨.non, .type⟩

-- Through `List.map`, so that `decide` and `rfl` evaluate it: `Array.map` does not reduce.
/-- The kinds of a `type` or `data`'s parameters, in order: the scope a datatype's payloads are
written in. -/
@[reducible] def TyParam.kinds (ps : Array (Param TyParam)) : Array Kind :=
  ⟨ps.toList.map (·.type.kind)⟩

end

/-- A type declaration. -/
structure TypeDecl (α : Type) where
  ann : α
  name : Name
  /-- Type parameters with their names, positivity and kinds. -/
  params : Array (Param TyParam) := #[]
deriving DecidableEq

/-- How many arguments the type constructor takes. -/
@[expose] def TypeDecl.arity {α : Type} (d : TypeDecl α) : Nat := d.params.size

-- Through `List.map`, so that `decide` and `rfl` evaluate it: `Array.map` does not reduce.
/-- The kind of each argument the type constructor takes. -/
@[expose] def TypeDecl.kinds {α : Type} (d : TypeDecl α) : Array Kind :=
  TyParam.kinds d.params

-- A `List`, so that `decide` can prove the names distinct.
/-- The names of the type's parameters, in order. -/
@[expose] def TypeDecl.paramNames {α : Type} (d : TypeDecl α) : List String :=
  d.params.toList.map (·.name)

/-- A constructor in a datatype. -/
structure Ctor (α : Type) (τ : Type) where
  ann : α
  name : Name
  args : Array (Param τ)
deriving DecidableEq

/-- A datatype declaration. -/
structure DatatypeDecl (α : Type) (τ : Type) where
  ann : α
  name : Name
  /-- Type parameters with their names, positivity and kinds. -/
  params : Array (Param TyParam) := #[]
  /-- The constructors for the datatype. -/
  ctors : Array (Ctor α τ)
deriving DecidableEq

/-- How many arguments the datatype takes. -/
@[expose] def DatatypeDecl.arity {α τ : Type} (d : DatatypeDecl α τ) : Nat := d.params.size

/-- The names of the datatype's parameters, in order. -/
@[expose] def DatatypeDecl.paramNames {α τ : Type} (d : DatatypeDecl α τ) : List String :=
  d.params.toList.map (·.name)

/-- Converts a datatype declaration to the corresponding abstract type declaration. -/
@[expose] def DatatypeDecl.toTypeDecl {α τ : Type} (d : DatatypeDecl α τ) : TypeDecl α :=
  { ann := d.ann, name := d.name, params := d.params }

/-- A mutual group of datatypes: a non-empty array of datatype declarations. -/
structure DataGroup (α : Type) (τ : Type) where
  members : Array (DatatypeDecl α τ)
  nonEmpty : 0 < members.size

namespace DataGroup

variable {α τ : Type}

/-- Groups are equal when their members are. -/
instance [DecidableEq α] [DecidableEq τ] : DecidableEq (DataGroup α τ) := fun a b =>
  decidable_of_iff (a.members = b.members) (by
    cases a; cases b
    constructor
    · intro h; subst h; rfl
    · intro h; simpa using h)

/-- The datatype the group is headed by, and whose name addresses it. -/
@[expose] def first (g : DataGroup α τ) : DatatypeDecl α τ := g.members[0]'g.nonEmpty

/-- The member at an index, if any. -/
@[expose] def member? (g : DataGroup α τ) (i : Nat) : Option (DatatypeDecl α τ) := g.members[i]?

/-- The type this group declares under `n`, if any. -/
@[expose] def typeOf? (g : DataGroup α τ) (n : Name) : Option (TypeDecl α) :=
  (g.members.find? (·.name == n)).map (·.toTypeDecl)

/-- Every name the group introduces: one per member, then one per constructor, then each
member's case instruction. -/
@[expose] def names (g : DataGroup α τ) : Array Name :=
  g.members.map (·.name) ++
    ((g.members.flatMap fun m => m.ctors.map (·.name)) ++ g.members.map (·.name.caseName))

/-- The constructor at an address inside the group. -/
@[expose] def ctor? (g : DataGroup α τ) (i j : Nat) : Option (Ctor α τ) := do
  let m ← g.member? i
  m.ctors[j]?

end DataGroup

/-- Where a constructor sits: the head of its mutual group, which datatype of the group, and
which constructor of that datatype.  An instruction declaration carrying one is that
constructor; the datatype's own constructor list is what the address is read against. -/
structure CtorAddr where
  head : Name
  dataIdx : Nat
  /-- Which constructor of the datatype. -/
  idx : Nat
deriving DecidableEq

/-- Which datatype a case instruction eliminates: the head of its mutual group, and which
datatype of the group.  An instruction declaration carrying one is that case instruction. -/
structure CaseAddr where
  head : Name
  dataIdx : Nat
deriving DecidableEq

/-- What an instruction declaration is.  A constructor and a case instruction are declared
only with their group, which well-formedness checks the declaration against. -/
inductive InsnKind where
  /-- An ordinary instruction: nothing derives it. -/
  | decl
  /-- Constructor `addr.idx` of member `addr.dataIdx` of the group headed by `addr.head`. -/
  | ctor (addr : CtorAddr)
  /-- The case instruction of member `addr.dataIdx` of the group headed by `addr.head`. -/
  | case (addr : CaseAddr)
deriving DecidableEq

namespace InsnKind

/-- The head of the group a constructor or case instruction belongs to. -/
@[expose] def head? : InsnKind → Option Name
  | .decl => none
  | .ctor a => some a.head
  | .case a => some a.head

/-- Where a constructor sits, if the instruction is one. -/
@[expose] def ctor? : InsnKind → Option CtorAddr
  | .ctor a => some a
  | _ => none

end InsnKind

/-! ### Changing the type representation

`mapTy` rewrites every payload type; names, parameters and annotations carry over. -/

@[expose] def Param.mapTy {τ τ' : Type} (f : τ → τ') (p : Param τ) : Param τ' :=
  ⟨p.name, f p.type⟩

@[expose] def Ctor.mapTy {α τ τ' : Type} (f : τ → τ') (c : Ctor α τ) : Ctor α τ' :=
  ⟨c.ann, c.name, c.args.map (Param.mapTy f)⟩

@[expose] def DatatypeDecl.mapTy {α τ τ' : Type} (f : τ → τ') (m : DatatypeDecl α τ) :
    DatatypeDecl α τ' :=
  ⟨m.ann, m.name, m.params, m.ctors.map (Ctor.mapTy f)⟩

@[expose] def DataGroup.mapTy {α τ τ' : Type} (f : τ → τ') (g : DataGroup α τ) :
    DataGroup α τ' :=
  ⟨g.members.map (DatatypeDecl.mapTy f), by simpa using g.nonEmpty⟩

/-! ### Erasing annotations

`erase` replaces every annotation by `()`. -/

/-- The type declaration without its annotation. -/
@[expose] def TypeDecl.erase {α : Type} (d : TypeDecl α) : TypeDecl Unit := { d with ann := () }

/-- The constructor without its annotation. -/
@[expose] def Ctor.erase {α τ : Type} (c : Ctor α τ) : Ctor Unit τ := { c with ann := () }

/-- The datatype without its annotations. -/
@[expose] def DatatypeDecl.erase {α τ : Type} (m : DatatypeDecl α τ) : DatatypeDecl Unit τ :=
  { m with ann := (), ctors := m.ctors.map Ctor.erase }

/-- The group without its annotations. -/
@[expose] def DataGroup.erase {α τ : Type} (g : DataGroup α τ) : DataGroup Unit τ :=
  ⟨g.members.map DatatypeDecl.erase, by simpa using g.nonEmpty⟩

end

end Strata.Mantle
