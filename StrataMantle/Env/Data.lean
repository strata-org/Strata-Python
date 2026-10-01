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

/-! ## Annotations

Every declaration carries an annotation `α` that could be any type.  The
environment layers are polymorphic in it and never read it.
-/

/-! ## Declarations -/

-- Exposed so that `decide` can compare parameters in other modules.
@[expose] section

/-- A named parameter. -/
structure Param (τ : Type) where
  name : String
  type : τ
deriving DecidableEq

end

/-- A type declaration. -/
structure TypeDecl (α : Type) where
  ann : α
  name : Name
  /-- Type parameters with their names and positivity. -/
  params : Array (Param Positivity) := #[]
deriving DecidableEq

/-- How many arguments the type constructor takes. -/
@[expose] def TypeDecl.arity {α : Type} (d : TypeDecl α) : Nat := d.params.size

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
  /-- Type parameters with their names and positivity. -/
  params : Array (Param Positivity) := #[]
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

/-- Every name the group introduces: one per member, then one per constructor. -/
@[expose] def names (g : DataGroup α τ) : Array Name :=
  g.members.map (·.name) ++ g.members.flatMap fun m => m.ctors.map (·.name)

/-- The constructor at an address inside the group. -/
@[expose] def ctor? (g : DataGroup α τ) (i j : Nat) : Option (Ctor α τ) := do
  let m ← g.member? i
  m.ctors[j]?

end DataGroup

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

end

end Strata.Mantle
