/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.Data
public import StrataMantle.Env.TypeExprRaw
public import StrataMantle.Util.IndexMap

set_option autoImplicit false

/-!
# Declarations and environments, unchecked

Plain, non-dependent representations: declarations carry values only, and
well-formedness is a separate predicate over them (`StrataMantle.Env.WF`).
As with `IndexMap.Raw`, the `Raw` suffix marks the representation that does not
carry its invariant.

`Env.Raw α` keeps its declarations in an `IndexMap`, in declaration order, and
well-formedness demands that every type reference resolve to an *earlier* declaration.
-/

open Strata (IndexMap)

namespace Strata.Mantle

public section

variable {α : Type}

/--
The signature of a region an instruction takes as an argument: the types of the parameters
of its entry block, and the type it returns.

Control inside a region leaves it only by a jump to its exit, which takes a value of the
return type.  The types are written under the instruction's type variables; a region binds none of
its own.
-/
structure RegionSig.Raw where
  params : Array (Param TypeExpr.Raw)
  returnType : TypeExpr.Raw
deriving DecidableEq

/--
An instruction declaration has a name, a list of type parameters, a list of required
arguments, an optional variadic parameter naming and typing any additional arguments beyond
the required arguments, and a return type, unless it is terminal.

The type parameters are named, but type expressions refer to them by de Bruijn level:
`.var i` is `typeParams[i]`.  The names are for printing and diagnostics.

It may also take named regions, each with its own signature, and named successors: blocks
it may transfer to, each receiving values of the declared types after whatever the use site
pre-binds.  A raising operation declares one, conventionally `err`, carrying the exception.
Both default to none.

A terminal instruction, one with no return type, ends its block: it never falls through, so
it leaves only by a successor, and it produces no result.  One with a return type falls
through to the next instruction, and may also transfer to any successor.

A constructor of a datatype is an instruction like any other, and so is a datatype's case
instruction; `kind` says which, and where it sits in its group.  Only adding the group
declares either: well-formedness checks such a declaration against the declaration the group
derives for it.
-/
structure InsnDecl.Raw (α : Type) where
  ann : α
  name : Name
  typeParams : Array String := #[]
  argTypes : Array (Param TypeExpr.Raw)
  variadic : Option (Param TypeExpr.Raw) := none
  /-- What it returns, or `none` if it is terminal. -/
  returnType : Option TypeExpr.Raw
  regions : Array (Param RegionSig.Raw) := #[]
  succs : Array (Param (Array TypeExpr.Raw)) := #[]
  kind : InsnKind := .decl
deriving DecidableEq

/-- Whether the instruction ends its block: it has no return type. -/
@[expose, reducible] def InsnDecl.Raw.terminal {α : Type} (d : InsnDecl.Raw α) : Bool :=
  d.returnType.isNone

/-- The declaration with its annotation erased: everything well-formedness compares. -/
@[expose] def InsnDecl.Raw.erase {α : Type} (d : InsnDecl.Raw α) : InsnDecl.Raw Unit :=
  { d with ann := () }

/-- How many type variables the instruction binds: the scope its type expressions are
checked in.  Reducible, so it computes on a literal declaration. -/
@[expose, reducible] def InsnDecl.Raw.typeArgc (d : InsnDecl.Raw α) : Nat := d.typeParams.size

/-! Parameter names, as lists: `List.Nodup` of a literal reduces in the kernel, so `decide`
proves distinctness for an environment written in Lean. -/

/-- The names of a region's parameters, in order. -/
@[expose] def RegionSig.Raw.paramNames (r : RegionSig.Raw) : List String :=
  r.params.toList.map (·.name)

/-- Every name an instruction binds: its type parameters', its arguments', its variadic's,
its regions', then its successors'.  They share one namespace. -/
@[expose] def InsnDecl.Raw.paramNames {α : Type} (d : InsnDecl.Raw α) : List String :=
  d.typeParams.toList ++ d.argTypes.toList.map (·.name) ++ (d.variadic.map (·.name)).toList ++
    d.regions.toList.map (·.name) ++ d.succs.toList.map (·.name)

/-- A declaration, annotated with a value of type `α`. -/
inductive Decl.Raw (α : Type) where
/-- A primitive type: no constructors, and so no elimination.  `Int`, `String`, `Ref`, a
language's opaque value type.  Not the same as a datatype with no constructors, which is
empty and may be eliminated by a case instruction with no successors. -/
| type (decl : TypeDecl α)
/-- A mutual group of datatypes, carried whole by the declaration that heads it.  It declares
the first datatype's name; the declarations after it that address it declare the rest. -/
| dataHead (group : DataGroup α TypeExpr.Raw)
/-- A name for member `idx` of the group headed by `head`. -/
| dataRest (name : Name) (head : Name) (idx : Nat)
/-- An instruction, which may be a constructor of a group declared earlier. -/
| insn (decl : InsnDecl.Raw α)
deriving DecidableEq

namespace Decl.Raw

@[expose]
def name : Decl.Raw α → Name
| .type d => d.name
| .dataHead g => g.first.name
| .dataRest n _ _ => n
| .insn d => d.name

@[simp] theorem name_type (d : TypeDecl α) : (Decl.Raw.type d).name = d.name := rfl

@[simp] theorem name_dataHead (g : DataGroup α TypeExpr.Raw) :
    (Decl.Raw.dataHead g).name = g.first.name := rfl

@[simp] theorem name_dataRest (n h : Name) (i : Nat) :
    (Decl.Raw.dataRest (α := α) n h i).name = n := rfl

@[simp] theorem name_insn (d : InsnDecl.Raw α) : (Decl.Raw.insn d).name = d.name := rfl

/-- Which mutual group a declaration belongs to.  A primitive, a group head and an
operation are each their own group; a member alias, a constructor and a case instruction name
the group they address. -/
@[expose]
def head : Decl.Raw α → Name
| .type d => d.name
| .dataHead g => g.first.name
| .dataRest _ h _ => h
| .insn d => d.kind.head?.getD d.name

@[simp] theorem head_type (d : TypeDecl α) : (Decl.Raw.type d).head = d.name := rfl

@[simp] theorem head_dataHead (g : DataGroup α TypeExpr.Raw) :
    (Decl.Raw.dataHead g).head = g.first.name := rfl

@[simp] theorem head_dataRest (n h : Name) (i : Nat) :
    (Decl.Raw.dataRest (α := α) n h i).head = h := rfl

/-- An instruction is its own group, unless it is a constructor or a case instruction of
one. -/
@[simp] theorem head_insn (d : InsnDecl.Raw α) :
    (Decl.Raw.insn d).head = d.kind.head?.getD d.name := rfl

/-- The group a declaration carries, if it heads one. -/
@[expose]
def asGroup : Decl.Raw α → Option (DataGroup α TypeExpr.Raw)
| .dataHead g => some g
| _ => none

/-- The address a declaration that belongs to an earlier group points at: its group's head,
which member, and for a constructor, which constructor of that member. -/
@[expose]
def asAlias : Decl.Raw α → Option (Name × Nat × Option Nat)
| .dataRest _ h i => some (h, i, none)
| .insn d => d.kind.ctor?.map fun a => (a.head, a.dataIdx, some a.idx)
| _ => none

@[expose]
def asInsn : Decl.Raw α → Option (InsnDecl.Raw α)
| .insn d => some d
| _ => none

@[simp] theorem asGroup_dataHead (g : DataGroup α TypeExpr.Raw) :
    (Decl.Raw.dataHead g).asGroup = some g := rfl

@[simp] theorem asGroup_type (d : TypeDecl α) : (Decl.Raw.type d).asGroup = none := rfl

@[simp] theorem asAlias_dataRest (n h : Name) (i : Nat) :
    (Decl.Raw.dataRest (α := α) n h i).asAlias = some (h, i, none) := rfl

@[simp] theorem asInsn_insn (d : InsnDecl.Raw α) : (Decl.Raw.insn d).asInsn = some d := rfl

@[simp] theorem asInsn_type (d : TypeDecl α) : (Decl.Raw.type d).asInsn = none := rfl

@[simp] theorem asInsn_dataHead (g : DataGroup α TypeExpr.Raw) :
    (Decl.Raw.dataHead g).asInsn = none := rfl

@[simp] theorem asInsn_dataRest (n h : Name) (i : Nat) :
    (Decl.Raw.dataRest (α := α) n h i).asInsn = none := rfl

end Decl.Raw

namespace DataGroup

/-- The instruction that is constructor `c`, the `j`th of `m`, the group's `i`th member.  Its
type parameters are `m`'s, by name and in order; its arguments are `c`'s payload; it returns
`m` applied to its parameters; and it is marked as that constructor.  No variadic, regions or
successors, and not terminal. -/
@[expose]
def ctorDecl (g : DataGroup α TypeExpr.Raw) (i : Nat) (m : DatatypeDecl α TypeExpr.Raw) (j : Nat)
    (c : Ctor α TypeExpr.Raw) : InsnDecl.Raw α where
  ann := c.ann
  name := c.name
  typeParams := m.params.map (·.name)
  argTypes := c.args
  returnType := some (.app m.name (TypeExpr.Raw.vars m.arity))
  kind := .ctor ⟨g.first.name, i, j⟩

/-- A constructor's instruction is named as the constructor is. -/
@[simp] theorem name_ctorDecl (g : DataGroup α TypeExpr.Raw) (i : Nat)
    (m : DatatypeDecl α TypeExpr.Raw) (j : Nat) (c : Ctor α TypeExpr.Raw) :
    (g.ctorDecl i m j c).name = c.name := rfl

/-- The instruction that is constructor `j` of member `i`, if the group has one. -/
@[expose]
def ctorInsn? (g : DataGroup α TypeExpr.Raw) (i j : Nat) : Option (InsnDecl.Raw α) := do
  let m ← g.member? i
  let c ← m.ctors[j]?
  pure (g.ctorDecl i m j c)

/-- The case instruction of `m`, the group's `i`th member: terminal; `m`'s type parameters,
by name and in order; one argument `scrutinee`, of `m` applied to its parameters; and one
successor per constructor, in declaration order, named by the last component of the
constructor's name and receiving its payload.  It is marked as `m`'s case. -/
@[expose]
def caseDecl (g : DataGroup α TypeExpr.Raw) (i : Nat) (m : DatatypeDecl α TypeExpr.Raw) :
    InsnDecl.Raw α where
  ann := m.ann
  name := m.name.caseName
  typeParams := m.params.map (·.name)
  argTypes := #[⟨"scrutinee", .app m.name (TypeExpr.Raw.vars m.arity)⟩]
  returnType := none
  succs := m.ctors.map fun c => ⟨c.name.lastString, c.args.map (·.type)⟩
  kind := .case ⟨g.first.name, i⟩

/-- A member's case instruction is named after the member. -/
@[simp] theorem name_caseDecl (g : DataGroup α TypeExpr.Raw) (i : Nat)
    (m : DatatypeDecl α TypeExpr.Raw) :
    (g.caseDecl i m).name = m.name.caseName := rfl

/-- The case instruction of member `i`, if the group has that member. -/
@[expose]
def caseInsn? (g : DataGroup α TypeExpr.Raw) (i : Nat) :
    Option (InsnDecl.Raw α) :=
  (g.member? i).map fun m => g.caseDecl i m

/-- Every declaration a group needs: the head that carries it, a name for each member past
the first, an instruction for each constructor, and each member's case instruction, in that
order.  The addresses and the signatures are computed only here. -/
@[expose]
def decls (g : DataGroup α TypeExpr.Raw) : Array (Decl.Raw α) :=
  let head := g.first.name
  -- One `map` with a case at index `0`, so the names line up with `DataGroup.names`.
  g.members.zipIdx.map
      (fun (m, i) => if i = 0 then .dataHead g else .dataRest m.name head i)
    ++ (g.members.zipIdx.flatMap
          (fun (m, i) => m.ctors.zipIdx.map (fun (c, j) => .insn (g.ctorDecl i m j c)))
        ++ g.members.zipIdx.map (fun (m, i) => .insn (g.caseDecl i m)))

/-- Mapping past a `zipIdx` that the function ignores the index of. -/
private theorem map_fst_zipIdx {β γ : Type} (f : β → γ) (l : List β) :
    l.zipIdx.map (fun p => f p.fst) = l.map f := by
  rw [show (fun p : β × Nat => f p.fst) = f ∘ Prod.fst from rfl, ← List.map_map,
    List.zipIdx_map_fst]

private theorem flatMap_fst_zipIdx {β γ : Type} (f : β → List γ) (l : List β) :
    l.zipIdx.flatMap (fun p => f p.fst) = l.flatMap f :=
  calc l.zipIdx.flatMap (fun p => f p.fst)
      = (l.zipIdx.map Prod.fst).flatMap f := (List.flatMap_map Prod.fst f l.zipIdx).symm
    _ = l.flatMap f := by rw [List.zipIdx_map_fst]

/-- The head declaration comes first. -/
theorem decls_getElem?_zero (g : DataGroup α TypeExpr.Raw) :
    g.decls.toList[0]? = some (.dataHead g) := by
  have hlen : 0 < g.members.toList.length := by simpa using g.nonEmpty
  simp only [DataGroup.decls, Array.toList_append, Array.toList_map, Array.toList_zipIdx,
    Array.toList_flatMap]
  rw [List.getElem?_append_left (by simpa using hlen), List.getElem?_map,
    List.getElem?_zipIdx, List.getElem?_eq_getElem hlen]
  simp

/-- Every member past the first is named, at its own position, by an alias of the head. -/
theorem decls_getElem?_of_member (g : DataGroup α TypeExpr.Raw) {j : Nat}
    {m : DatatypeDecl α TypeExpr.Raw} (hm : g.members[j]? = some m) (hj : j ≠ 0) :
    g.decls.toList[j]? = some (.dataRest m.name g.first.name j) := by
  have hlen : j < g.members.toList.length := by
    simpa using (Array.getElem?_eq_some_iff.mp hm).1
  simp only [DataGroup.decls, Array.toList_append, Array.toList_map, Array.toList_zipIdx,
    Array.toList_flatMap]
  rw [List.getElem?_append_left (by simpa using hlen), List.getElem?_map,
    List.getElem?_zipIdx, Array.getElem?_toList, hm]
  simp [hj]

/-- The declarations are named exactly the names the group introduces, in that order. -/
theorem decls_names (g : DataGroup α TypeExpr.Raw) :
    g.decls.map (·.name) = g.names := by
  -- at index `0` the head declaration is named after the first member, which is what
  -- `DataGroup.first` is, so both arms of the `if` give that member's name
  have hfirst : ∀ p ∈ g.members.toList.zipIdx,
      Decl.Raw.name (if p.2 = 0 then .dataHead g else .dataRest p.1.name g.first.name p.2) =
        p.1.name := by
    intro p hp
    have hget : g.members.toList[p.2]? = some p.1 := List.mk_mem_zipIdx_iff_getElem?.mp hp
    split
    · rename_i h0
      rw [h0] at hget
      have h1 : g.members[0]? = some p.1 := by simpa using hget
      simp only [Decl.Raw.name_dataHead, DataGroup.first]
      rw [Array.getElem?_eq_getElem g.nonEmpty] at h1
      rw [Option.some.inj h1]
    · rfl
  -- the constructor block ignores its member's index too, once the names are read off
  have hctors : ∀ p : DatatypeDecl α TypeExpr.Raw × Nat,
      ((p.1.ctors.toList.zipIdx.map
          (fun x => Decl.Raw.insn (g.ctorDecl p.2 p.1 x.snd x.fst))).map
            (Decl.Raw.name (α := α)))
        = p.1.ctors.toList.map (·.name) := by
    intro p
    rw [List.map_map]
    simp only [Function.comp_def, Decl.Raw.name_insn, name_ctorDecl]
    exact map_fst_zipIdx _ _
  apply Array.toList_inj.mp
  simp only [DataGroup.decls, DataGroup.names, Array.toList_append, Array.toList_map,
    Array.toList_flatMap, Array.toList_zipIdx, List.map_append]
  congr 1
  · rw [List.map_map]
    simp only [Function.comp_def]
    rw [List.map_congr_left hfirst]
    exact map_fst_zipIdx _ _
  · congr 1
    · rw [List.map_flatMap, funext hctors]
      exact flatMap_fst_zipIdx (fun m => m.ctors.toList.map (·.name)) g.members.toList
    · rw [List.map_map]
      simp only [Function.comp_def, Decl.Raw.name_insn, name_caseDecl]
      exact map_fst_zipIdx (fun m : DatatypeDecl α TypeExpr.Raw => m.name.caseName) _

/-- `d` is one of the declarations past the head that `decls` computes for `g`: a member past
the first, addressed through `g`'s head under the name `g` gives it there, or the
instruction that is one of `g`'s constructors or one of its members' case instructions. -/
@[expose] def IsAlias (g : DataGroup α TypeExpr.Raw) : Decl.Raw α → Prop
  | .dataRest n h i => h = g.first.name ∧ (g.member? i).map (·.name) = some n
  | .insn d => (∃ i j, g.ctorInsn? i j = some d) ∨ ∃ i, g.caseInsn? i = some d
  | _ => False

/-- The head comes first and everything after it is an alias of the group. -/
theorem decls_toList_eq_cons (g : DataGroup α TypeExpr.Raw) :
    ∃ rest, g.decls.toList = .dataHead g :: rest ∧ ∀ d ∈ rest, g.IsAlias d := by
  obtain ⟨m₀, ms, hms⟩ : ∃ m₀ ms, g.members.toList = m₀ :: ms := by
    have hne : g.members.toList ≠ [] := by
      intro h
      have := g.nonEmpty
      rw [← Array.length_toList, h] at this
      simp at this
    exact List.exists_cons_of_ne_nil hne
  have hfirst : g.first = m₀ := by
    have : g.members.toList[0]? = some m₀ := by rw [hms]; rfl
    simpa [DataGroup.first, Array.getElem?_eq_getElem g.nonEmpty] using this
  refine ⟨(ms.zipIdx 1).map
      (fun p => if p.2 = 0 then Decl.Raw.dataHead g else .dataRest p.1.name g.first.name p.2) ++
    (g.members.toList.zipIdx.flatMap
      (fun p => p.1.ctors.toList.zipIdx.map (fun q => .insn (g.ctorDecl p.2 p.1 q.2 q.1))) ++
     g.members.toList.zipIdx.map (fun p => .insn (g.caseDecl p.2 p.1))),
    ?_, ?_⟩
  · simp only [DataGroup.decls, Array.toList_append, Array.toList_map, Array.toList_zipIdx,
      Array.toList_flatMap]
    rw [hms, List.zipIdx_cons, List.map_cons]
    simp
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨⟨m, i⟩, hp, rfl⟩ := List.mem_map.mp hd
      obtain ⟨hi, hget⟩ := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp hp
      have hi0 : i ≠ 0 := by omega
      simp only [hi0, if_false, IsAlias, DataGroup.member?, true_and]
      have : g.members.toList[i]? = some m := by
        rw [hms]; obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩; simpa using hget
      simp [← Array.getElem?_toList, this]
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨⟨m, i⟩, hp, hd⟩ := List.mem_flatMap.mp hd
      obtain ⟨⟨c, j⟩, hq, rfl⟩ := List.mem_map.mp hd
      have hm : g.members.toList[i]? = some m := List.mk_mem_zipIdx_iff_getElem?.mp hp
      have hc : m.ctors.toList[j]? = some c := List.mk_mem_zipIdx_iff_getElem?.mp hq
      rw [Array.getElem?_toList] at hm hc
      exact .inl ⟨i, j, by simp [ctorInsn?, member?, hm, hc]⟩
    · obtain ⟨⟨m, i⟩, hp, rfl⟩ := List.mem_map.mp hd
      have hm : g.members.toList[i]? = some m := List.mk_mem_zipIdx_iff_getElem?.mp hp
      rw [Array.getElem?_toList] at hm
      exact .inr ⟨i, by simp [caseInsn?, member?, hm]⟩

/-- Every constructor's instruction is among the group's declarations. -/
theorem mem_decls_of_ctorInsn? {g : DataGroup α TypeExpr.Raw} {i j : Nat}
    {d : InsnDecl.Raw α} (h : g.ctorInsn? i j = some d) : Decl.Raw.insn d ∈ g.decls := by
  simp only [ctorInsn?, member?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨m, hm, c, hc, rfl⟩ := h
  simp only [decls, Array.mem_append, Array.mem_flatMap, Array.mem_map]
  refine .inr (.inl ⟨(m, i), Array.mk_mem_zipIdx_iff_getElem?.mpr hm, (c, j),
    Array.mk_mem_zipIdx_iff_getElem?.mpr hc, rfl⟩)

/-- Every member's case instruction is among the group's declarations. -/
theorem mem_decls_of_caseInsn? {g : DataGroup α TypeExpr.Raw} {i : Nat}
    {d : InsnDecl.Raw α} (h : g.caseInsn? i = some d) : Decl.Raw.insn d ∈ g.decls := by
  simp only [caseInsn?, member?, Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  simp only [decls, Array.mem_append, Array.mem_flatMap, Array.mem_map]
  exact .inr (.inr ⟨(m, i), Array.mk_mem_zipIdx_iff_getElem?.mpr hm, rfl⟩)

/-- An instruction sits past every member: the members' declarations come first. -/
theorem size_le_of_decls_getElem? {g : DataGroup α TypeExpr.Raw} {k : Nat}
    {d : InsnDecl.Raw α} (h : g.decls.toList[k]? = some (.insn d)) :
    g.members.size ≤ k := by
  simp only [decls, Array.toList_append, Array.toList_map, Array.toList_zipIdx,
    Array.toList_flatMap] at h
  rw [List.getElem?_append] at h
  split at h
  · rename_i hk
    simp only [List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨⟨m, i⟩, -, he⟩ := h
    split at he <;> simp at he
  · rename_i hk
    simpa using hk

end DataGroup

structure Env.Raw (α : Type) where
  decls : IndexMap Name (Decl.Raw α)
  /-- Every declaration is stored under its own name, positionally: `keys` is determined
      by `vals`. -/
  declsWF : decls.keys = decls.vals.map (·.name)

namespace Env.Raw

instance : Membership Name (Env.Raw α) where
  mem s n := n ∈ s.decls

instance (nm : Name) (s : Env.Raw α) : Decidable (nm ∈ s) :=
  inferInstanceAs (Decidable (nm ∈ s.decls))

instance : GetElem? (Env.Raw α) Name (Decl.Raw α) (fun s n => n ∈ s) where
  getElem s n p := s.decls[n]'p
  getElem? s n := s.decls[n]?

/-- Which mutual group the declaration named `n` belongs to.

A type is its own group's head or names it; an operation is its own group; a constructor's
group and a case instruction's are its type's. -/
@[expose]
def groupOf (env : Env.Raw α) (n : Name) : Option Name :=
  (env[n]?).map Decl.Raw.head

/-- An environment is determined by its declarations. -/
theorem eq_of_decls_eq {a b : Env.Raw α} (h : a.decls = b.decls) : a = b := by
  cases a; cases b; subst h; rfl

/-- Every declaration is reachable: the `i`-th declaration is what its own name
    looks up to. -/
theorem getElem?_getElem_vals (env : Env.Raw α) (i : Nat) (h : i < env.decls.vals.size) :
    env[(env.decls.vals[i]'h).name]? = some (env.decls.vals[i]'h) := by
  have hk : i < env.decls.keys.size := by rw [env.declsWF]; simpa using h
  have hkey : env.decls.keys[i]'hk = (env.decls.vals[i]'h).name :=
    Option.some.inj (by
      rw [← Array.getElem?_eq_getElem hk, env.declsWF, Array.getElem?_map,
        Array.getElem?_eq_getElem h]
      rfl)
  show env.decls[(env.decls.vals[i]'h).name]? = _
  rw [← hkey, IndexMap.getElem?_getElem_keys, Array.getElem?_eq_getElem h]

/-- The lookup form of `declsWF`: what a name maps to is named that. -/
theorem name_getElem (env : Env.Raw α) {n : Name} (p : n ∈ env.decls) :
    (env.decls[n]'p).name = n := by
  have hs : (IndexMap.idxOf? env.decls n).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]; simpa using p
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
  have hkn : env.decls.keys[j]? = some n := IndexMap.getElem?_keys_of_idxOf?_eq_some hj
  have hval : env.decls.vals[j]? = some (env.decls[n]'p) := by
    rw [← IndexMap.getElem?_eq_some_getElem p, IndexMap.getElem?_eq_bind_idxOf?, hj]
    simp
  rw [env.declsWF, Array.getElem?_map, hval] at hkn
  simpa using hkn

/-- The environment with no declarations. -/
def empty : Env.Raw α where
  decls := ∅
  declsWF := by simp

instance : EmptyCollection (Env.Raw α) := ⟨empty⟩

@[simp] theorem emptyCollection_eq : (∅ : Env.Raw α) = empty := rfl

@[simp]
theorem get?_empty (n : Name) : (empty : Env.Raw α)[n]? = none :=
  IndexMap.getElem?_empty n

@[simp]
theorem not_mem_empty (n : Name) : n ∉ (empty : Env.Raw α) :=
  IndexMap.not_mem_empty

@[simp]
theorem keys_empty : (empty : Env.Raw α).decls.keys = #[] :=
  IndexMap.keys_empty

-- `fresh` is unused in the body, but `keys_append` needs it.
set_option linter.unusedVariables false in
/-- Extend an environment with one declaration, which must not already be present. -/
def append (env : Env.Raw α) (decl : Decl.Raw α) (fresh : decl.name ∉ env): Env.Raw α :=
  { decls := env.decls.insert decl.name decl
    declsWF := by
      rw [IndexMap.keys_insert_of_not_mem decl fresh,
        IndexMap.vals_insert_of_not_mem decl fresh, Array.map_push, env.declsWF]
  }

-- Private: the proof unfolds `append`, whose body mentions a private helper.
@[simp]
private theorem decls_append (env : Env.Raw α) (decl : Decl.Raw α) (fresh : decl.name ∉ env) :
    (env.append decl fresh).decls = env.decls.insert decl.name decl := rfl

@[simp]
theorem get?_append (env : Env.Raw α) (decl : Decl.Raw α) (fresh : decl.name ∉ env) (n : Name) :
    (env.append decl fresh)[n]? = if decl.name == n then some decl else env[n]? := by
  show (env.append decl fresh).decls[n]? = if decl.name == n then some decl else env.decls[n]?
  rw [decls_append, IndexMap.getElem?_insert]

theorem get?_append_self (env : Env.Raw α) (decl : Decl.Raw α) (fresh : decl.name ∉ env) :
    (env.append decl fresh)[decl.name]? = some decl := by simp

@[simp]
theorem mem_append {env : Env.Raw α} {decl : Decl.Raw α} {fresh : decl.name ∉ env} {n : Name} :
    n ∈ env.append decl fresh ↔ decl.name = n ∨ n ∈ env := by
  show n ∈ (env.append decl fresh).decls ↔ decl.name = n ∨ n ∈ env.decls
  rw [decls_append]
  constructor
  · intro q
    have hg := IndexMap.getElem?_eq_some_getElem q
    rw [IndexMap.getElem?_insert] at hg
    if hn : (decl.name == n) = true then
      exact .inl (eq_of_beq hn)
    else
      simp [hn] at hg
      exact .inr (IndexMap.mem_of_getElem?_eq_some hg)
  · intro hn
    rcases hn with h | h
    · subst h
      exact IndexMap.mem_insert_self env.decls decl.name decl
    · have hg := IndexMap.getElem?_eq_some_getElem h
      refine IndexMap.mem_of_getElem?_eq_some
        (v := if decl.name == n then decl else env.decls[n]'h) ?_
      rw [IndexMap.getElem?_insert]
      split
      · rfl
      · exact hg

/-- Appending leaves the positions of existing names alone and puts the new one
    at the end. -/
theorem idxOf?_append (env : Env.Raw α) (decl : Decl.Raw α) (fresh : decl.name ∉ env)
    (n : Name) :
    IndexMap.idxOf? (env.append decl fresh).decls n =
      if decl.name == n then some env.decls.keys.size else IndexMap.idxOf? env.decls n := by
  rw [decls_append, IndexMap.idxOf?_insert_of_not_mem fresh]

@[simp]
theorem vals_empty : (empty : Env.Raw α).decls.vals = #[] :=
  IndexMap.vals_empty

/-- `append` pushes the declaration onto `vals`. -/
theorem vals_append (env : Env.Raw α) (decl : Decl.Raw α) (fresh : decl.name ∉ env) :
    (env.append decl fresh).decls.vals = env.decls.vals.push decl :=
  IndexMap.vals_insert_of_not_mem decl fresh

/-- `append` pushes the new name onto `keys`, so an environment built by repeated
    `append` iterates in declaration order. -/
theorem keys_append (env : Env.Raw α) (decl : Decl.Raw α) (fresh : decl.name ∉ env) :
    (env.append decl fresh).decls.keys = env.decls.keys.push decl.name :=
  IndexMap.keys_insert_of_not_mem decl fresh

/-! ### Appending several declarations at once

`appendList` appends a batch in one step, and `Env.Raw.WF.appendList` checks it there.  A
mutual group is added this way: its head is checked against the positions its members
occupy. -/

/-- `ds` may be appended to `env`: their names are distinct, and none is declared already. -/
@[expose] def FreshList (env : Env.Raw α) (ds : List (Decl.Raw α)) : Prop :=
  List.Pairwise (fun x y => x.name ≠ y.name) ds ∧ ∀ d ∈ ds, d.name ∉ env

instance (env : Env.Raw α) (ds : List (Decl.Raw α)) : Decidable (env.FreshList ds) :=
  inferInstanceAs (Decidable (List.Pairwise (fun x y => x.name ≠ y.name) ds ∧
    ∀ d ∈ ds, d.name ∉ env))

theorem FreshList.head {env : Env.Raw α} {d : Decl.Raw α} {ds : List (Decl.Raw α)}
    (h : env.FreshList (d :: ds)) : d.name ∉ env :=
  h.2 d List.mem_cons_self

theorem FreshList.tail {env : Env.Raw α} {d : Decl.Raw α} {ds : List (Decl.Raw α)}
    (h : env.FreshList (d :: ds)) : (env.append d h.head).FreshList ds := by
  refine ⟨(List.pairwise_cons.mp h.1).2, fun e he hm => ?_⟩
  rcases mem_append.mp hm with heq | hm
  · exact (List.pairwise_cons.mp h.1).1 e he heq
  · exact h.2 e (List.mem_cons_of_mem _ he) hm

/-- Append a batch of declarations, in order. -/
@[expose] def appendList (env : Env.Raw α) : (ds : List (Decl.Raw α)) → env.FreshList ds → Env.Raw α
  | [], _ => env
  | _ :: ds, h => (env.append _ h.head).appendList ds h.tail

/-- Whatever every `append` preserves, a batch preserves. -/
theorem appendList_induct {P : Env.Raw α → Prop}
    (step : ∀ (s : Env.Raw α) (d : Decl.Raw α) (h : d.name ∉ s), P s → P (s.append d h)) :
    ∀ {env : Env.Raw α} (ds : List (Decl.Raw α)) (h : env.FreshList ds), P env →
      P (env.appendList ds h)
  | _, [], _, hp => hp
  | env, d :: ds, h, hp => appendList_induct step ds h.tail (step env d h.head hp)

/-- The batch's names go after the existing ones, in order. -/
theorem keys_appendList : ∀ {env : Env.Raw α} (ds : List (Decl.Raw α)) (h : env.FreshList ds),
    (env.appendList ds h).decls.keys = env.decls.keys ++ (ds.map (·.name)).toArray
  | _, [], _ => by simp [appendList]
  | env, d :: ds, h => by
    rw [appendList, keys_appendList ds h.tail, keys_append]
    apply Array.toList_inj.mp
    simp

theorem vals_appendList : ∀ {env : Env.Raw α} (ds : List (Decl.Raw α)) (h : env.FreshList ds),
    (env.appendList ds h).decls.vals = env.decls.vals ++ ds.toArray
  | _, [], _ => by simp [appendList]
  | env, d :: ds, h => by
    rw [appendList, vals_appendList ds h.tail, vals_append]
    apply Array.toList_inj.mp
    simp

theorem not_getElem?_of_not_mem {env : Env.Raw α} {n : Name} (h : n ∉ env) : env[n]? = none := by
  show env.decls[n]? = none
  cases hx : env.decls[n]? with
  | none => rfl
  | some _ => exact absurd (IndexMap.mem_of_getElem?_eq_some hx) h

/-- A name resolves to what it resolved to before, or else to the batch's declaration of it. -/
theorem get?_appendList : ∀ {env : Env.Raw α} (ds : List (Decl.Raw α)) (h : env.FreshList ds)
    (n : Name), (env.appendList ds h)[n]? = env[n]?.or (ds.find? (·.name == n))
  | _, [], _, n => by simp [appendList]
  | env, d :: ds, h, n => by
    rw [appendList, get?_appendList ds h.tail, get?_append, List.find?_cons]
    by_cases hd : d.name = n
    · subst hd
      simp [not_getElem?_of_not_mem h.head]
    · have : (d.name == n) = false := by simpa using hd
      simp [this]

theorem mem_appendList {env : Env.Raw α} {ds : List (Decl.Raw α)} {h : env.FreshList ds}
    {n : Name} : n ∈ env.appendList ds h ↔ n ∈ env ∨ ∃ d ∈ ds, d.name = n := by
  show n ∈ (env.appendList ds h).decls ↔ n ∈ env.decls ∨ _
  rw [IndexMap.mem_iff_keys_contains, IndexMap.mem_iff_keys_contains, keys_appendList]
  simp

abbrev DistinctDecls (a : Array (Decl.Raw α)) :=
  List.Pairwise (λx y => x.name ≠ y.name) a.toList

/-! ### Building an environment from an array

`ofAscArray` walks the array by index, appending each declaration in turn. -/

/-- A position in `vals` is a position in the prefix. -/
private theorem lt_of_lt_size_vals {env : Env.Raw α} {decls : Array (Decl.Raw α)} {i j : Nat}
    (hvals : env.decls.vals = decls.extract 0 i) (hj : j < env.decls.vals.size) :
    j < i ∧ j < decls.size := by
  rw [hvals, Array.size_extract] at hj
  omega

/-- The prefix invariant, read off a single position. -/
private theorem getElem?_vals_of_prefix {env : Env.Raw α} {decls : Array (Decl.Raw α)} {i j : Nat}
    (hvals : env.decls.vals = decls.extract 0 i) (hj : j < i) (hjs : j < decls.size) :
    env.decls.vals[j]? = some (decls[j]'hjs) := by
  have hlt : j < (decls.extract 0 i).size := by rw [Array.size_extract]; omega
  rw [hvals, Array.getElem?_eq_getElem hlt]
  simp [Array.getElem_extract]

/-- The freshness obligation for the walk: the `i`-th name does not occur among
    the first `i` declarations. -/
private theorem name_not_mem_of_vals_prefix {decls : Array (Decl.Raw α)} (p : DistinctDecls decls)
    {env : Env.Raw α} {i : Nat} (hvals : env.decls.vals = decls.extract 0 i)
    (h : i < decls.size) : (decls[i]'h).name ∉ env := by
  intro hmem
  have hs : (IndexMap.idxOf? env.decls (decls[i]'h).name).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]; exact IndexMap.mem_iff_contains.mp hmem
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
  have hkj : env.decls.keys[j]? = some (decls[i]'h).name :=
    IndexMap.getElem?_keys_of_idxOf?_eq_some hj
  rw [env.declsWF, Array.getElem?_map] at hkj
  obtain ⟨d, hd, hdname⟩ := Option.map_eq_some_iff.mp hkj
  obtain ⟨hji, hjs⟩ := lt_of_lt_size_vals hvals (Array.getElem?_eq_some_iff.mp hd).1
  rw [getElem?_vals_of_prefix hvals hji hjs] at hd
  obtain rfl : decls[j]'hjs = d := Option.some.inj hd
  exact List.pairwise_iff_getElem.mp p j i (by simpa using hjs) (by simpa using h) hji
    (by simpa using hdname)

/-- Build an environment from an array of distinctly-named declarations, preserving
    the array's order. -/
def ofAscArray (decls : Array (Decl.Raw α)) (p : DistinctDecls decls) : Env.Raw α :=
  aux empty 0 (by simp)
  where
  aux (env : Env.Raw α) (i : Nat) (hvals : env.decls.vals = decls.extract 0 i) : Env.Raw α :=
    if h : i < decls.size then
      aux (env.append decls[i] (name_not_mem_of_vals_prefix p hvals h)) (i + 1)
        (by rw [vals_append, hvals, Array.extract_succ_right (by omega) h])
    else
      env
  termination_by decls.size - i

/-- The walk stores exactly the array. -/
private theorem vals_aux {decls : Array (Decl.Raw α)} (p : DistinctDecls decls)
    (env : Env.Raw α) (i : Nat) (hvals : env.decls.vals = decls.extract 0 i) :
    (ofAscArray.aux decls p env i hvals).decls.vals = decls := by
  unfold ofAscArray.aux
  split
  · exact vals_aux p _ (i + 1) _
  · rename_i h
    rw [hvals, Array.extract_eq_self_iff]
    omega
  termination_by decls.size - i

/-- `ofAscArray` stores exactly the declarations it was given, in order. -/
@[simp]
theorem vals_ofAscArray (decls : Array (Decl.Raw α)) (p : DistinctDecls decls) :
    (ofAscArray decls p).decls.vals = decls :=
  vals_aux p empty 0 (by simp)

/-- `ofAscArray` preserves declaration order: iteration order is exactly the
    order of the input array. -/
@[simp]
theorem keys_ofAscArray (decls : Array (Decl.Raw α)) (p : DistinctDecls decls) :
    (ofAscArray decls p).decls.keys = decls.map Decl.Raw.name := by
  rw [(ofAscArray decls p).declsWF, vals_ofAscArray]

theorem ofAscArrayMem? (decls : Array (Decl.Raw α)) (p : DistinctDecls decls) (name : Name) :
    (ofAscArray decls p)[name]? = decls.find? (fun d => d.name == name) := by
  cases hf : decls.find? (fun d => d.name == name) with
  | some d =>
    obtain ⟨hp, i, hi, hdi, -⟩ := Array.find?_eq_some_iff_getElem.mp hf
    have hlt : i < (ofAscArray decls p).decls.vals.size := by
      rw [vals_ofAscArray]; exact hi
    have hv : (ofAscArray decls p).decls.vals[i]'hlt = d :=
      Option.some.inj (by
        rw [← Array.getElem?_eq_getElem hlt, vals_ofAscArray, Array.getElem?_eq_getElem hi, hdi])
    have hget := (ofAscArray decls p).getElem?_getElem_vals i hlt
    rw [hv, eq_of_beq hp] at hget
    exact hget
  | none =>
    -- `name` names no declaration, so it is not a key, so the lookup fails.
    have hnm : name ∉ (ofAscArray decls p).decls := by
      intro hmem
      have hk : name ∈ (ofAscArray decls p).decls.keys := by
        simpa using IndexMap.mem_iff_keys_contains.mp hmem
      rw [keys_ofAscArray] at hk
      obtain ⟨d, hd, hdn⟩ := Array.mem_map.mp hk
      exact Array.find?_eq_none.mp hf d hd (by simp [hdn])
    show (ofAscArray decls p).decls[name]? = none
    exact Option.not_isSome_iff_eq_none.mp (by
      rw [IndexMap.isSome_getElem?_eq_contains]; simpa using hnm)

/-- A view of an environment that keeps the declarations `pred` accepts.  `pred`
    receives the declaration's *position*, so a view can depend on declaration
    order (`before`). -/
structure SubEnv (α : Type) (β : Type) where
  decls : IndexMap Name (Decl.Raw α)
  pred : Nat → Decl.Raw α → Option β

namespace SubEnv

/-- What the view yields for `n`: its position and declaration must both exist,
    and `pred` must accept them. -/
@[expose]
def get? {α β} (s : SubEnv α β) (n : Name) : Option β := do
  s.pred (← s.decls.idxOf? n) (← s.decls[n]?)

end SubEnv

instance {α β} : Membership Name (SubEnv α β) where
  mem s n := (s.get? n).isSome

instance {α β} (nm : Name) (s : SubEnv α β) : Decidable (nm ∈ s) :=
  inferInstanceAs (Decidable ((s.get? nm).isSome = true))

instance {α β} : GetElem? (SubEnv α β) Name β (fun s n => n ∈ s) where
  getElem s n p := (s.get? n).get p
  getElem? s n := s.get? n

/-- Restrict a view to declarations at positions `< limit`.  `env.types.before i`
    is exactly the type declarations visible to the declaration at position `i`. -/
@[expose]
def SubEnv.before {α β} (s : SubEnv α β) (limit : Nat) : SubEnv α β :=
  { s with pred := fun i d => if i < limit then s.pred i d else none }

namespace SubEnv

variable {α β : Type}

/-! `simp` normalises `get?` to an `Option.bind` chain over the two lookups, the
position and the declaration. -/

@[simp] theorem get?_eq (s : SubEnv α β) (n : Name) :
    s.get? n = (s.decls.idxOf? n).bind (fun i => (s.decls[n]?).bind (s.pred i)) := rfl

@[simp] theorem getElem?_eq_get? (s : SubEnv α β) (n : Name) : s[n]? = s.get? n := rfl

@[simp] theorem mem_iff_isSome_get? {s : SubEnv α β} {n : Name} :
    n ∈ s ↔ (s.get? n).isSome := Iff.rfl

@[simp] theorem decls_before (s : SubEnv α β) (limit : Nat) :
    (s.before limit).decls = s.decls := rfl

-- Function-level: `pred` occurs partially applied inside `bind`.
@[simp] theorem pred_before (s : SubEnv α β) (limit : Nat) :
    (s.before limit).pred = fun i d => if i < limit then s.pred i d else none := rfl

theorem not_mem_iff_get?_eq_none {s : SubEnv α β} {n : Name} :
    ¬ n ∈ s ↔ s.get? n = none := by simp [Option.isNone_iff_eq_none]

/-- At a position in range, `before` agrees with the underlying view. -/
theorem get?_before_of_lt (s : SubEnv α β) {limit i : Nat} {n : Name}
    (h : s.decls.idxOf? n = some i) (hi : i < limit) :
    (s.before limit).get? n = s.get? n := by simp [h, hi]

/-- At a position out of range, `before` yields nothing. -/
theorem get?_before_of_le (s : SubEnv α β) {limit i : Nat} {n : Name}
    (h : s.decls.idxOf? n = some i) (hi : limit ≤ i) :
    (s.before limit).get? n = none := by
  simp [h, show ¬ i < limit from by omega]

/-- Nothing is visible before position `0`. -/
@[simp] theorem get?_before_zero (s : SubEnv α β) (n : Name) :
    (s.before 0).get? n = none := by simp

/-- Widening the limit keeps what the narrower view yielded. -/
theorem get?_before_mono (s : SubEnv α β) {a b : Nat} (hab : a ≤ b) {n : Name} {t : β}
    (h : (s.before a).get? n = some t) : (s.before b).get? n = some t := by
  cases hj : s.decls.idxOf? n with
  | none => simp [hj] at h
  | some j =>
    cases hd : s.decls[n]? with
    | none => simp [hj, hd] at h
    | some d => simp [hj, hd] at h ⊢; grind

theorem before_before (s : SubEnv α β) (a b : Nat) :
    (s.before a).before b = s.before (min a b) := by
  unfold before
  simp only [SubEnv.mk.injEq, true_and]
  funext i d
  grind

/-- A view whose `pred` ignores positions is a plain filtered lookup. -/
theorem get?_of_pred_const (s : SubEnv α β) (f : Decl.Raw α → Option β)
    (hf : ∀ i d, s.pred i d = f d) (n : Name) : s.get? n = (s.decls[n]?).bind f := by
  -- A key has a position exactly when it has a value, so the outer lookup never
  -- decides the result on its own; the mixed cases are impossible.
  have hidx := IndexMap.isSome_idxOf?_eq_contains (m := s.decls) (key := n)
  have hval := IndexMap.isSome_getElem?_eq_contains (m := s.decls) (key := n)
  cases hj : s.decls.idxOf? n with
  | none =>
    cases hd : s.decls[n]? with
    | none => simp [hj, hd]
    | some d => simp [hj, hd] at hidx hval; simp_all
  | some j =>
    cases hd : s.decls[n]? with
    | none => simp [hj, hd] at hidx hval; simp_all
    | some d => simp [hj, hd, hf]

end SubEnv

/-- What type a declaration denotes: itself for a primitive or a group head, and the member
it addresses for an alias. -/
@[expose]
def typeOfDecl? (env : Env.Raw α) : Decl.Raw α → Option (TypeDecl α)
| .type t => some t
| .dataHead g => some g.first.toTypeDecl
| .dataRest _ h i =>
  ((env.decls[h]?).bind Decl.Raw.asGroup).bind (fun g => (g.member? i).map (·.toTypeDecl))
| _ => none

/-- The type the name `n` denotes, if it denotes one. -/
@[expose]
def typeOf? (env : Env.Raw α) (n : Name) : Option (TypeDecl α) :=
  (env.decls[n]?).bind env.typeOfDecl?

/-- The datatype the name `n` is, if it is one: the group that carries it, and which member
of that group it is.  A head is member `0` of its own group; an alias is resolved through the
head it addresses. -/
@[expose]
def dataOf? (env : Env.Raw α) (n : Name) : Option (DataGroup α TypeExpr.Raw × Nat) :=
  match env.decls[n]? with
  | some (.dataHead g) => some (g, 0)
  | some (.dataRest _ h i) => ((env.decls[h]?).bind Decl.Raw.asGroup).map (fun g => (g, i))
  | _ => none

/-- Where the name `n` sits, if it names a constructor: its group's head, which datatype of
that group, and which constructor of that datatype. -/
@[expose]
def ctorAddr? (env : Env.Raw α) (n : Name) : Option CtorAddr :=
  match env.decls[n]? with
  | some (.insn d) => d.kind.ctor?
  | _ => none

@[expose]
def types (env : Env.Raw α) : SubEnv α (TypeDecl α) := ⟨env.decls, fun _ => env.typeOfDecl?⟩

@[expose]
def insns (env : Env.Raw α) : SubEnv α (InsnDecl.Raw α) :=
  ⟨env.decls, fun _ => Decl.Raw.asInsn⟩

@[simp] theorem get?_types (env : Env.Raw α) (n : Name) :
    env.types.get? n = (env.decls[n]?).bind env.typeOfDecl? :=
  SubEnv.get?_of_pred_const _ _ (fun _ _ => rfl) n

@[simp] theorem get?_insns (env : Env.Raw α) (n : Name) :
    env.insns.get? n = (env.decls[n]?).bind Decl.Raw.asInsn :=
  SubEnv.get?_of_pred_const _ _ (fun _ _ => rfl) n

@[simp] theorem decls_types (env : Env.Raw α) : env.types.decls = env.decls := rfl
@[simp] theorem pred_types (env : Env.Raw α) (i : Nat) (d : Decl.Raw α) :
    env.types.pred i d = env.typeOfDecl? d := rfl
@[simp] theorem decls_insns (env : Env.Raw α) : env.insns.decls = env.decls := rfl
@[simp] theorem pred_insns (env : Env.Raw α) (i : Nat) (d : Decl.Raw α) :
    env.insns.pred i d = d.asInsn := rfl

end Env.Raw

end

end Strata.Mantle
