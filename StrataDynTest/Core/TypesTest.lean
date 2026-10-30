/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all StrataDyn.Core.Types
import all StrataDyn.Env
import StrataDyn.Base
import StrataDyn.DSL.Core
meta import StrataDyn.Base
meta import StrataDyn.Env.TypeExprElim
meta import Strata.DL.Lambda.LExprTypeEnv
meta import Strata.DL.Lambda.TypeFactory
meta import Strata.Languages.Core.Function
meta import Strata.Languages.Core.FunctionType
meta import Strata.Languages.Core.Factory
meta import Strata.Languages.Core.TypeDecl
import all Strata.Languages.Core.ProgramType

set_option autoImplicit false

/-! # Dyn type declarations compiled to Core

A primitive policy, the declarations it compiles to, `check` deciding their well-formedness,
total translation of closed, generic and instantiated types, and the rejections.
-/

namespace Strata.Dyn.CoreTypesTest

open Lambda CoreTypes

local instance {α : Type} [DecidableEq α] : BEq (Except Error α) where
  beq a b := match a, b with
    | .ok x, .ok y => decide (x = y)
    | .error x, .error y => decide (x = y)
    | _, _ => false

/-- The scope of a closed type, with no Core variables. -/
private def closedScope {K : Signature} : CoreTypes.Scope K (fun _ => False) #[] := Scope.closed

/-- The default Core context: Core's known types and factory, no datatypes, plus the opaque
`Closure` the test policies give function types, declared by the host like Core's `Sequence`. -/
private def coreContext : LContext Core.CoreLParams :=
  { LContext.default with
    knownTypes := Core.KnownTypes.insert "Closure" 0
    functions := Core.Factory }

/-- Whether `check` accepts the environment under the policy. -/
private def accepts (env : Env Unit) (policy : Policy) : Bool :=
  (checkEnv env policy coreContext).isOk

/-- The error `check` reports from a context, if any. -/
private def rejectionIn (C : LContext Core.CoreLParams) (env : Env Unit) (policy : Policy) :
    Option Error :=
  match checkEnv env policy C with
  | .error e => some e
  | .ok _ => none

/-- The error `check` reports, if any. -/
private def rejection (env : Env Unit) (policy : Policy) : Option Error :=
  rejectionIn coreContext env policy

private def isCoreRejection (env : Env Unit) (policy : Policy) (head : Name) : Bool :=
  match rejection env policy with
  | some (.coreDatatype n _) => n == head
  | _ => false

/-- The names of the Core declarations, groups by their first member. -/
private def declared (env : Env Unit) (policy : Policy) : List String :=
  (compile env policy).map (·.name.name)

/-! ## Policies

Concrete representations are total functions of the arguments at their kinds, under any
signature with the constructors they use. A function type is the one opaque constructor
`Closure`, its arguments ignored: a Dyn `Fn` value is a closure pointer, and calls are modelled
by the value lowering, not by Core's total `arrow`. -/

/-- A nullary Core constructor, whatever the primitive's arguments. -/
private def scalar {kinds : Array Kind} (name : String) : Concrete kinds :=
  { uses := [(name, 0)], apply := fun hK _ => Ty.app name [] (hK (name, 0) (by simp)) }

private def basePrimitives : Policy := fun d =>
  if d.name == bn "Int" then .concrete (scalar "int")
  else if d.name == bn "Bool" then .concrete (scalar "bool")
  else if d.kinds = #[.list, .type] then .concrete (scalar "Closure")
  else .nominal

private def pv (i : Nat) : LMonoTy := .ftvar (datatypeBinder i)
private def unitTy : LMonoTy := .tcons (typeName (bn "Unit")) []
private def exceptTy (e a : LMonoTy) : LMonoTy := .tcons (typeName (bn "Except")) [e, a]
private def refTy (a : LMonoTy) : LMonoTy := .tcons (typeName (bn "Ref")) [a]
private def closureTy : LMonoTy := .tcons "Closure" []

private def unitDecl : LDatatype Unit := {
  name := typeName (bn "Unit"), typeArgs := []
  constrs := [{
    name := ⟨constructorName (bn "unit"), ()⟩
    args := []
    testerName := testerName (bn "unit") }]
  constrs_ne := rfl
}

private def exceptDecl : LDatatype Unit := {
  name := typeName (bn "Except"), typeArgs := [datatypeBinder 0, datatypeBinder 1]
  constrs := [
    { name := ⟨constructorName (bn "ok"), ()⟩,
      args := [(⟨fieldName (bn "ok") "value", ()⟩, pv 1)],
      testerName := testerName (bn "ok") },
    { name := ⟨constructorName (bn "error"), ()⟩,
      args := [(⟨fieldName (bn "error") "err", ()⟩, pv 0)],
      testerName := testerName (bn "error") }]
  constrs_ne := rfl
}

-- One declaration per nominal type, in declaration order; concrete primitives declare nothing.
#guard compile base basePrimitives == [
  .data [unitDecl],
  .con { name := typeName (bn "Float64"), params := [] },
  .con { name := typeName (bn "String"), params := [] },
  .con { name := typeName (bn "Sequence"), params := ["a"] },
  .con { name := typeName (bn "Ref"), params := ["a"] },
  .data [exceptDecl],
  .con { name := typeName (bn "Loc"), params := [] }]

-- The base is supported in Core's default context; the final context knows the declarations.
#guard accepts base basePrimitives
#guard match checkEnv base basePrimitives coreContext with
  | .ok ⟨C, _⟩ => C.knownTypes[typeName (bn "Ref")]? == some 1 &&
      C.knownTypes[typeName (bn "Except")]? == some 2 && C.datatypes.size == 2
  | .error _ => false

/-! ## Translation -/

/-- A closed type of the base, as a Core type. -/
private def closed (t : TypeExpr base) : LMonoTy :=
  (translateType basePrimitives (fun _ _ h => h) closedScope t).val

#guard closed Base.Int == .int
#guard closed Base.Bool == .bool
#guard closed Base.Unit == unitTy
#guard closed (Base.Ref Base.Int) == refTy .int
#guard closed (Base.Except Base.Unit (Base.Except Base.Int Base.Bool)) ==
  exceptTy unitTy (exceptTy .int .bool)
#guard closed (Base.Fn [Base.Int, Base.Bool] Base.Unit) == closureTy
-- Not `int`: a nullary function is still a closure to call.
#guard closed (Base.Fn [] Base.Int) == closureTy

/-- The Core function type of a signature: its arguments to its result, quantified once over
the signature's type parameters; `none` for a terminal instruction. -/
private def signatureType (sig : InsnSig base) : Except Error (Option LTy) := do
  let ⟨names, s⟩ ← Scope.generic (K := signature base basePrimitives) sig.typeParams
    (sig.distinct.sublist (by simp only [List.append_assoc]; exact List.sublist_append_left _ _))
  let args := sig.argTypes.toList.map fun p =>
    (translateType basePrimitives (fun _ _ h => h) s p.type).val
  return sig.returnType.map fun ret =>
    .forAll names.val
      (LMonoTy.mkArrow' (translateType basePrimitives (fun _ _ h => h) s ret).val args)

private def a : LMonoTy := .ftvar (binderName "a")

#guard signatureType (Base.refNew.sig (e := base)) ==
  .ok (some (.forAll [binderName "a"] (.arrow a (refTy a))))
#guard signatureType (Base.refSet.sig (e := base)) ==
  .ok (some (.forAll [binderName "a"] (.arrow (refTy a) (.arrow a unitTy))))
#guard signatureType (Base.branch.sig (e := base)) == .ok none
-- A list parameter has no Core binder.
#guard signatureType (Base.callCode.sig (e := base)) == .error (.listBinder 0 "as")

/-- `refGet`'s return type at Core arguments, checked against the compiled context. -/
private def refGetAt (args : List ((k : Kind) × Translated k)) : Except Error (Option LMonoTy) := do
  let ⟨C, _⟩ ← checkEnv base basePrimitives coreContext
  let sig := Base.refGet.sig (e := base)
  let s ← Scope.ofArguments (K := contextSignature C) (V := fun _ => False) sig.scope args
  let s := s.mono (K' := fun n a => signature base basePrimitives n a ∨ contextSignature C n a)
    (fun _ _ h => Or.inr h) (fun _ h => h)
  return sig.returnType.map fun ret =>
    (translateType basePrimitives (fun _ _ h => Or.inl h) s ret).val

#guard refGetAt [⟨.type, .int⟩] == .ok (some .int)
#guard refGetAt [⟨.type, refTy .bool⟩] == .ok (some (refTy .bool))
#guard refGetAt [] == .error (.parameterCount 0 1)
#guard refGetAt [⟨.type, .int⟩, ⟨.type, .int⟩] == .error (.parameterCount 2 1)
#guard refGetAt [⟨.list, []⟩] == .error (.parameterKind 0 .list .type)
-- A consumer's type must be well formed in the context.
#guard refGetAt [⟨.type, .tcons "Nowhere" []⟩] == .error (.illFormed (.tcons "Nowhere" []))
#guard refGetAt [⟨.type, .ftvar "x"⟩] == .error (.illFormed (.ftvar "x"))

/-! ## Datatypes with fields, recursion and mutual groups -/

private environment Shapes extends Base where
  namespace shapes
  open base
  data Pair (+a) (+b) where
    | pair (left : a) (right : b) (unit : Unit)
  data Choice (+a) where
    | first (value : Except Int a)
    | second (value : Pair a Bool)
  data Recursive (+a) where
    | stop
    | step (next : Recursive a)
  mutual
    data Even where
      | zero
      | succE (pred : Odd)
    data Odd where
      | succO (pred : Even)
  end
  data Through where
    | through (value : Ref Int)
  data Reserved («$__ty0») («$__rigid_x») («$__elimty») where
    | reserved (x : «$__ty0») (y : «$__rigid_x») (z : «$__elimty»)
  end shapes

private def sn (s : String) : Name := .str (.str .base "shapes") s

#guard accepts Shapes.env basePrimitives
-- An extension adds its declarations after the base's, in order, one per group.
#guard declared Shapes.env basePrimitives == declared base basePrimitives ++
  [typeName (sn "Pair"), typeName (sn "Choice"), typeName (sn "Recursive"), typeName (sn "Even"),
   typeName (sn "Through"), typeName (sn "Reserved")]

-- Signatures stay generic, in order, with constructor-qualified fields; a mutual group is one
-- Core block.
#guard match ((compile Shapes.env basePrimitives)[7]? : Option Core.TypeDecl),
    ((compile Shapes.env basePrimitives)[8]? : Option Core.TypeDecl),
    ((compile Shapes.env basePrimitives)[10]? : Option Core.TypeDecl) with
  | some (.data [pair]), some (.data [choice]), some (.data [even, odd]) =>
    pair.typeArgs == [datatypeBinder 0, datatypeBinder 1] &&
    pair.constrs.map (·.args.map Prod.snd) == [[pv 0, pv 1, unitTy]] &&
    choice.typeArgs == [datatypeBinder 0] &&
    choice.constrs.map (·.args.map Prod.snd) ==
      [[exceptTy .int (pv 0)], [.tcons (typeName (sn "Pair")) [pv 0, .bool]]] &&
    choice.constrs.flatMap (·.args.map (·.1.name)) ==
      [fieldName (sn "first") "value", fieldName (sn "second") "value"] &&
    even.name == typeName (sn "Even") && odd.name == typeName (sn "Odd")
  | _, _, _ => false

#guard (translateType basePrimitives (fun _ _ h => h) closedScope
  (Shapes.Choice Base.Unit : TypeExpr Shapes.env)).val == .tcons (typeName (sn "Choice")) [unitTy]

-- Dyn identities that a dotted printer conflates remain distinct Core identities.
#guard typeName (.num .base 1) != typeName (.str .base "1")
#guard typeName (.str (.str .base "x") "y") != typeName (.str .base "x.y")
#guard constructorName (bn "ok") != testerName (bn "ok")
#guard fieldName (sn "first") "value" != fieldName (sn "second") "value"

-- Core names are readable: the Dyn name's segments, with marks inside a segment escaped.
#guard typeName (bn "Except") == "$dyn.type.base.Except"
#guard fieldName (bn "ok") "value" == "$dyn.field.base.ok.value"
#guard constructorName (.num (bn "f") 3) == "$dyn.ctor.base.f#3"
#guard typeName (.str .base "a.b") == "$dyn.type.a'.b"

/-! ## Generated functions typecheck

For these fixtures, `check`'s acceptance agrees with the typechecking of every generated
datatype function. -/

private def contextFor (decls : List Core.TypeDecl) : Except Strata.Message Core.Expression.TyContext := do
  let mut ctx : Core.Expression.TyContext := coreContext
  for decl in decls do
    match decl with
    | .data block =>
      ctx ← ctx.addMutualBlock block
      let functions ← genBlockFactory (T := Core.CoreLParams) block
      for f in functions.toArray do
        let _ ← Core.Function.typeCheck ctx Lambda.TEnv.default f.toFunc
          |>.mapError Strata.Message.fromFormat
    | .con d =>
      ctx ← ctx.addKnownTypeWithError { name := d.name, metadata := d.numargs }
        (Strata.Message.fromFormat "Duplicate type constructor")
    | .syn _ => throw <| Strata.Message.fromFormat "Unexpected type synonym"
  return ctx

#guard accepts base basePrimitives == (contextFor (compile base basePrimitives)).isOk
#guard accepts Shapes.env basePrimitives == (contextFor (compile Shapes.env basePrimitives)).isOk
#guard !(contextFor [.data [exceptDecl], .data [exceptDecl]]).isOk

/-- The context `check` returns is Core's own: it holds the same functions as the context
Core's checks build, the generated datatype functions included. -/
private def sameFunctions (env : Env Unit) (policy : Policy) : Bool :=
  match checkEnv env policy coreContext, contextFor (compile env policy) with
  | .ok ⟨C, _⟩, .ok C' =>
    C.functions.toArray.map (·.name.name) == C'.functions.toArray.map (·.name.name)
  | _, _ => false
#guard sameFunctions base basePrimitives
#guard sameFunctions Shapes.env basePrimitives

/-! ### Names next to Core's generated ones

Core names its generated functions by suffixing: a field's unsafe selector is its selector's
name and `!`, a datatype's eliminator is the datatype's name and `$Elim`. Escaping `!` and `$`
inside a segment keeps a Dyn name from spelling another name's suffixed form. -/

-- A constructor with fields `x` and `x!`, and datatypes `T` and `T$Elim`.
private environment Suffixed extends Base where
  namespace suffixed
  open base
  data T where
    | mk (x : Int) («x!» : Int)
  data «T$Elim» where
    | elim (t : T)
  end suffixed
#guard accepts Suffixed.env basePrimitives
#guard accepts Suffixed.env basePrimitives ==
  (contextFor (compile Suffixed.env basePrimitives)).isOk
#guard fieldName (bn "c") "x!" == "$dyn.field.base.c.x'!"
#guard typeName (bn "T$Elim") == "$dyn.type.base.T'$Elim"

/-! ### Members that cannot share binders

Core requires every member to declare the same parameter set, even when no field uses it.
The oracle below sees the block that provisional binders would have produced. -/

/-- The blocks `compile` would emit under provisional binders. -/
private def provisionalBlocks (env : Env Unit) (policy : Policy) : List (MutualDatatype Unit) :=
  env.entries.toList.flatMap fun
    | .data g => (blockWithBinders policy g (provisionalBinders g)).toList
    | _ => []

/-- Isolate unequal parameter sets from duplicate, reserved or unscoped variables. -/
private def coreRejectsParameters (env : Env Unit) (policy : Policy) : Bool :=
  match provisionalBlocks env policy with
  | [block] =>
    (checkTypeParamsNodup block).isOk && (checkTypeParamsNotReserved block).isOk &&
    (checkConstructorArgVarsScoped block).isOk && !(checkTypeParamsAgree block).isOk &&
    !(coreContext.addMutualBlock block).isOk
  | _ => false

-- Unrelated members: each field uses a parameter the other member does not bind.
private environment Unrelated where
  namespace unrelated
  mutual
    data A (+a) where
      | mkA (x : a)
    data B (+b) where
      | mkB (y : b)
  end
  end unrelated
#guard rejection Unrelated.env uninterpreted ==
  some (.unsharedBinders (.str (.str .base "unrelated") "A"))
#guard coreRejectsParameters Unrelated.env uninterpreted

-- A member binding a subset of the parameters a field of another member uses.
private environment Subset where
  namespace subset
  mutual
    data A (+a) where
      | stopA
      | mkA (v : a) (n : B)
    data B where
      | stopB
  end
  end subset
#guard rejection Subset.env uninterpreted ==
  some (.unsharedBinders (.str (.str .base "subset") "A"))
#guard coreRejectsParameters Subset.env uninterpreted

-- An unused parameter still belongs to the set every member must declare. The accepted twin
-- is Custom below, where Phantom and Ground are in separate groups.
private environment PhantomMismatch where
  namespace custom
  mutual
    data Phantom (+a) where
      | phantom
    data Ground where
      | ground
  end
  end custom
#guard rejection PhantomMismatch.env uninterpreted ==
  some (.unsharedBinders (.str (.str .base "custom") "Phantom"))
#guard compile PhantomMismatch.env uninterpreted == []
#guard coreRejectsParameters PhantomMismatch.env uninterpreted

-- Equal arities do not suffice when the alignment leaves distinct unused binders.
private environment UnrelatedPhantoms where
  namespace unrelatedPhantoms
  mutual
    data A (+a) where
      | mkA
    data B (+b) where
      | mkB
  end
  end unrelatedPhantoms
#guard rejection UnrelatedPhantoms.env uninterpreted ==
  some (.unsharedBinders (.str (.str .base "unrelatedPhantoms") "A"))
#guard compile UnrelatedPhantoms.env uninterpreted == []
#guard coreRejectsParameters UnrelatedPhantoms.env uninterpreted

-- Without the mutual block, both phantom parameters are allowed.
private environment SeparatePhantoms where
  namespace unrelatedPhantoms
  data A (+a) where
    | mkA
  data B (+b) where
    | mkB
  end unrelatedPhantoms
#guard accepts SeparatePhantoms.env uninterpreted
#guard accepts SeparatePhantoms.env uninterpreted ==
  (contextFor (compile SeparatePhantoms.env uninterpreted)).isOk

-- The twin whose members share the binder through a recursive application is accepted.
private environment Shared where
  namespace shared
  mutual
    data A (+a) where
      | mkA (x : a) (n : B a)
    data B (+b) where
      | mkB (y : b)
  end
  end shared
#guard accepts Shared.env uninterpreted
#guard accepts Shared.env uninterpreted ==
  (contextFor (compile Shared.env uninterpreted)).isOk

/-! ## Primitive representations -/

private environment Custom where
  namespace custom
  type Token
  type Bag (+a)
  type Erase (+a)
  type Function (as : list) (+r)
  data Node (+a) where
    | leaf (value : a)
    | link (next : Node a)
  data Handler (a) where
    | handler (run : Function [Token, a] a)
  mutual
    data Tree (+a) where
      | tree (value : a) (children : Forest a)
    data Forest (+element) where
      | nil
      | cons (head : Tree element) (tail : Forest element)
  end
  mutual
    data Left (+a) (+b) where
      | leftNil
      | leftStep (value : a) (next : Right b a)
    data Right (+c) (+d) where
      | rightNil
      | rightStep (value : c) (next : Left d c)
  end
  data Phantom (+a) where
    | phantom
  data Ground where
    | ground
  end custom

private def cn (s : String) : Name := .str (.str .base "custom") s

/-- `Bag a` as Core `Sequence a`. -/
private def bag : Concrete #[.type] :=
  { uses := [("Sequence", 1)]
    apply := fun hK args => Ty.app "Sequence" [args.get ⟨0, by decide⟩] (hK ("Sequence", 1) (by simp)) }

private def customPrimitives : Policy := fun d =>
  if d.name == cn "Token" then .concrete (scalar "int")
  else if d.name == cn "Erase" then .concrete (scalar "bool")
  else if h : d.name = cn "Bag" ∧ d.kinds = #[.type] then .concrete (h.2 ▸ bag)
  else if d.kinds = #[.list, .type] then .concrete (scalar "Closure")
  else .nominal

private def custom (t : TypeExpr Custom.env) : LMonoTy :=
  (translateType customPrimitives (fun _ _ h => h) closedScope t).val

#guard custom Custom.Token == .int
#guard custom (Custom.Bag Custom.Token) == .tcons "Sequence" [.int]
#guard custom (Custom.Erase Custom.Ground) == .bool
#guard custom (Custom.Function [Custom.Token, Custom.Bag Custom.Token] Custom.Token) == closureTy
#guard accepts Custom.env customPrimitives
#guard declared Custom.env customPrimitives ==
  [typeName (cn "Node"), typeName (cn "Handler"), typeName (cn "Tree"), typeName (cn "Left"),
   typeName (cn "Phantom"), typeName (cn "Ground")]
#guard accepts Custom.env customPrimitives ==
  (contextFor (compile Custom.env customPrimitives)).isOk

-- Binders are shared across a group, also when the members permute them.
#guard match ((compile Custom.env customPrimitives)[2]? : Option Core.TypeDecl),
    ((compile Custom.env customPrimitives)[3]? : Option Core.TypeDecl) with
  | some (.data [tree, forest]), some (.data [left, right]) =>
    tree.typeArgs == [datatypeBinder 0] && forest.typeArgs == [datatypeBinder 0] &&
    left.typeArgs == [datatypeBinder 0, datatypeBinder 1] &&
    right.typeArgs == [datatypeBinder 1, datatypeBinder 0]
  | _, _ => false

-- Uninterpreted, every primitive without a list parameter is a Core type constructor.
#guard compile (Env.empty.addType { ann := (), name := cn "Token" } (by simp) (by decide))
    uninterpreted ==
  [.con { name := typeName (cn "Token"), params := [] }]

-- An instantiation of two list parameters splices repeatedly without losing boundaries or order.
private def repeatedList : TypeList Custom.env #[.list, .list] :=
  TypeList.lit #[.splice 0 (by rfl), .ty Custom.Token, .splice 1 (by rfl), .splice 0 (by rfl)]

#guard (do
  let ⟨C, _⟩ ← checkEnv Custom.env customPrimitives coreContext
  let s ← Scope.ofArguments (K := contextSignature C) (V := fun _ => False) #[.list, .list]
    [⟨.list, [.bool]⟩, ⟨.list, [.int, .bool]⟩]
  let s := s.mono
    (K' := fun n a => signature Custom.env customPrimitives n a ∨ contextSignature C n a)
    (fun _ _ h => Or.inr h) (fun _ h => h)
  return (translate customPrimitives (fun _ _ h => Or.inl h) s repeatedList : List (Ty _ _)).map
    Subtype.val) ==
  .ok [LMonoTy.bool, .int, .int, .bool, .bool]

-- Environment annotations do not participate in representation choices.
private def annotatedDecl : TypeDecl Nat := { ann := 8, name := .str .base "Word" }
private def annotatedEnv : Env Nat := Env.empty.addType annotatedDecl (by simp) (by decide)
private def annotatedRef (ann : Nat) : TypeRef annotatedEnv 0 :=
  let r := TypeRef.ofAddType Env.empty annotatedDecl (by simp)
  { r with decl := { annotatedDecl with ann }, matchArity := rfl, resolves := r.resolves }
private def annotatedType : TypeExpr annotatedEnv :=
  .app (annotatedRef 8) #v[] (TypeRef.kinds_zero _)

-- Even a reference with different metadata must select the same representation, for every policy.
example (policy : Policy) (a b : Nat) :
    representation policy (annotatedRef a) =
      representation policy (annotatedRef b) := rfl

#guard (translateType uninterpreted (fun _ _ h => h)
    closedScope annotatedType).val == .tcons (typeName annotatedDecl.name) []
#guard (checkEnv annotatedEnv uninterpreted coreContext).isOk

/-! ## Rejections

`check` fails at the first declaration without a well-formed Core form, naming it. -/

-- A nominal primitive with a list parameter has no fixed-arity Core constructor.
#guard rejection base uninterpreted ==
  some (.listParameter (bn "Fn"))

-- Checked again from the context it returned, a declaration's Core name is taken.
private def tokenEnv : Env Unit :=
  Env.empty.addType { ann := (), name := cn "Token" } (by simp) (by decide)
#guard match checkEnv tokenEnv uninterpreted coreContext with
  | .ok ⟨C, _⟩ => rejectionIn C tokenEnv uninterpreted == some (.duplicateType (cn "Token"))
  | .error _ => false

private environment EmptyData extends Base where
  namespace empty
  data Nothing where
  end empty
#guard rejection EmptyData.env basePrimitives ==
  some (.emptyDatatype (.str (.str .base "empty") "Nothing"))
private environment NullaryData extends Base where
  namespace nullary
  data Nothing where
    | nothing
  end nullary
#guard accepts NullaryData.env basePrimitives
#guard accepts NullaryData.env basePrimitives ==
  (contextFor (compile NullaryData.env basePrimitives)).isOk

private environment PackedData extends Base where
  namespace packed
  data Packed (as : list) where
    | pack
  end packed
#guard rejection PackedData.env basePrimitives ==
  some (.listParameter (.str (.str .base "packed") "Packed"))
private environment UnpackedData extends Base where
  namespace unpacked
  data Packed (+a) where
    | pack
  end unpacked
#guard accepts UnpackedData.env basePrimitives
#guard accepts UnpackedData.env basePrimitives ==
  (contextFor (compile UnpackedData.env basePrimitives)).isOk

-- Core forbids recursion nested under another constructor: `Nested a` under `Except`. The
-- nullary constructor keeps Core's inhabitance check out of the way, here and below.
private environment NestedData extends Base where
  namespace nested
  open base
  data Nested (+a) where
    | nestStop
    | nest (child : Except Int (Nested a))
  end nested
#guard isCoreRejection NestedData.env basePrimitives
  (.str (.str .base "nested") "Nested")
-- The twin with the `Except` beside the recursion instead of around it is accepted.
private environment BesideData extends Base where
  namespace beside
  open base
  data Beside (+a) where
    | besideStop
    | beside (child : Except Int a) (next : Beside a)
  end beside
#guard accepts BesideData.env basePrimitives
#guard accepts BesideData.env basePrimitives ==
  (contextFor (compile BesideData.env basePrimitives)).isOk

-- Through a concrete representation, the same nesting: `Bag Wrapped` is `Sequence Wrapped`.
private environment WrappedData extends Custom where
  namespace wrapped
  open custom
  data Wrapped where
    | wrappedStop
    | wrapped (children : Bag Wrapped)
  end wrapped
#guard isCoreRejection WrappedData.env customPrimitives
  (.str (.str .base "wrapped") "Wrapped")
-- Erasing the argument instead makes it a plain constant field.
private def erasingBag : Policy := fun d =>
  if d.name == cn "Bag" then .concrete (scalar "int") else customPrimitives d
#guard accepts WrappedData.env erasingBag
#guard accepts WrappedData.env erasingBag == (contextFor (compile WrappedData.env erasingBag)).isOk

-- Core requires uniform recursion: `BadRec (Bag a)` applies the datatype to a type other than
-- its own parameter. The uniform twin is `Shapes.Recursive`, accepted above.
private environment UniformData extends Custom where
  namespace uniform
  open custom
  data BadRec (+a) where
    | badStop
    | badRec (next : BadRec (Bag a))
  end uniform
#guard isCoreRejection UniformData.env customPrimitives
  (.str (.str .base "uniform") "BadRec")

-- Core requires inhabited datatypes: every constructor of `Forever` recurses.
private environment InhabitedData extends Custom where
  namespace inhabited
  data Forever where
    | forever (next : Forever)
  end inhabited
#guard isCoreRejection InhabitedData.env customPrimitives
  (.str (.str .base "inhabited") "Forever")
-- The twin with a terminating constructor is accepted.
private environment EndingData extends Custom where
  namespace ending
  data Ending where
    | endingStop
    | ending (next : Ending)
  end ending
#guard accepts EndingData.env customPrimitives
#guard accepts EndingData.env customPrimitives ==
  (contextFor (compile EndingData.env customPrimitives)).isOk

-- A representation that puts the argument to the left of an arrow is not strictly positive.
private environment NegativeData extends Custom where
  namespace negative
  open custom
  data Negative where
    | negativeStop
    | negativeStep (next : Bag Negative)
  end negative
private def negativeBag : Concrete #[.type] :=
  { uses := [("arrow", 2), ("int", 0)]
    apply := fun hK args =>
      Ty.app "arrow" [args.get ⟨0, by decide⟩, Ty.app "int" [] (hK ("int", 0) (by simp))]
        (hK ("arrow", 2) (by simp)) }
private def negativePrimitives : Policy := fun d =>
  if h : d.name = cn "Bag" ∧ d.kinds = #[.type] then .concrete (h.2 ▸ negativeBag)
  else customPrimitives d
#guard isCoreRejection NegativeData.env negativePrimitives
  (.str (.str .base "negative") "Negative")
-- As a `Sequence`, the same shape is positive but nested, which Core refuses as for `Wrapped`;
-- erasing the argument makes it a plain constant field.
#guard isCoreRejection NegativeData.env customPrimitives
  (.str (.str .base "negative") "Negative")
#guard accepts NegativeData.env erasingBag
#guard accepts NegativeData.env erasingBag ==
  (contextFor (compile NegativeData.env erasingBag)).isOk

-- A concrete representation may only use constructors the context knows.
private def unknownBag : Concrete #[.type] :=
  { uses := [("Nowhere", 1)]
    apply := fun hK args => Ty.app "Nowhere" [args.get ⟨0, by decide⟩] (hK ("Nowhere", 1) (by simp)) }
#guard rejection Custom.env (fun d =>
    if h : d.name = cn "Bag" ∧ d.kinds = #[.type] then .concrete (h.2 ▸ unknownBag)
    else customPrimitives d) ==
  some (.unknownType (cn "Bag") "Nowhere" 1)

end Strata.Dyn.CoreTypesTest
