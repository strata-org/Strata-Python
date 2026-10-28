/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env
public import StrataMantle.Env.TypeExprMatch
import StrataMantle.Env.WF
public meta import Lean.Elab.Term
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Util

set_option autoImplicit false

/-!
# Type arguments checked by kind

`KindedTypeArgs env scope ks` is a list of type arguments, one per kind of `ks`: a type for
`.type` and a list of types for `.list`.  The kinds are its index, so Lean checks the count and
each argument's kind where the arguments are written.  It is the builder's form of an
application's type arguments; `toTypeArgs` turns it into the IR's `TypeArgs`, an array with a
proof of its kinds, with no proof to write.

`KindedTypeArgsFor r type` is the `KindedTypeArgs` an application of the instruction `r` takes,
one per type parameter of its signature.  `type` is the application's result type, `none` for a
terminal instruction; it does not constrain the arguments, and is there for inference.

* `ta[e₁, e₂, …]` writes the arguments.  Each element is elaborated at its parameter's kind: a
  type, or a list of types, written `[t₁, t₂, …]` or given as a `TypeList`.
* `infer_type_args`, the builder's default, infers them from the result type, by matching the
  signature's result type against `type`.  A list literal in it may splice one list parameter
  among other elements: those match the caller's elements at either end, and the parameter
  binds the run between them.  For a `KindedTypeArgsFor` goal, parameters that do not occur in
  the result, those of a terminal instruction, and those of a literal that splices two lists,
  must be written with `ta[…]`; for the builder's `TypeArgsOf`, the first two are left to the
  builder (below), unless a parameter occurs in no operand's type either, which is an error
  when the code is compiled.
* `KindedTypeArgs.check?` checks arguments given as data, an array of `TypeArg`s.

The builder takes an application's type arguments as a `TypeArgsOf r type`: `given`, written
or inferred from the result type when the code is compiled, or `infer`, which `infer_type_args`
gives when the result type does not fix them all.  The builder then infers them when it runs,
with `InsnSig.inferTypeArgs?`, from the operands' types and the result type, by the matcher of
`Env/TypeExprMatch.lean`.  So `callCode`, whose argument list occurs only in its operands' types,
needs no `ta[…]`.

`ta[…]` and `infer_type_args` are scoped to `Strata.Mantle`, so `ta[` is a token only where
that namespace is open.  The builder's default argument is already parsed, so a caller outside
the namespace still gets inference.
-/

namespace Strata.Mantle

public section

/-- Type arguments in `scope`, one per kind of `ks`, each of its kind. -/
inductive KindedTypeArgs {α : Type} (env : Env α) (scope : Array Kind) : List Kind → Type
  | nil : KindedTypeArgs env scope []
  | ty {ks : List Kind} (t : TypeExpr env scope) (rest : KindedTypeArgs env scope ks) :
      KindedTypeArgs env scope (.type :: ks)
  | list {ks : List Kind} (l : TypeList env scope) (rest : KindedTypeArgs env scope ks) :
      KindedTypeArgs env scope (.list :: ks)

namespace KindedTypeArgs

variable {α : Type} {env : Env α} {scope : Array Kind}

/-- The arguments as a list, in order. -/
@[expose] def toList {ks : List Kind} : KindedTypeArgs env scope ks → List (TypeArg env scope)
  | .nil => []
  | .ty t rest => .ty t :: rest.toList
  | .list l rest => .list l :: rest.toList

/-- Each argument has its position's kind. -/
private theorem kinds_toList {ks : List Kind} :
    (l : KindedTypeArgs env scope ks) → l.toList.map TypeArg.kind = ks
  | .nil => rfl
  | .ty _ rest => by simp [toList, kinds_toList rest]
  | .list _ rest => by simp [toList, kinds_toList rest]

/-- The arguments in the IR's form, for the variables of `params`. -/
@[expose] def toTypeArgs {params : Array Kind} (l : KindedTypeArgs env scope params.toList) :
    TypeArgs env params scope :=
  ⟨l.toList.toArray, by simpa using kinds_toList l⟩

/-- A kind as error messages name it: `a type` or `a list of types`. -/
def kindText : Kind → String
  | .type => "a type"
  | .list => "a list of types"

/-- A kind error, as the builder words it. -/
def errorText : KindError → String
  | .count given expected => s!"{given} type argument(s) given, but it takes {expected}"
  | .kind i given expected =>
    s!"type argument {i + 1} is {kindText given}, but its parameter takes {kindText expected}"

/-- `args`, as arguments of their own kinds. -/
@[expose] def ofList : (args : List (TypeArg env scope)) →
    KindedTypeArgs env scope (args.map TypeArg.kind)
  | [] => .nil
  | ⟨.type, t⟩ :: as => .ty t (ofList as)
  | ⟨.list, l⟩ :: as => .list l (ofList as)

/-- The IR's type arguments, in the builder's form. -/
@[expose] def ofTypeArgs {params : Array Kind} (a : TypeArgs env params scope) :
    KindedTypeArgs env scope params.toList :=
  a.kinds ▸ ofList a.args.toList

/-- `ofList` keeps the arguments. -/
theorem toList_ofList : ∀ args : List (TypeArg env scope), (ofList args).toList = args
  | [] => rfl
  | ⟨.type, _⟩ :: as => by simp [ofList, toList, toList_ofList as]
  | ⟨.list, _⟩ :: as => by simp [ofList, toList, toList_ofList as]

/-- Casting along the kinds keeps the arguments. -/
private theorem toList_cast {ks₁ ks₂ : List Kind} (h : ks₁ = ks₂)
    (l : KindedTypeArgs env scope ks₁) : (h ▸ l).toList = l.toList := by
  subst h
  rfl

/-- `ofTypeArgs` keeps the arguments. -/
@[simp] theorem toTypeArgs_ofTypeArgs {params : Array Kind} (a : TypeArgs env params scope) :
    (ofTypeArgs a).toTypeArgs = a := by
  obtain ⟨args, h⟩ := a
  simp only [toTypeArgs, ofTypeArgs, toList_cast, toList_ofList, Array.toArray_toList]

/-- `args` as arguments for `ks`, or why they do not fit: for arguments given as data.  The one
check `TypeArgs.check?` decides the fit and gives the reason. -/
def check? (ks : List Kind) (args : Array (TypeArg env scope)) :
    Except String (KindedTypeArgs env scope ks) :=
  match TypeArgs.check? ks.toArray args with
  | .ok a => .ok (ofTypeArgs a)
  | .error e => .error (errorText e)

end KindedTypeArgs

/-- The type arguments of an application of `r` whose result has type `type`, `none` for a
terminal instruction.  `type` does not constrain them: it is there for `infer_type_args`. -/
@[expose, reducible] def KindedTypeArgsFor {α : Type} {env : Env α} {isig : InsnSig env}
    (_r : InsnRef env isig) (_type : Option (TypeExpr env)) : Type :=
  KindedTypeArgs env #[] isig.scope.toList

/-- An application's type arguments as the builder takes them: `given`, or `infer`, left for
the builder to infer from the operands' types and the result type when it runs. -/
inductive TypeArgsOf {α : Type} {env : Env α} {isig : InsnSig env} (r : InsnRef env isig)
    (type : Option (TypeExpr env)) where
  /-- Written with `ta[…]`, or inferred from the result type when the code is compiled. -/
  | given (args : KindedTypeArgsFor r type)
  /-- To infer when the builder runs. -/
  | infer

/-! ## Inference from the operands -/

/-- Why an application's type arguments could not be inferred. -/
inductive InferError where
  /-- The operands' or the result's types do not fit the signature at any arguments. -/
  | mismatch
  /-- A list in the signature splices these parameters, two or more, whose lengths nothing
  fixes. -/
  | ambiguous (params : List String)
  /-- These parameters occur in no operand's type and not in the result type. -/
  | missing (params : List String)
deriving DecidableEq, Repr

/-- `ps`, each in backquotes, separated by commas. -/
private def quoted (ps : List String) : String := ", ".intercalate (ps.map (s!"`{·}`"))

/-- The error, for an application of the instruction `who`. -/
def InferError.text (who : String) : InferError → String
  | .mismatch => s!"cannot infer the type arguments of {who}: the types of its operands and \
      result do not fit its signature"
  | .ambiguous ps => s!"cannot infer the type arguments of {who}: a list in its signature \
      splices {quoted ps}, whose lengths nothing fixes; pass them with `(typeArgs := ta[…])`"
  | .missing ps => s!"cannot infer type argument(s) {quoted ps} of {who}: they occur in no \
      operand's type and not in its result type; pass them with `(typeArgs := ta[…])`"

namespace InsnSig

variable {α : Type} {env : Env α}

/-- Each type of `isig` that the operands' types and the result type fix, with that type, in
the order inference solves them: the result type, then the operands', a spread's as one list.
`none` if there are too few or too many operands. -/
def inferPairs (isig : InsnSig env) (result? : Option (TypeExpr env))
    (operands : Array (TypeExpr env)) : Option (List (TypeExpr.Raw × TypeExpr.Raw)) :=
  let res := match isig.returnType, result? with
    | some p, some t => [(p.toRaw, t.toRaw)]
    | _, _ => []
  let fixed := isig.argTypes.size
  if operands.size < fixed then none
  else
    let args := (isig.argTypes.toList.zip operands.toList).map fun (p, t) =>
      (p.type.toRaw, t.toRaw)
    let rest := operands.toList.drop fixed
    match isig.variadic with
    | none => if rest.isEmpty then some (res ++ args) else none
    | some v =>
      match v.type.kind with
      | .type => some (res ++ args ++ rest.map fun t => (v.type.toRaw, t.toRaw))
      | .list => some (res ++ args ++ [(v.type.toRaw, .list ⟨rest.map (·.toRaw)⟩)])

/-- The type arguments that give an application of `isig` the operands' types `operands` and,
if given, the result type `result?`, or why there are none or several.  The arguments are
found by matching (`TypeExpr.Raw.matchAll`).  For any signature, arguments it finds are the
only ones on the parameters they fix, and otherwise it reports an ambiguity or that none exist
(`matchAll_complete`).  For a signature that splices at most one list per literal, as every
one the `environment` command declares does, it never reports an ambiguity
(`matchAll_complete_oneSplice`).  Each argument is then checked. -/
def inferTypeArgs? (isig : InsnSig env) (result? : Option (TypeExpr env))
    (operands : Array (TypeExpr env)) : Except InferError (TypeArgs env isig.scope) := do
  let some pts := isig.inferPairs result? operands | throw .mismatch
  let name (i : Nat) : String := (isig.typeParams[i]?.map (·.name)).getD "?"
  let σ ← (TypeExpr.Raw.matchAll isig.scope pts (.replicate isig.scope.size none)).mapError
    fun
    | .mismatch => .mismatch
    | .ambiguous vs => .ambiguous (vs.eraseDups.map name)
  let missing := (List.range σ.size).filter fun i => (σ[i]?.join).isNone
  unless missing.isEmpty do throw (.missing (missing.map name))
  let args ← σ.mapM fun
    | some x => match TypeArg.check? env #[] x with
      | some a => .ok a
      | none => .error .mismatch
    | none => .error .mismatch
  match TypeArgs.check? isig.scope args with
  | .ok a => pure a
  | .error _ => throw .mismatch

end InsnSig

end

/-! ## Elaboration -/

/-- `ta[e₁, e₂, …]`: the type arguments `e₁, e₂, …`, each of its parameter's kind. -/
scoped syntax (name := typeArgsLit) "ta[" withoutPosition(term,*,?) "]" : term

/-- `infer_type_args`: the type arguments of an application, inferred from its result type. -/
scoped syntax (name := inferTypeArgs) "infer_type_args" : tactic

public meta section

open Lean Elab Term Meta

namespace TypeArgElab

/-- The elements of a list literal, reducing it. -/
partial def listElems? (l : Expr) : MetaM (Option (List Expr)) := do
  let l ← whnf l
  match_expr l with
  | List.nil _ => return some []
  | List.cons _ x rest => return (← listElems? rest).map (x :: ·)
  | _ => return none

/-- The kinds of `ks`, a `List Kind` that reduces to a literal: `true` for a list. -/
def kindsOf? (ks : Expr) : MetaM (Option (List Bool)) := do
  let some es ← listElems? ks | return none
  let mut out := #[]
  for k in es do
    let k ← whnf k
    if k.isConstOf ``Kind.type then out := out.push false
    else if k.isConstOf ``Kind.list then out := out.push true
    else return none
  return some out.toList

/-- A kind, for an error message. -/
def kindText (isList : Bool) : String := if isList then "a list of types" else "a type"

/-- The kinds, for an error message: `[a type, a list of types]`. -/
def kindsText (ks : List Bool) : String := s!"[{", ".intercalate (ks.map kindText)}]"

/-- Elaborate `stx` against `expected`, failing rather than producing `sorry`. -/
def elabStrict (stx : Term) (expected : Expr) : TermElabM Expr :=
  withoutErrToSorry do
    let e ← elabTermEnsuringType stx expected
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

/-- Whether `stx` elaborates with `elab`, leaving no trace. -/
def elaboratesAs (act : TermElabM Expr) : TermElabM Bool := do
  let s ← saveState
  let ok ← try discard act; pure true catch _ => pure false
  s.restore
  return ok

/-- Who takes the arguments, for an error message. -/
def whoText (who? : Option Expr) : MessageData :=
  match who? with
  | some r => m!"{r}"
  | none => m!"the instruction"

/-- The argument `stx` at position `i` (from 0), of kind `isList`, in `env` and `scope`. -/
def elabArg (who? : Option Expr) (env scope : Expr) (i : Nat) (isList : Bool) (stx : Term) :
    TermElabM Expr := do
  let tyT ← mkAppM ``TypeExpr #[env, scope, mkConst ``Kind.type]
  let listT ← mkAppM ``TypeList #[env, scope]
  let wrong (given : Bool) : TermElabM Expr :=
    throwErrorAt stx m!"type argument {i + 1} of {whoText who?} is {kindText given}, but its \
      parameter takes {kindText isList}"
  let literal? : Option (Array Term) := match stx with
    | `([$ts,*]) => some ts.getElems
    | _ => none
  let s ← saveState
  if !isList then
    if literal?.isSome then return ← wrong true
    try elabStrict stx tyT
    catch ex =>
      s.restore
      if ← elaboratesAs (elabStrict stx listT) then wrong true else throw ex
  else if let some ts := literal? then
    -- The literal of the types, as a handle and a generated signature write it.
    let ts ← ts.mapM (elabStrict · tyT)
    let elemT ← mkAppOptM ``TypeList.Elem #[none, env, scope]
    let es ← ts.mapM fun t => mkAppOptM ``TypeList.Elem.ty #[none, env, scope, some t]
    mkAppOptM ``TypeList.lit #[none, env, scope, ← mkArrayLit elemT es.toList]
  else
    try elabStrict stx listT
    catch ex =>
      s.restore
      if ← elaboratesAs (elabStrict stx tyT) then wrong false else throw ex

/-- The chain of arguments `as`, of kinds `ks`. -/
def chain (env scope : Expr) : List (Bool × Expr) → MetaM Expr
  | [] => mkAppOptM ``KindedTypeArgs.nil #[none, env, scope]
  | (isList, a) :: rest => do
    let r ← chain env scope rest
    mkAppOptM (if isList then ``KindedTypeArgs.list else ``KindedTypeArgs.ty)
      #[none, env, scope, none, a, r]

/-- The expected type, unfolded to `KindedTypeArgs env scope ks`: `env`, `scope`, the kinds, and
the instruction if the type was `KindedTypeArgsFor r _`. -/
def expectedArgs (expected : Expr) :
    TermElabM (Expr × Expr × Option (List Bool) × Option Expr) := do
  let expected ← instantiateMVars expected
  let who? := match_expr expected with
    | KindedTypeArgsFor _ _ _ r _ => some r
    | _ => none
  let unfolded ← whnfR expected
  match_expr unfolded with
  | KindedTypeArgs _ env scope ks => return (env, scope, ← kindsOf? ks, who?)
  | _ => throwError "ta[…] builds type arguments, but {expected} is expected"

/-! ## Inference -/

/-- Bind variable `i` to `t`, or check it against an earlier binding. -/
def bindVar (i : Expr) (t : Expr) : StateT (Array (Option Expr)) MetaM Bool := do
  let some i ← (evalNat (← whnf i)).run | return false
  let bs ← get
  match bs[i]? with
  | some none => set (bs.setIfInBounds i (some t)); return true
  | some (some t₀) => isDefEq t t₀
  | none => return false

/-- The elements of a vector or array literal. -/
def vecElems? (v : Expr) : MetaM (Option (List Expr)) := do
  let ty ← whnfR (← inferType v)
  let arr ← if ty.isAppOf ``Vector then mkAppM ``Vector.toArray #[v] else pure v
  listElems? (← mkAppM ``Array.toList #[arr])

/-- `TypeList.ofTypes #[t₁, …]` as the literal it stands for, `TypeList.lit #[.ty t₁, …]`.
Unfolding `ofTypes` gives `lit (ts.map .ty)`, whose `Array.map` does not reduce. -/
def litOfTypes? (e : Expr) : MetaM (Option Expr) := do
  let_expr TypeList.ofTypes α env scope ts := e | return none
  let some xs ← vecElems? ts | return none
  let es ← xs.mapM fun x => mkAppOptM ``TypeList.Elem.ty #[α, env, scope, some x]
  let elemT ← mkAppOptM ``TypeList.Elem #[α, env, scope]
  return some (← mkAppOptM ``TypeList.lit #[α, env, scope, ← mkArrayLit elemT es])

/-- `e`, unfolded until its head is the constant `c`.  A `TypeList.ofTypes` unfolds to its
literal. -/
partial def unfoldTo (c : Lean.Name) (e : Expr) : MetaM (Option Expr) := do
  let e ← whnfCore e
  if e.getAppFn.isConstOf c then return some e
  if let .fvar x := e then
    if let some v ← x.getValue? then return ← unfoldTo c v
  if let some l ← litOfTypes? e then return ← unfoldTo c l
  match ← unfoldDefinition? e with
  | some e₁ => unfoldTo c e₁
  | none => return none

/-- `e`, for an error message: each proof it names is wrapped so that it prints as `⋯`, and a
message does not show the auxiliary lemmas a signature's proofs elaborate to. -/
def forMessage (e : Expr) : MetaM Expr :=
  transform e (post := fun x => do
    if x.isConst && (← isProof x) then return .done (← mkAppM ``id #[x])
    return .continue)

/-- The list variable `l` is, if it is one: `TypeList.var j`, or the literal `[*j]`. -/
def listVar? (l : Expr) : MetaM (Option Expr) := do
  match_expr l with
  | TypeList.var _ _ _ j _ => return some j
  | TypeList.lit _ _ _ es =>
    let some [e] ← vecElems? es | return none
    match_expr e with
    | TypeList.Elem.splice _ _ _ j _ => return some j
    | _ => return none
  | _ => return none

/-- The elements of `l`, if it reduces to a literal: `TypeList.lit`, `TypeList.var`, which is
`[*j]`, `TypeList.ofTypes`, whose elements are its types, and `l₁ ++ l₂` (`TypeExpr.append`)
of two of them, whose elements are theirs one after the other (`TypeExpr.lit_append_lit`), as an
abbreviation's handle builds its lists from a `TypeList` argument. -/
partial def litElems? (l : Expr) : MetaM (Option (List Expr)) := do
  let l ← whnfCore l.headBeta
  match_expr l with
  | TypeList.lit _ _ _ es => vecElems? es
  | TypeList.var α env scope j h =>
    return some [← mkAppOptM ``TypeList.Elem.splice #[α, env, scope, some j, some h]]
  | TypeList.ofTypes α env scope ts =>
    let some xs ← vecElems? ts | return none
    return some (← xs.mapM fun x => mkAppOptM ``TypeList.Elem.ty #[α, env, scope, some x])
  | TypeExpr.append _ _ _ a b => appended a b
  | HAppend.hAppend _ _ _ _ a b => appended a b
  | Append.append _ _ a b => appended a b
  | _ =>
    if let .fvar x := l then
      if let some v ← x.getValue? then return ← litElems? v
    match ← unfoldDefinition? l with
    | some l₁ => litElems? l₁
    | none => return none
where
  /-- The elements of `a`, then those of `b`. -/
  appended (a b : Expr) : MetaM (Option (List Expr)) := do
    let some xs ← litElems? a | return none
    let some ys ← litElems? b | return none
    return some (xs ++ ys)

/-- The list of the elements `es`, in the environment and scope of the list `l`: their literal,
as `ta[…]` and a handle write it. -/
def listOf (l : Expr) (es : List Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType l)
  let_expr TypeExpr α env scope _ := ty
    | throwError "infer_type_args: {l} is not a list of types"
  let elemT ← mkAppOptM ``TypeList.Elem #[α, env, scope]
  mkAppOptM ``TypeList.lit #[α, env, scope, ← mkArrayLit elemT es]

mutual

/-- Match the signature's type `pat` against the caller's `tgt`, binding the variables of
`pat` to parts of `tgt`.  A list variable binds the whole of the caller's list.  `who` names the
instruction, for the error a literal with two splices gives. -/
partial def matchTy (who : MessageData) (pat tgt : Expr) :
    StateT (Array (Option Expr)) MetaM Bool := do
  -- A handle in a hand-written signature unfolds, as abbreviations do, to its type's
  -- `Internal.T.ty`, which a generated signature writes.
  let pat ← whnfR pat
  let pat := (← litOfTypes? pat).getD pat
  if let some j ← listVar? pat then return ← bindVar j tgt
  if let some ok ← matchLit? who pat tgt then return ok
  match_expr pat with
  | TypeExpr.var _ _ _ i _ => bindVar i tgt
  | _ =>
    -- A hand-written signature carried into an extension: `carry` keeps the expression, so
    -- what is under it matches `tgt`, which is already in the extension.  The environment is an
    -- implicit argument of everything under it, which matching skips.
    if pat.isAppOf ``TypeExpr.carry then
      let some inner := pat.getAppArgs.back? | return false
      return ← matchTy who inner tgt
    let .const c _ := pat.getAppFn | return false
    let some tgt ← unfoldTo c tgt | return false
    let pargs := pat.getAppArgs
    let targs := tgt.getAppArgs
    if pargs.size ≠ targs.size then return false
    let info ← getFunInfoNArgs pat.getAppFn pargs.size
    for h : i in [:pargs.size] do
      let explicit := (info.paramInfo[i]?.map (·.binderInfo.isExplicit)).getD true
      let pa := pargs[i]
      let some ta := targs[i]? | return false
      if !explicit || (← isProof pa) then continue
      let paTy ← whnfR (← inferType pa)
      if paTy.isAppOf ``TypeExpr || paTy.isAppOf ``TypeList then
        unless ← matchTy who pa ta do return false
      else if paTy.isAppOf ``Vector || paTy.isAppOf ``Array then
        let (some ps, some ts) := (← vecElems? pa, ← vecElems? ta) | return false
        if ps.length ≠ ts.length then return false
        for (p, t) in ps.zip ts do
          unless ← matchTy who p t do return false
      else
        unless ← isDefEq pa ta do return false
    return true

/-- Match the literal `pat` against `tgt`, if `pat` is a literal: `none` if it is not.  The
elements before the literal's splice match the caller's first elements one by one, those after
it the caller's last, and the splice binds the run between them.  With no splice the literals
match element by element; with two the match is ambiguous, and an error. -/
partial def matchLit? (who : MessageData) (pat tgt : Expr) :
    StateT (Array (Option Expr)) MetaM (Option Bool) := do
  let_expr TypeList.lit _ _ _ es := pat | return none
  let some ps ← vecElems? es | return none
  let splices := ps.zipIdx.filterMap fun (p, i) => match_expr p with
    | TypeList.Elem.splice _ _ _ j _ => some (i, j)
    | _ => none
  if splices.length > 1 then
    throwError "cannot infer the type arguments of {who}: it is ambiguous, with more than one \
      splice in{indentExpr (← forMessage pat)}\npass them with `(typeArgs := ta[…])`"
  let some ts ← litElems? tgt | return some false
  let pairs (ps ts : List Expr) : StateT (Array (Option Expr)) MetaM Bool := do
    for (p, t) in ps.zip ts do
      unless ← matchTy who p t do return false
    return true
  match splices with
  | [] =>
    if ps.length ≠ ts.length then return some false
    return some (← pairs ps ts)
  | _ :: _ :: _ => return some false
  | [(k, j)] =>
    let m := ps.length - k - 1
    let n := ts.length
    if n < k + m then return some false
    unless ← pairs (ps.take k) (ts.take k) do return some false
    unless ← pairs (ps.drop (k + 1)) (ts.drop (n - m)) do return some false
    return some (← bindVar j (← listOf tgt ((ts.drop k).take (n - k - m))))

end

/-- The names of a signature's type parameters. -/
def paramNames (isig : Expr) : MetaM (List String) := do
  let some ps ← listElems? (← mkAppM ``Array.toList #[← mkAppM ``InsnSig.typeParams #[isig]])
    | return []
  ps.mapM fun p => do
    match ← whnf (← mkAppM ``Param.name #[p]) with
    | .lit (.strVal s) => return s
    | _ => return "?"

/-- What a signature's result type fixes of its type arguments. -/
private inductive ResultInfo where
  /-- The kinds of its type parameters do not reduce to a list. -/
  | unknownKinds
  /-- It fixes them all, as the arguments `args`. -/
  | fixes (args : Expr)
  /-- There is no result type to infer its `n` arguments from: the signature is `terminal`, or
  the goal gives none. -/
  | noResult (n : Nat) (terminal : Bool)
  /-- The result type `pat` leaves the parameters `unfixed` unfixed. -/
  | leaves (pat : Expr) (unfixed : List Nat)

/-- The application `r`, signature `isig` and result type `type` of the goal
`KindedTypeArgsFor r type`. -/
private def argsGoal (goal : Expr) : MetaM (Expr × Expr × Expr) := do
  let some parts := match_expr goal with
      | KindedTypeArgsFor _ _ isig r type => some (r, isig, type)
      | _ => none
    | throwError "infer_type_args: the goal is not the type arguments of an application"
  return parts

/-- What the result type fixes of the type arguments the goal `KindedTypeArgsFor r type` asks
for.  A result type that does not match, or is ambiguous, is an exception. -/
private def resultInfo (goal : Expr) : MetaM ResultInfo := do
  let goal ← instantiateMVars goal
  let (r, isig, type) ← argsGoal goal
  let unfolded ← whnfR goal
  let some (env, scope, ks) ← match_expr unfolded with
      | KindedTypeArgs _ env scope ks => pure (some (env, scope, ks))
      | _ => pure none
    | throwError "infer_type_args: the goal is not the type arguments of an application"
  let some kinds ← kindsOf? ks | return .unknownKinds
  if kinds.isEmpty then return .fixes (← chain env scope [])
  let ret ← whnf (← mkAppM ``InsnSig.returnType #[isig])
  let some pat := match_expr ret with
      | Option.some _ p => some p
      | _ => none
    | return .noResult kinds.length true
  let some tgt := match_expr (← whnf type) with
      | Option.some _ t => some t
      | _ => none
    | return .noResult kinds.length false
  let (ok, bs) ← (matchTy m!"{r}" pat tgt).run (Array.replicate kinds.length none)
  unless ok do
    throwError "cannot infer the type arguments of {r}: its result type\
      {indentExpr (← forMessage pat)}\ndoes not match{indentExpr (← forMessage tgt)}\n\
      pass them with `(typeArgs := ta[…])`"
  let unfixed := (List.range bs.size).filter fun i => (bs[i]?.join).isNone
  unless unfixed.isEmpty do return .leaves pat unfixed
  return .fixes (← chain env scope (kinds.zip (bs.toList.filterMap id)))

/-- The parameters the result type leaves unfixed: none if their kinds are unknown. -/
private def ResultInfo.unfixed : ResultInfo → List Nat
  | .unknownKinds | .fixes _ => []
  | .noResult n _ => List.range n
  | .leaves _ unfixed => unfixed

/-- Why the result type does not fix the type arguments of `r`, of the signature `isig`. -/
private def ResultInfo.explain (r isig : Expr) : ResultInfo → MetaM MessageData
  | .unknownKinds => return m!"cannot infer the type arguments of {r}: the kinds of its type \
      parameters do not reduce to a list; pass them with `(typeArgs := ta[…])`"
  | .fixes _ => return m!"the result type fixes the type arguments of {r}"
  | .noResult _ true => return m!"cannot infer the type arguments of {r}: it is terminal, with \
      no result type to infer them from; pass them with `(typeArgs := ta[…])`"
  | .noResult _ false => return m!"cannot infer the type arguments of {r}: no result type is \
      given; pass them with `(typeArgs := ta[…])`"
  | .leaves pat unfixed => do
    let names ← paramNames isig
    let missing := ", ".intercalate (unfixed.map fun i => s!"`{names.getD i "?"}`")
    return m!"cannot infer type argument(s) {missing} of {r}: they do not occur in its result \
      type{indentExpr (← forMessage pat)}\npass them with `(typeArgs := ta[…])`"

/-- Infer the type arguments the goal `KindedTypeArgsFor r type` asks for from the result type,
failing where it does not fix them all. -/
def inferArgs (goal : Expr) : MetaM Expr := do
  let (r, isig, _) ← argsGoal (← instantiateMVars goal)
  match ← resultInfo goal with
  | .fixes e => return e
  | info => throwError (← info.explain r isig)

/-- The variables the type expression or argument `e` mentions, if it reduces to variables,
applications and list literals: `none` if a part does not, such as a definition whose body is
not exposed. -/
partial def varsOf? (e : Expr) : MetaM (Option (List Nat)) := do
  let e ← whnfR e.headBeta
  let all (es : List Expr) : MetaM (Option (List Nat)) := do
    let mut out := []
    for x in es do
      let some vs ← varsOf? x | return none
      out := out ++ vs
    return some out
  match_expr e with
  | TypeExpr.var _ _ _ i _ => return (← (evalNat (← whnf i)).run).map ([·])
  | TypeList.Elem.splice _ _ _ j _ => return (← (evalNat (← whnf j)).run).map ([·])
  | TypeList.Elem.ty _ _ _ t => varsOf? t
  | TypeArg.mk _ _ _ _ v => varsOf? v
  | TypeExpr.app _ _ _ _ _ args _ =>
    let some xs ← vecElems? args | return none
    all xs
  | TypeExpr.appK _ _ _ _ _ args _ =>
    let some xs ← vecElems? args | return none
    all xs
  | _ =>
    if e.isAppOf ``TypeExpr.carry then
      let some inner := e.getAppArgs.back? | return none
      return ← varsOf? inner
    if let some es ← litElems? e then return ← all es
    match ← unfoldDefinition? e with
    | some e₁ => varsOf? e₁
    | none => return none

/-- The variables the operands' types of the signature `isig` mention, its variadic's
included, if each reduces (`varsOf?`). -/
def operandVars? (isig : Expr) : MetaM (Option (List Nat)) := do
  let some ps ← listElems? (← mkAppM ``Array.toList #[← mkAppM ``InsnSig.argTypes #[isig]])
    | return none
  let mut out := []
  for p in ps do
    let some vs ← varsOf? (← mkAppM ``Param.type #[p]) | return none
    out := out ++ vs
  match_expr ← whnf (← mkAppM ``InsnSig.variadic #[isig]) with
  | Option.none _ => return some out
  | Option.some _ p =>
    let some vs ← varsOf? (← mkAppM ``Param.type #[p]) | return none
    return some (out ++ vs)
  | _ => return none

/-- The type arguments a goal asks for: inferred from the result type for
`KindedTypeArgsFor r type`; for `TypeArgsOf r type`, `given` those, or `infer` where the result
type does not fix them all and the operands' types may.  A parameter that occurs in no
operand's type either, when those types reduce, is an error here, as the builder would report
it when it runs. -/
def inferGoal (goal : Expr) : MetaM Expr := do
  let goal ← instantiateMVars goal
  match_expr goal with
  | TypeArgsOf α env isig r type =>
    match ← resultInfo (← mkAppOptM ``KindedTypeArgsFor #[α, env, isig, r, type]) with
    | .fixes e => mkAppOptM ``TypeArgsOf.given #[α, env, isig, r, type, e]
    | info =>
      if let some ops ← operandVars? isig then
        let nowhere := info.unfixed.filter (!ops.contains ·)
        unless nowhere.isEmpty do
          let names ← paramNames isig
          let ps := ", ".intercalate (nowhere.map fun i => s!"`{names.getD i "?"}`")
          throwError "cannot infer type argument(s) {ps} of {r}: they occur in no operand's \
            type and not in its result type; pass them with `(typeArgs := ta[…])`"
      mkAppOptM ``TypeArgsOf.infer #[α, env, isig, r, type]
  | _ => inferArgs goal

end TypeArgElab

end

/-! ## The entry points

Public, as the attributes require; their signatures need only `Lean.Elab.Term` and
`Lean.Elab.Tactic.Basic`, so a module that imports this one does not load the rest of the
elaborator. -/

public meta section

open Lean Elab Term Meta TypeArgElab

namespace TypeArgElab

/-- `ta[…]` at the expected type `expected`, a `KindedTypeArgs`. -/
def elabKinded (stx : Syntax) (expected : Expr) : TermElabM Expr := do
  let `(ta[$es,*]) := stx | throwUnsupportedSyntax
  let (env, scope, ks?, who?) ← expectedArgs expected
  let some ks := ks? | do
    tryPostpone
    throwError "ta[…]: the kinds of {whoText who?}'s type parameters do not reduce to a \
      list; build the arguments with `KindedTypeArgs.check?`"
  let es := es.getElems
  if es.size ≠ ks.length then
    throwError "{whoText who?} takes {ks.length} type argument(s), {kindsText ks}, but \
      {es.size} are given"
  let as ← (ks.zip es.toList).zipIdx.mapM fun ((k, e), i) =>
    return (k, ← elabArg who? env scope i k e)
  chain env scope as

@[term_elab typeArgsLit] def elabTypeArgsLit : TermElab := fun stx expected? => do
  tryPostponeIfNoneOrMVar expected?
  let some expected := expected?
    | throwError "ta[…]: the type arguments' kinds are not known here"
  let expected ← instantiateMVars expected
  -- The builder's form: the arguments, given.
  match_expr expected with
  | TypeArgsOf α env isig r type =>
    let k ← elabKinded stx (← mkAppOptM ``KindedTypeArgsFor #[α, env, isig, r, type])
    mkAppOptM ``TypeArgsOf.given #[α, env, isig, r, type, k]
  | _ => elabKinded stx expected

@[tactic inferTypeArgs] def evalInferTypeArgs : Tactic.Tactic := fun _ =>
  Tactic.liftMetaTactic fun g => do
    let e ← inferGoal (← g.getType)
    unless ← isDefEq (← inferType e) (← g.getType) do
      throwError "infer_type_args: the inferred arguments{indentExpr e}\ndo not have the \
        goal's type"
    g.assign e
    return []

end TypeArgElab

end

end Strata.Mantle
