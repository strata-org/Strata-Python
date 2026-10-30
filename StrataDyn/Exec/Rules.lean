/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public meta import StrataDyn.DSL.Model
public import StrataDyn.Exec.Sem

set_option autoImplicit false

/-!
# Semantic rules: registration

Three attributes, each with its own extension.  A key is the Lean name of a type or an
instruction, such as `Base.Int` or `Py.add`, resolved through the record its `environment`
command left.  An instruction's key is its own name, which its emitter shares, not its
reference `Py.add.ref`.  Registration rejects a key that the module, or a module it imports,
registers already.  Two modules that do not import each other may both register one key; a
module that imports both keeps the first and records the second (`Registry`), and
`@[dyn_sem]`, `#dyn_coverage`, `#dyn_types` and `#dyn_sem_table` report the pair as an error
(`checkNoDuplicates`).  Two modules that register one declaration for one key give one rule.

* `@[dyn_type T] d`: the Lean type `d` interprets the primitive or opaque Dyn type `T`.
  If `T` has `n` parameters, `d : Type → … → Type` takes `n`, or, for a type whose values may
  hold refs, `d : (σ : Type) → [Store σ] → Type → … → Type` takes the run token first.  A
  datatype usually takes no rule: `#dyn_types` generates its Lean type and registers it
  (`Exec/Types.lean`).  The base's `Unit` and `Except` are Lean's own, by hand-written rules:
  a datatype's rule must unfold to an inductive with its parameters, whose constructors match
  its own by name, count and field types, and `#dyn_types` then leaves it alone.  The engine
  interprets `base.Ref a` as `Ref σ ⟦a⟧` and `base.Fn as r` as `FnRef σ ⟦as⟧ ⟦r⟧`, and neither
  takes a rule.
* `@[dyn_lang] class L`: a language's capabilities, as one class that its rules take
  (below).
* `@[dyn_sem o] r`: the rule `r` gives the instruction `o` its meaning.  `r` is written at
  Lean types only, and its type must be, up to reducible unfolding,

  ```
  {σ : Type} → [Store σ] → [Decode σ] → {ε : Eff} → {E : Type} → {α₁ … αₘ : Type} →
    [capability]… → ⟦a₁⟧ → … → ⟦aₙ⟧ → [Array ⟦v⟧ → | Payload cs →]
    Region ε ⟦T₁⟧ ⟦C₁⟧ → … → Target E ⟦P₁⟧ → … → [Option S → Again E S →]
    Sem ε E ⟦R⟧
  ```

  with one type variable per type parameter of `o`, in order, a `Type` for a type and a
  `List Type` for a list, the variadic's array if `o` has one, or, for a spread over the list
  variable `cs`, the payload of its operands, one region per region, where `⟦Tᵢ⟧` lists the
  Lean types of region `i`'s parameters and `⟦Cᵢ⟧` is its result, one target per successor,
  where `⟦Pᵢ⟧` lists the Lean types of successor `i`'s payload, and, for a rule that loops, its
  state and its `Again`, at a Lean type `S` of the rule's choosing, which may mention its token
  and type variables.  The leading binders may come in any order.  A terminal instruction's rule
  returns `Sem ε E Empty`.
  * The token `σ` is needed only by a rule whose types mention a ref, `⟦base.Ref a⟧ = Ref σ ⟦a⟧`,
    or a closure, `⟦base.Fn as r⟧ = FnRef σ ⟦as⟧ ⟦r⟧`.
  * A list variable `cs` occurs only as the spread and spliced into the arguments of a
    closure operand, and its splice is the variable: `⟦Fn [*cs, a] r⟧` is
    `FnRef σ (cs ++ [⟦a⟧]) ⟦r⟧`, `⟦Fn [a, *cs] r⟧` is `FnRef σ (⟦a⟧ :: cs) ⟦r⟧`, and
    `⟦Fn [*cs] r⟧` is `FnRef σ cs ⟦r⟧`.  A rule over one takes `[TagsOf σ cs]` to reach cells
    or calls at its elements; `bindAll` binds a closure's leading arguments to a payload of
    them.
  * The capabilities, which the wrapper supplies, are: parts of the world, `HasPart ε.W P`; the
    machine's cells, `HasHeap σ ε`, through which the rule makes, reads, writes and updates
    cells (`newRef`, `readRef`, `writeRef`, `modifyRef`); its calls, `HasCall σ ε`, through
    which it calls and binds closures (`callFn`, `bindFn`, `bindAll`); and the tags those
    need, `TagOf σ α`, `SigOf σ as r`, `TagCon σ F`, `TagCon₂ σ F` and `TagsOf σ cs`, at Lean
    types of the instruction's environment.  A generic rule takes `[TagOf σ A]` only if it
    reaches a cell or a call at `A`.  A rule that takes a tag takes `[Decode σ]`, which the
    wrapper supplies with its table's decoding, so that every tag decodes by `rfl` at the
    wrapper's types.
  * A language's capabilities may come as one class instead, declared with `@[dyn_lang]`:
    each field a capability, or a parent language's class that it extends.  The attribute
    makes each field an instance, so a rule that takes the class, usually from a `variable`
    line, has each capability, and the wrapper builds the class field by field.  Its first
    parameter, the token, is an `outParam`, so that a part of the world, which does not mention
    the token, is found through it:

    ```
    @[dyn_lang] class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
      out : HasPart ε.W Output
      heap : HasHeap σ ε
      tagInt : TagOf σ Int
    variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [Lang σ ε]
    ```
  * Rules are trusted: a rule is what its instruction means, and registration checks its shape
    and types, not its meaning.  `implemented_by` and `@[extern]` in a rule are flags for
    review, as in Lean.

  An instruction without regions or successors may also take a pure rule,
  `{σ : Type} → [Store σ] → {α₁ … αₘ : Type} → ⟦a₁⟧ → … → ⟦R⟧`, with `σ` only if its types
  need it.

A mismatch is an error at the rule, naming the operand, region, target, state, `Again` or
result.
Constructors and case instructions are derived and take no rule, and `base.refNew`,
`base.refGet` and `base.refSet` are the machine's, on its heap, as is `base.callCode`, the call
of a closure.
-/

public meta section

namespace Strata.Dyn.Exec

open Lean Elab Meta
open Strata.Dyn.DSL (TypeInfo OpInfo OpKind EnvEntry DeclInfo findDecl? ancestry)

/-! ## Extensions -/

/-- A type rule. -/
structure TypeRule where
  /-- The Dyn type's Lean name, `Strata.Dyn.Base.Int`. -/
  key : Lean.Name
  decl : Lean.Name
  /-- For a datatype: the Lean constructor of each Dyn constructor, in Dyn's order. -/
  ctors : Array Lean.Name := #[]
  /-- Whether `decl` takes the run token first, `(σ : Type) → [Store σ] → …`. -/
  takesσ : Bool := false
  /-- Whether `#dyn_types` generated `decl`, a datatype's. -/
  generated : Bool := false
  deriving Inhabited, Repr

/-- A Lean type that a capability names, as a rule writes it: the rule's type variable `i`,
a ref, a code pointer, a type rule's constant applied to Lean types, or, in a type
constructor's capability, its `i`-th argument.  The wrapper gives it its tag in its table. -/
inductive LTy where
  | var (i : Nat)
  | hole (i : Nat)
  | ref (a : LTy)
  | fn (as : List LTy) (r : LTy)
  | con (decl : Lean.Name) (args : List LTy)
  deriving Inhabited, Repr, BEq

/-- What a leading, non-explicit binder of a rule is, in order, so that a wrapper can pass each
one positionally. -/
inductive Lead where
  /-- The run token `σ`. -/
  | sigma
  /-- `[Store σ]`. -/
  | store
  /-- `[Decode σ]`, which the wrapper supplies with its table's decoding. -/
  | decode
  /-- The requests `ε`. -/
  | eff
  /-- The exits `E`. -/
  | exits
  /-- The type variable of the instruction's `i`-th type parameter. -/
  | tyVar (i : Nat)
  /-- `[HasPart ε.W P]`, which instance search supplies. -/
  | part
  /-- `[HasHeap σ ε]`, the machine's cells. -/
  | heap
  /-- `[HasCall σ ε]`, the machine's calls. -/
  | call
  /-- `[TagOf σ t]`. -/
  | tag (t : LTy)
  /-- `[SigOf σ as r]`. -/
  | sig (as : List LTy) (r : LTy)
  /-- `[TagCon σ F]`, where `F X` is `t` with hole `0` for `X`. -/
  | tagCon (t : LTy)
  /-- `[TagCon₂ σ F]`, where `F X Y` is `t` with holes `0` and `1` for `X` and `Y`. -/
  | tagCon₂ (t : LTy)
  /-- `[TagsOf σ cs]`, the tags of the elements of `t`, a list-kinded type variable. -/
  | tags (t : LTy)
  /-- `[L σ ε]`, a language's capabilities in one class (`@[dyn_lang]`): the wrapper
  builds it field by field, each field a capability. -/
  | bundle (fields : Array (Lean.Name × Lead))
  deriving Inhabited, Repr

/-- A semantic rule. -/
structure SemRule where
  /-- The instruction's Lean name, `StrataPython.Dyn.Py.add`. -/
  key : Lean.Name
  decl : Lean.Name
  /-- Whether the rule returns its result directly, not in `Sem`. -/
  pure : Bool
  /-- The names of the rule's type variables, one per type parameter, in order. -/
  typeVars : Array Lean.Name := #[]
  /-- The leading, non-explicit binders, in order. -/
  leads : Array Lead := #[]
  /-- Whether the rule loops: it takes its state and its operation's `Again`, after its
  targets. -/
  again : Bool := false
  deriving Inhabited, Repr

/-- What a registry's extension holds: the entry for each key, and each key that two imported
modules both register, which import order would otherwise settle. -/
structure Registry (α : Type) where
  entries : Lean.NameMap α := {}
  /-- `(key, decl₁, decl₂)`: an imported module registers `decl₂` for `key`, which an earlier
  import registers `decl₁` for.  `entries` keeps `decl₁`. -/
  dups : Array (Lean.Name × Lean.Name × Lean.Name) := #[]
  deriving Inhabited

/-- The registry of the imported entries, `ess`, one array per module, by `key`, with `decl`
naming each entry's declaration.  Two modules that register one declaration for one key give
one entry. -/
def Registry.ofImports {α : Type} (key decl : α → Lean.Name) (ess : Array (Array α)) :
    Registry α :=
  ess.foldl (init := {}) fun r es => es.foldl (init := r) fun r e =>
    match r.entries.find? (key e) with
    | some e₁ =>
      if decl e₁ == decl e then r else { r with dups := r.dups.push (key e, decl e₁, decl e) }
    | none => { r with entries := r.entries.insert (key e) e }

initialize typeExt : SimplePersistentEnvExtension TypeRule (Registry TypeRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun r e => { r with entries := r.entries.insert e.key e }
    addImportedFn := Registry.ofImports (·.key) (·.decl) }

initialize semExt : SimplePersistentEnvExtension SemRule (Registry SemRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun r e => { r with entries := r.entries.insert e.key e }
    addImportedFn := Registry.ofImports (·.key) (·.decl) }

/-- The languages' classes, `@[dyn_lang]`: classes whose fields are capabilities, which a
rule takes whole. -/
initialize langExt : SimplePersistentEnvExtension Lean.Name Lean.NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun ess => ess.foldl (fun s es => es.foldl (fun s n => s.insert n) s) {} }

/-- The type rule for the type whose Lean name is `key`. -/
def findTypeRule? (env : Environment) (key : Lean.Name) : Option TypeRule :=
  (typeExt.getState env).entries.find? key

/-- The semantic rule for the instruction whose Lean name is `key`. -/
def findSemRule? (env : Environment) (key : Lean.Name) : Option SemRule :=
  (semExt.getState env).entries.find? key

/-- `d`, and the module that declares it if it is imported: `inc (in Foo.Rules)`. -/
def declWithModule (env : Environment) (d : Lean.Name) : MessageData :=
  match env.getModuleIdxFor? d >>= fun i => env.allImportedModuleNames[i.toNat]? with
  | some m => m!"{.ofConstName d} (in {m})"
  | none => m!"{.ofConstName d}"

/-- Fail if two imported modules register a type rule, or a rule, for a type or instruction of
the environment `ns` or one of its ancestors, naming both declarations. -/
def checkNoDuplicates (ns : Lean.Name) : CoreM Unit := do
  let env ← getEnv
  let mut names : Lean.NameMap Lean.Name := {}
  for e in ancestry env ns do
    for t in e.types do names := names.insert t.fullName t.envName
    for o in e.ops do names := names.insert o.fullName o.envName
  let mut lines : Array MessageData := #[]
  for (what, dups) in [("a type rule", (typeExt.getState env).dups),
      ("a rule", (semExt.getState env).dups)] do
    for (key, d₁, d₂) in dups do
      if let some n := names.find? key then
        lines := lines.push m!"two imported modules give {n.toString (escape := false)} \
          {what}: {declWithModule env d₁} and {declWithModule env d₂}"
  unless lines.isEmpty do
    throwError (MessageData.joinSep lines.toList "\n")

/-! ## Keys -/

/-- An environment name as a block writes it: `py.add`. -/
def showEnvName (n : Lean.Name) : String := n.toString (escape := false)

/-- The declaration the key `k` names: `Base.Int`, `Py.add`, `Base.Except.ok`. -/
def resolveKey (k : Ident) : CoreM (Lean.Name × DeclInfo) := do
  -- A private environment's names resolve in its own module.
  let c? ← withoutExporting <| try
      some <$> resolveGlobalConstNoOverload (mkIdentFrom k (k.getId ++ `name))
    catch _ => pure none
  let some c := c? |
    throwErrorAt k "unknown Dyn type or instruction `{k.getId}`"
  let full := (privateToUserName c).getPrefix
  match findDecl? (← getEnv) full with
  | some d => return (full, d)
  | none => throwErrorAt k "`{k.getId}` is not a type or instruction of an `environment`"

/-- The key a user writes for the declaration whose Lean name is `full`. -/
def refName (full : Lean.Name) : CoreM Lean.Name := do
  let env ← getEnv
  let c := full ++ `name
  let c := if env.contains c then c else mkPrivateName env c
  if env.contains c then return (← unresolveNameGlobal c).getPrefix
  return full

/-! ## Interpreting types -/

/-- A type the engine interprets, at every token. -/
inductive EngineType where
  /-- `base.Ref a`, a `Ref σ ⟦a⟧`. -/
  | ref
  /-- `base.Fn as r`, an `FnRef σ ⟦as⟧ ⟦r⟧`: a closure. -/
  | fn
  deriving BEq

/-- How the engine interprets the type, for a message. -/
def EngineType.show : EngineType → String
  | .ref => "Ref"
  | .fn => "FnRef"

/-- What the engine interprets `t` by, if it is `base.Ref` or `base.Fn`. -/
def engineType? (t : TypeInfo) : Option EngineType :=
  if t.fullName == `Strata.Dyn.Base.Ref then some .ref
  else if t.fullName == `Strata.Dyn.Base.Fn then some .fn
  else none

/-- Every type of the environment `ns` and its ancestors, by environment name. -/
def typesOf (env : Environment) (ns : Lean.Name) : Std.HashMap Lean.Name TypeInfo := Id.run do
  let mut m := {}
  for e in ancestry env ns do
    for t in e.types do m := m.insert t.envName t
  return m

/-- `Type → … → Type`, taking `n` types. -/
def typeArrows (n : Nat) : Expr :=
  n.fold (fun _ _ acc => .forallE `a (mkSort Level.one) acc .default) (mkSort Level.one)

/-- `(σ : Type) → [Store σ] → Type → … → Type`, a type at every token, taking `n` types. -/
def tokenArrows (n : Nat) : Expr :=
  .forallE `σ (mkSort Level.one)
    (.forallE `inst (mkApp (mkConst ``Store) (.bvar 0)) (typeArrows n) .instImplicit) .default

/-- The constant `d`, with its universe levels fixed so that its type is `typeArrows n`, or
`tokenArrows n` if `σ`, or `none` if it has no such type. -/
def typeConst? (d : Lean.Name) (n : Nat) (σ := false) : MetaM (Option Expr) := do
  let e ← mkConstWithFreshMVarLevels d
  unless ← isDefEq (← inferType e) (if σ then tokenArrows n else typeArrows n) do return none
  let .const _ lvls ← instantiateMVars e | return none
  -- A level the type does not fix is `0`.
  return some (mkConst d (lvls.map fun l => if l.hasMVar then Level.zero else l))

/-- The constant `d` of the type rule for `t`. -/
def ruleConst (t : TypeInfo) (r : TypeRule) : MetaM Expr := do
  let some e ← typeConst? r.decl t.params.size r.takesσ
    | throwError "the type rule {.ofConstName r.decl} of {showEnvName t.envName} \
        does not take {t.params.size} types"
  return e

/-- The type rule for `t` applied to the Lean types `as`, at the token `σ` if it takes one. -/
def ruleApp (t : TypeInfo) (r : TypeRule) (σ : Option Expr) (as : Array Expr) : MetaM Expr := do
  let c ← ruleConst t r
  unless r.takesσ do return mkAppN c as
  let some σ := σ | throwError "{showEnvName t.envName} needs the run token: a rule that \
      takes or makes one must be generic in it, \{σ : Type} [Store σ]"
  mkAppOptM' c (#[some σ, none] ++ as.map some)

/-- The Lean type constructor a type rule's constant `d` is, up to reducible unfolding: two
rules whose constants unfold to one constructor give one Lean type, and so one tag. -/
def canonDecl (d : Lean.Name) : MetaM Lean.Name := do
  let e ← whnfR (← mkConstWithFreshMVarLevels d)
  match e.getAppFn with
  | .const c _ => return c
  | _ => return d

/-- The type rules, by the Lean type constructor each is (`canonDecl`). -/
def rulesByDecl (env : Environment) : MetaM (Std.HashMap Lean.Name TypeRule) := do
  let mut m := {}
  for (_, r) in (typeExt.getState env).entries.toList do
    let c ← canonDecl r.decl
    unless m.contains c do m := m.insert c r
  return m

/-- What interpreting a type needs: the environment's types, and the Lean types of its type
variables. -/
structure InterpCtx where
  types : Std.HashMap Lean.Name TypeInfo
  vars : Array Expr
  /-- The kind of each type variable: a list variable's Lean type is a `List Type`. -/
  kinds : Array Kind := #[]
  /-- The token, if the rule is generic in one: a ref's or a closure's Lean type needs it. -/
  sigma : Option Expr := none

/-- The context for the environment `ns`, with the type variables `vars`. -/
def InterpCtx.ofEnv (env : Environment) (ns : Lean.Name) (vars : Array Expr) : InterpCtx :=
  { types := typesOf env ns, vars }

/-- The elements of the list `e`, a literal up to reducible unfolding. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e ← instantiateMVars e
  if let some (_, xs) := e.listLit? then return xs.toArray
  let e' ← whnfR e
  match_expr e' with
  | List.nil _ => return #[]
  | List.cons _ x rest => return #[x] ++ (← listElems rest)
  | _ => throwError "{e} is not a list literal"

mutual
/-- `⟦t⟧`, by the registered type rules. -/
partial def interpTy (cx : InterpCtx) : DSL.Ty → MetaM Expr
  | .var i => match cx.vars[i]? with
    | some x => return x
    | none => throwError "type variable {i} is out of scope"
  | .app h args => do
    let h := DSL.leanName h
    let some t := cx.types[h]? | throwError "unknown Dyn type {showEnvName h}"
    let needσ : MetaM Expr := match cx.sigma with
      | some σ => pure σ
      | none => throwError "{showEnvName h} needs the run token: a rule that takes or makes \
          one must be generic in it, \{σ : Type} [Store σ]"
    match engineType? t, args.toList with
    | some .ref, [a] => return ← mkAppM ``Ref #[← needσ, ← interpTy cx a]
    | some .fn, [.list es, r] =>
      return ← mkAppM ``FnRef #[← needσ, ← interpList cx es, ← interpTy cx r]
    | some _, _ => throwError "{showEnvName h} has the wrong arguments"
    | none, _ => pure ()
    let as ← args.mapM (interpTy cx)
    match findTypeRule? (← getEnv) t.fullName with
    | some r => ruleApp t r cx.sigma as
    | none =>
      if t.isData then
        throwError "no type rule for {showEnvName h}; its Lean type is generated by \
          #dyn_types for its environment"
      throwError "no type rule for {showEnvName h}; register one with \
          @[dyn_type {← refName t.fullName}]"
  | .list _ => throwError "a list of types has no Lean interpretation"

/-- `⟦es⟧`, the Lean types of a list literal, a `List Type`, with a list variable's splice as
the variable: `[*cs, a]` is `cs ++ [⟦a⟧]`, `[a, *cs]` is `⟦a⟧ :: cs`, and `[*cs]` is `cs`. -/
partial def interpList (cx : InterpCtx) (es : Array DSL.Ty) : MetaM Expr := do
  let splice? : DSL.Ty → Option Nat := fun
    | .var i => if cx.kinds[i]? == some .list then some i else none
    | _ => none
  let ty := mkSort Level.one
  match es.findIdx? (splice? · |>.isSome) with
  | none => mkListLit ty (← es.mapM (interpTy cx)).toList
  | some k =>
    let some i := es[k]? >>= splice? | throwError "a splice is out of range"
    let some v := cx.vars[i]? | throwError "type variable {i} is out of scope"
    let pre ← (es.extract 0 k).mapM (interpTy cx)
    let post ← (es.extract (k + 1) es.size).mapM (interpTy cx)
    let mid ← if post.isEmpty then pure v
      else mkAppM ``HAppend.hAppend #[v, ← mkListLit ty post.toList]
    pre.foldrM (fun a acc => mkAppM ``List.cons #[a, acc]) mid
end

/-- `⟦t⟧`, by the registered type rules. -/
def interpTyAll (cx : InterpCtx) (t : DSL.Ty) : MetaM Expr := interpTy cx t

/-- Whether `t` mentions a list variable, whose kinds `kinds` gives. -/
partial def mentionsList (kinds : Array Kind) : DSL.Ty → Bool
  | .var i => kinds[i]? == some .list
  | .app _ args => args.any (mentionsList kinds)
  | .list es => es.any (mentionsList kinds)

/-- Whether a rule can take an operand of type `t`: one that mentions no list variable, or a
closure whose result mentions none and whose arguments are types that mention none and splices
of list variables. -/
def listOperandOK (types : Std.HashMap Lean.Name TypeInfo) (kinds : Array Kind) (t : DSL.Ty) :
    Bool :=
  if !mentionsList kinds t then true else
  match t with
  | .app h #[.list es, r] =>
    (types[DSL.leanName h]?.bind engineType?) == some .fn && !mentionsList kinds r &&
      es.all fun
        | .var _ => true
        | e => !mentionsList kinds e
  | _ => false

/-- The Lean type `e`, which a capability names, as an `LTy`: over the rule's type variables
`vars` and a type constructor's arguments `holes`, and, after reducible unfolding, refs, code
pointers and the registered type rules' constructors. -/
partial def ltyOf (byDecl : Std.HashMap Lean.Name TypeRule) (vars holes : Array Expr)
    (e : Expr) : MetaM LTy := do
  let e ← instantiateMVars e
  if let some i := vars.idxOf? e then return .var i
  if let some i := holes.idxOf? e then return .hole i
  let e ← whnfR e
  if let some i := vars.idxOf? e then return .var i
  if let some i := holes.idxOf? e then return .hole i
  match e.getAppFnArgs with
  | (``Ref, #[_, _, a]) => return .ref (← ltyOf byDecl vars holes a)
  | (``FnRef, #[_, _, as, r]) =>
    return .fn (← (← listElems as).mapM (ltyOf byDecl vars holes)).toList
      (← ltyOf byDecl vars holes r)
  | _ =>
    let .const c _ := e.getAppFn |
      throwError "{e} is not a Lean type of a Dyn type: a capability names refs, code \
        pointers and the Lean types the type rules register"
    let some r := byDecl[c]? |
      throwError "{e} is the Lean type of no Dyn type: register its type with @[dyn_type]"
    let args := e.getAppArgs
    let args := if r.takesσ then args.extract 2 args.size else args
    return .con c (← args.mapM (ltyOf byDecl vars holes)).toList

/-- `n thing` or `n things`. -/
def plural (n : Nat) (thing : String) : String :=
  s!"{n} {thing}{if n == 1 then "" else "s"}"

/-- `⟦t⟧`, as a message: `⟦base.Int⟧`. -/
def showTy (vars : Array String) (t : DSL.Ty) : MessageData := m!"⟦{DSL.showTy vars t}⟧"

/-! ## `@[dyn_type]` -/

/-- The last component of an environment or Lean name. -/
def lastString : Lean.Name → String
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => ""

/-- Whether `t` mentions a ref or a code pointer, whose Lean types need the token. -/
partial def needsToken (types : Std.HashMap Lean.Name TypeInfo) : DSL.Ty → Bool
  | .var _ => false
  | .list es => es.any (needsToken types)
  | .app h args =>
    (types[DSL.leanName h]?.bind engineType?).isSome || args.any (needsToken types)

/-- Check that `decl` interprets the datatype `t`, declared in `entry`: applied to `t`'s
parameters, it unfolds to an inductive with those parameters, whose constructors match `t`'s by
name, count and field types.  Every field's type must have its rule already.  A hand-written
rule is for the base's `Unit` and `Except`, which are Lean's own, and none of its fields may hold
a ref or a closure, which need the token; `#dyn_types` generates every other datatype's Lean
type.  With `takesσ`, `decl` is a rule at every token, as `#dyn_types` generates for a
datatype that may hold a cell, and it is checked at a token of its own. -/
def checkDataRule (entry : EnvEntry) (t : TypeInfo) (decl : Lean.Name) (takesσ : Bool := false) :
    MetaM TypeRule := do
  let key := t.fullName
  let n := t.params.size
  let some e ← typeConst? decl n (σ := takesσ)
    | let want := if takesσ then m!"{tokenArrows n}" else if n == 0 then m!"Type" else
        m!"{typeArrows n}"
      throwError "the type rule for the datatype {showEnvName t.envName} must be a {want}, but \
        {.ofConstName decl} : {(← getConstInfo decl).type}"
  let names := t.params.map (·.1)
  let env ← getEnv
  -- A rule at every token is checked at a token `σ` of its own.
  let atToken {β : Type} (k : Array Expr → Option Expr → MetaM β) : MetaM β :=
    if takesσ then
      withLocalDeclD `σ (mkSort Level.one) fun σ => do
        withLocalDecl `inst .instImplicit (mkApp (mkConst ``Store) σ) fun inst =>
          k #[σ, inst] (some σ)
    else k #[] none
  atToken fun pre sigma? =>
  withLocalDeclsDND (names.map fun x => (Lean.Name.mkSimple x, mkSort Level.one)) fun αs => do
    let w ← whnf (mkAppN e (pre ++ αs))
    let notInd : MessageData := m!"{.ofConstName decl} does not unfold to an inductive type"
    let .const ind lvls := w.getAppFn | throwError notInd
    let .inductInfo iv ← getConstInfo ind | throwError notInd
    unless iv.numIndices == 0 && iv.numParams == pre.size + n && w.getAppArgs == pre ++ αs do
      throwError "{.ofConstName decl} must unfold to an inductive whose parameters are \
        {showEnvName t.envName}'s ({", ".intercalate names.toList}), in order, with no indices"
    let ctorOps := entry.ops.filter fun o => match o.kind with
      | .ctor d _ => d == t.envName
      | _ => false
    unless iv.ctors.length == ctorOps.size do
      throwError "{showEnvName t.envName} has {ctorOps.size} constructors, but \
        {.ofConstName ind} has {iv.ctors.length}"
    let cx := { InterpCtx.ofEnv env entry.leanNs αs with sigma := sigma? }
    let mut ctors := #[]
    for c in ctorOps do
      let short := lastString c.envName
      let some lc := iv.ctors.find? (lastString · == short)
        | throwError "{.ofConstName ind} has no constructor named {short}, for \
            {showEnvName c.envName}"
      let cty ← instantiateForall (← inferType (mkConst lc lvls)) w.getAppArgs
      forallTelescopeReducing cty fun xs _ => do
        unless xs.size == c.args.size do
          throwError "{.ofConstName lc} takes {plural xs.size "field"}, but \
            {showEnvName c.envName} declares {c.args.size}"
        for x in xs, (fname, fty) in c.args do
          if !takesσ && needsToken cx.types fty then
            throwError "field {fname} of {showEnvName c.envName} may hold a ref or a closure, \
              which a hand-written rule cannot interpret; leave {showEnvName t.envName} to \
              #dyn_types"
          let want ← interpTy cx fty
          let got ← inferType x
          unless ← isDefEq got want do
            throwError "field {fname} of {showEnvName c.envName}: {.ofConstName lc} has \
              {got}, but {showTy names fty} is {want}"
      ctors := ctors.push lc
    return { key, decl, ctors, takesσ }

/-- Check that `decl` interprets the type `t`, declared in `entry`.  A primitive or opaque
type's rule is a Lean type constructor of `t`'s parameters, `Type → … → Type`, or one at every
token, `(σ : Type) → [Store σ] → Type → … → Type`, for a type whose values may hold cells.  A
datatype's is checked by `checkDataRule`. -/
def checkTypeRule (entry : EnvEntry) (t : TypeInfo) (decl : Lean.Name) : MetaM TypeRule := do
  let key := t.fullName
  let n := t.params.size
  if t.params.any (·.2.2 == .list) then
    throwError "{showEnvName t.envName} takes a list of types, which no Lean type rule interprets"
  if t.isData then return ← checkDataRule entry t decl
  if (← typeConst? decl n).isSome then return { key, decl }
  if (← typeConst? decl n (σ := true)).isSome then return { key, decl, takesσ := true }
  let want := if n == 0 then m!"Type" else m!"{typeArrows n}"
  throwError "the type rule for {showEnvName t.envName} must be a {want}, or one at every \
    token, {tokenArrows n}, but {.ofConstName decl} : {(← getConstInfo decl).type}"

syntax (name := dyn_type) "dyn_type " ident : attr

initialize registerBuiltinAttribute {
  name := `dyn_type
  descr := "the Lean type that interprets a Dyn type"
  add := fun decl stx kind => do
    unless kind == .global do throwError "dyn_type must be global"
    let `(attr| dyn_type $k:ident) := stx | throwUnsupportedSyntax
    let (key, d) ← resolveKey k
    let .type entry t := d | throwErrorAt k "`{k.getId}` is an instruction, not a type"
    if let some c := engineType? t then
      throwError "the engine interprets {showEnvName t.envName} as {c.show}, and it \
        takes no type rule"
    if let some r := findTypeRule? (← getEnv) key then
      throwError "{showEnvName t.envName} already has the type rule {.ofConstName r.decl}"
    let r ← (checkTypeRule entry t decl).run'
    modifyEnv (typeExt.addEntry · r)
}

/-! ## `@[dyn_sem]` -/

/-- A handle's type as a check reports it: `Target [Int]`, `Region [] Bool`, `Again Int`,
without the exit type or requests. -/
def showHandle (t : Expr) : MessageData :=
  match t.getAppFnArgs with
  | (``Target, #[_, ts]) => m!"Target {ts}"
  | (``Again, #[_, S]) => if S.isApp then m!"Again ({S})" else m!"Again {S}"
  | (``Region, #[_, ts, a]) => m!"Region {ts} {a}"
  | _ => m!"{t}"

/-- The base instructions the machine implements: its heap's, and the call of a typed code
pointer. -/
def machineOps : List Lean.Name :=
  [`Strata.Dyn.Base.refNew, `Strata.Dyn.Base.refGet, `Strata.Dyn.Base.refSet,
   `Strata.Dyn.Base.callCode]

/-- Why `o` takes no rule, if it takes none. -/
def noRuleReason (o : OpInfo) : Option String :=
  match o.kind with
  | .ctor d _ => some s!"a constructor of {showEnvName d}, derived"
  | .case d => some s!"the case instruction of {showEnvName d}, derived"
  | .decl =>
    if machineOps.contains o.fullName then some "implemented by the machine" else none

/-- The capabilities a rule may take, as a message. -/
def capsMsg : MessageData :=
  m!"parts of the world, HasPart ε.W P, the machine's cells, HasHeap σ ε, its calls, \
    HasCall σ ε, and tags, TagOf σ α, SigOf σ as r, TagCon σ F, TagCon₂ σ F and TagsOf σ cs"

/-- The capability classes. -/
def capClasses : List Lean.Name :=
  [``HasPart, ``HasHeap, ``HasCall, ``TagOf, ``SigOf, ``TagCon, ``TagCon₂, ``TagsOf]

/-- What a capability the wrapper supplies is, if `ty` is one: a part of the world, the
machine's cells or calls, or a tag, at the token `sigma` and the requests `eff`, over the rule's
type variables `vars`. -/
def capOf? (byDecl : Std.HashMap Lean.Name TypeRule) (vars : Array Expr) (what : MessageData)
    (sigma : Option Expr) (eff : Expr) (ty : Expr) : MetaM (Option Lead) := do
  let atToken (σ : Expr) : MetaM Unit := unless some σ == sigma do
    throwError "{what} takes {ty}, which is not at its token"
  let atReqs (σ eff₁ : Expr) : MetaM Unit := do
    unless some σ == sigma && (← isDefEq eff₁ eff) do
      throwError "{what} takes {ty}, which is not at its token and its requests"
  match ty.getAppFnArgs with
  | (``HasPart, #[w, _]) =>
    unless ← isDefEq w (mkApp (mkConst ``Eff.W) eff) do
      throwError "{what} may require only {capsMsg}, but requires {ty}"
    return some .part
  | (``HasHeap, #[σ, _, _, eff₁]) => atReqs σ eff₁; return some .heap
  | (``HasCall, #[σ, _, _, eff₁]) => atReqs σ eff₁; return some .call
  | (``TagOf, #[σ, _, _, α]) => atToken σ; return some (.tag (← ltyOf byDecl vars #[] α))
  | (``SigOf, #[σ, _, _, as, r]) =>
    atToken σ
    let as ← (← listElems as).mapM (ltyOf byDecl vars #[])
    return some (.sig as.toList (← ltyOf byDecl vars #[] r))
  | (``TagCon, #[σ, _, _, F]) =>
    atToken σ
    withLocalDeclD `X (mkSort Level.one) fun x => do
      return some (.tagCon (← ltyOf byDecl vars #[x] (mkApp F x)))
  | (``TagsOf, #[σ, _, _, cs]) =>
    atToken σ
    let some i := vars.idxOf? (← instantiateMVars cs) |
      throwError "{what} takes {ty}, but TagsOf takes a list-kinded type variable"
    return some (.tags (.var i))
  | (``TagCon₂, #[σ, _, _, F]) =>
    atToken σ
    withLocalDeclD `X (mkSort Level.one) fun x => withLocalDeclD `Y (mkSort Level.one) fun y => do
      return some (.tagCon₂ (← ltyOf byDecl vars #[x, y] (mkApp2 F x y)))
  | _ => return none

/-- The fields of `x`, an instance of a language's class (`@[dyn_lang]`), as capabilities,
by their flattened names.  `none` if `x` is not one. -/
def bundleOf (byDecl : Std.HashMap Lean.Name TypeRule) (vars : Array Expr) (what : MessageData)
    (sigma : Option Expr) (eff : Expr) (x : Expr) : MetaM (Option (Array (Lean.Name × Lead))) := do
  let ty ← whnfR (← inferType x)
  let .const S _ := ty.getAppFn | return none
  let env ← getEnv
  unless isStructure env S && (langExt.getState env).contains S do return none
  let mut out := #[]
  for f in getStructureFieldsFlattened env S (includeSubobjectFields := false) do
    let e ← mkProjection x f
    let fty ← inferType e
    let some c ← capOf? byDecl vars m!"{what}'s field {f}" sigma eff fty |
      throwError "{what}'s field {f} : {fty} is not a capability: {capsMsg}"
    out := out.push (f, c)
  return some out

/-- Check that `decl` is a rule for the instruction `o`, given the type rules by declaration
(`rulesByDecl`) if the caller has them. -/
def checkSemRule (o : OpInfo) (decl : Lean.Name)
    (byDecl? : Option (Std.HashMap Lean.Name TypeRule) := none) : MetaM SemRule := do
  let key := o.fullName
  let opStr := showEnvName o.envName
  if let some why := noRuleReason o then
    throwError "{opStr} is {why}, and takes no rule"
  let vars := o.typeParams.map (·.1)
  let ty ← inferType (← mkConstWithFreshMVarLevels decl)
  let byDecl ← match byDecl? with
    | some m => pure m
    | none => rulesByDecl (← getEnv)
  forallTelescope ty fun xs body => do
    -- The leading non-explicit binders: requests, exits, type variables and capabilities.
    let nLead ← xs.findIdxM? fun x => return (← getFVarLocalDecl x).binderInfo.isExplicit
    let lead := xs.extract 0 (nLead.getD xs.size)
    let rest := xs.extract lead.size xs.size
    let sem? : Option (Expr × Expr) := match body.getAppFnArgs with
      | (``Sem, #[eff, e, _]) => some (eff, e)
      | _ => none
    if let some (eff, ex) := sem? then
      unless lead.contains eff && lead.contains ex do
        throwError "{.ofConstName decl} must be generic in its requests and exits: \
          {.ofConstName decl} \{ε : Eff} \{E : Type} … : Sem ε E …"
    let effEx : Array Expr := match sem? with
      | some (eff, ex) => #[eff, ex]
      | none => #[]
    -- The token: the one leading `Type` binder that a `[Store σ]` binder names.
    let mut sigmas : Array Expr := #[]
    for x in lead do
      let ld ← getFVarLocalDecl x
      if ld.binderInfo.isInstImplicit then
        if let (``Store, #[σ]) := ld.type.getAppFnArgs then
          unless lead.contains σ do
            throwError "{.ofConstName decl} takes {ld.type}, whose token it does not bind"
          unless sigmas.contains σ do sigmas := sigmas.push σ
    if sigmas.size > 1 then
      throwError "{.ofConstName decl} is generic in {sigmas.size} tokens, but a run has one"
    let sigma := sigmas[0]?
    let mut tyVars := #[]
    for x in lead do
      if effEx.contains x || some x == sigma then continue
      let ld ← getFVarLocalDecl x
      if ld.binderInfo.isInstImplicit then continue
      if (← isDefEq ld.type (mkSort Level.one)) ||
          (← isDefEq ld.type (mkApp (mkConst ``List [Level.one]) (mkSort Level.one))) then
        tyVars := tyVars.push x
      else
        throwError "{.ofConstName decl} takes the implicit {ld.userName} : {ld.type}, which is \
          neither a type variable, the token nor its requests"
    unless tyVars.size == vars.size do
      let ps := if vars.isEmpty then "" else s!" ({", ".intercalate vars.toList})"
      throwError "{opStr} has {plural vars.size "type parameter"}{ps}, but \
        {.ofConstName decl} binds {plural tyVars.size "type variable"}"
    let kinds := o.typeParams.map (·.2)
    let mut typeVars := #[]
    for x in tyVars, (p, k) in o.typeParams do
      let ld ← getFVarLocalDecl x
      if ld.userName.hasMacroScopes then
        throwError "{.ofConstName decl} must name its type variables"
      let isList ← isDefEq ld.type (mkApp (mkConst ``List [Level.one]) (mkSort Level.one))
      if isList != (k == .list) then
        let want := if k == .list then "a List Type" else "a Type"
        throwError "type parameter {p} of {opStr} is a {if k == .list then "list" else "type"}, so \
          {.ofConstName decl}'s {ld.userName} must be {want}"
      typeVars := typeVars.push ld.userName
    let cx : InterpCtx := { InterpCtx.ofEnv (← getEnv) o.owner tyVars with sigma, kinds }
    -- A list variable is the Lean type of a spread, and the arguments a closure takes.
    let listMsg : MessageData := m!"a list type variable may occur only in the arguments of a \
      closure operand, as a splice, and as the spread"
    for (x, t) in o.args do
      unless listOperandOK cx.types kinds t do
        throwError "operand {x} of {opStr}: {listMsg}"
    if let some t := o.ret then
      if mentionsList kinds t then throwError "the result of {opStr}: {listMsg}"
    for rd in o.regions do
      if mentionsList kinds rd.ret || rd.params.any (mentionsList kinds ·.2) then
        throwError "region {rd.name} of {opStr}: {listMsg}"
    for sd in o.succs do
      if sd.payload.any (mentionsList kinds) then
        throwError "successor {sd.name} of {opStr}: {listMsg}"
    -- Each leading binder's role, in order.
    let mut leads : Array Lead := #[]
    for x in lead do
      if some x == sigma then leads := leads.push .sigma; continue
      if let some (eff, ex) := sem? then
        if x == eff then leads := leads.push .eff; continue
        if x == ex then leads := leads.push .exits; continue
      if let some i := tyVars.idxOf? x then leads := leads.push (.tyVar i); continue
      let ld ← getFVarLocalDecl x
      match ld.type.getAppFnArgs with
      | (``Store, _) => leads := leads.push .store
      | (``Decode, #[σ, _]) =>
        unless some σ == sigma do
          throwError "{.ofConstName decl} takes {ld.type}, which is not at its token"
        leads := leads.push .decode
      | _ =>
        let some (eff, _) := sem? |
          throwError "{.ofConstName decl} takes {ld.type}, which a pure rule cannot"
        if let some c ← capOf? byDecl tyVars m!"{.ofConstName decl}" sigma eff ld.type then
          leads := leads.push c
        else if let some fs ← bundleOf byDecl tyVars m!"{.ofConstName decl}" sigma eff x then
          leads := leads.push (.bundle fs)
        else
          throwError "{.ofConstName decl} may require only {capsMsg}, but requires {ld.type}"
    let mut operands : Array (String × Expr) := #[]
    for (x, t) in o.args do
      operands := operands.push (s!"operand {x}", ← interpTyAll cx t)
    if let some (x, t) := o.variadic then
      match t with
      | .list es =>
        operands := operands.push (s!"spread {x}", ← mkAppM ``Payload #[← interpList cx es])
      | _ => operands := operands.push (s!"variadic {x}", ← mkAppM ``Array #[← interpTyAll cx t])
    let n := operands.size
    unless n ≤ rest.size && (sem?.isSome || rest.size == n) do
      throwError "{opStr} takes {plural n "operand"}, but {.ofConstName decl} takes {rest.size}"
    for x in rest, (what, want) in operands do
      let got ← inferType x
      unless ← withReducible (isDefEq got want) do
        throwError "{what} of {opStr}: expected {want}, but {.ofConstName decl} takes {got}"
    let res ← match o.ret with
      | some t => interpTyAll cx t
      | none => pure (mkConst ``Empty)
    -- The result as an argument of `Sem ε E`, in parentheses if it is an application.
    let resArg : MessageData := if res.isApp then m!"({res})" else m!"{res}"
    let simple := o.succs.isEmpty && o.regions.isEmpty && o.ret.isSome
    let some (eff, exitTy) := sem?
      | if simple && (← withReducible (isDefEq body res)) then
          return { key, decl, pure := true, typeVars, leads }
        let alt := if simple then m!"{res} or Sem ε E {resArg}" else m!"Sem ε E {resArg}"
        throwError "the result of {.ofConstName decl} is {body}, but {opStr} needs {alt}"
    let handles := rest.extract n rest.size
    let nr := o.regions.size
    unless nr ≤ handles.size do
      throwError "{opStr} has {plural nr "region"}, but {.ofConstName decl} takes \
        {handles.size} arguments after its operands"
    for x in handles, rd in o.regions do
      let ps ← rd.params.mapM (interpTyAll cx ·.2)
      let want ← mkAppM ``Region
        #[eff, ← mkListLit (mkSort Level.one) ps.toList, ← interpTyAll cx rd.ret]
      let got ← inferType x
      unless ← withReducible (isDefEq got want) do
        throwError "region {rd.name} of {opStr}: expected {showHandle want}, got \
          {showHandle got}"
    let afterRegions := handles.extract nr handles.size
    let isTarget (x : Expr) : MetaM Bool := return (← inferType x).isAppOf ``Target
    let targets := afterRegions.extract 0
      ((← afterRegions.findIdxM? fun x => return !(← isTarget x)).getD afterRegions.size)
    unless targets.size == o.succs.size do
      let names := ", ".intercalate (o.succs.toList.map ("^" ++ ·.name))
      let names := if names.isEmpty then "" else s!" ({names})"
      throwError "{opStr} has {plural o.succs.size "successor"}{names}, but \
        {.ofConstName decl} takes {plural targets.size "target"}"
    for l in targets, sd in o.succs do
      let ps ← sd.payload.mapM (interpTyAll cx)
      let want ← mkAppM ``Target #[exitTy, ← mkListLit (mkSort Level.one) ps.toList]
      let got ← inferType l
      unless ← withReducible (isDefEq got want) do
        throwError "target {sd.name} of {opStr}: expected {showHandle want}, got \
          {showHandle got}"
    -- The rule's state and its operation's `Again`, if the rule loops.
    let afterTargets := afterRegions.extract targets.size afterRegions.size
    let stateOf? (t : Expr) : Option Expr := match t.getAppFnArgs with
      | (``Option, #[S]) => some S
      | _ => none
    let again ← match afterTargets[0]?, afterTargets[1]? with
      | none, _ => pure false
      | some a, b? => do
        let got ← inferType a
        let some S := stateOf? got |
          if got.isAppOf ``Again then
            if let some b := b? then
              if (stateOf? (← inferType b)).isSome then
                throwError "{.ofConstName decl} takes its Again before its state: a rule that \
                  loops takes (st : Option σ), then its Again"
            throwError "{.ofConstName decl} takes {showHandle got} without its state: a rule \
              that loops takes (st : Option σ) before its Again"
          else
            throwError "{.ofConstName decl} takes {got} after its targets, but only its state \
              and its Again may follow them"
        let some b := b? |
          throwError "{.ofConstName decl} takes its state, {got}, but no Again after it"
        let gotA ← inferType b
        unless gotA.isAppOf ``Again do
          throwError "{.ofConstName decl} takes {gotA} after its state, but only its Again may \
            follow it"
        let want ← mkAppM ``Again #[exitTy, S]
        unless ← withReducible (isDefEq gotA want) do
          throwError "the Again of {opStr}: expected {showHandle want}, got {showHandle gotA}"
        -- The table instantiates the state at each token and type arguments.
        let allowed (v : FVarId) : MetaM Bool := do
          let x := Expr.fvar v
          if tyVars.contains x || some x == sigma then return true
          return (← getFVarLocalDecl x).type.isAppOf ``Store
        let S ← instantiateMVars S
        for v in (collectFVars {} S).fvarIds do
          unless ← allowed v do
            throwError "the state {S} of {.ofConstName decl} mentions \
              {(← getFVarLocalDecl (.fvar v)).userName}, but may mention only its token and \
              type variables"
        pure true
    if h : 2 < afterTargets.size then
      throwError "{.ofConstName decl} takes {← inferType afterTargets[2]} after its Again, but \
        nothing may follow it"
    unless ← withReducible (isDefEq body (← mkAppM ``Sem #[eff, exitTy, res])) do
      throwError "the result of {.ofConstName decl} is {body}, but {opStr} needs Sem ε E {resArg}"
    return { key, decl, pure := false, typeVars, leads, again }

syntax (name := dyn_lang) "dyn_lang" : attr

initialize registerBuiltinAttribute {
  name := `dyn_lang
  descr := "a language's capabilities, as one class, which a rule takes whole"
  add := fun decl _ kind => do
    unless kind == .global do throwError "dyn_lang must be global"
    let env ← getEnv
    unless isClass env decl && isStructure env decl do
      throwError "{.ofConstName decl} is not a class"
    -- Each field is an instance, so that a rule that takes the class finds its capabilities.
    for f in getStructureFields env decl do
      if let some parent := isSubobjectField? env decl f then
        unless (langExt.getState env).contains parent do
          throwError "{.ofConstName decl} extends {.ofConstName parent}, which is not a \
            language's class: declare it with @[dyn_lang]"
        continue
      let proj := decl ++ f
      let ok ← (do
        let ty ← inferType (← mkConstWithFreshMVarLevels proj)
        forallTelescope ty fun _ b => return capClasses.contains b.getAppFn.constName).run'
      unless ok do
        throwError "field {f} of {.ofConstName decl} is not a capability: {capsMsg}"
      setReducibilityStatus proj .reducible
      -- A tag's field does not name the requests, so its instance cannot fix them: it is
      -- found through the class's instance in scope, as a part of the world is.
      withOptions (synthInstance.checkSynthOrder.set · false) do
        (addInstance proj .global (eval_prio default)).run'
    modifyEnv (langExt.addEntry · decl)
}

syntax (name := dyn_sem) "dyn_sem " ident : attr

initialize registerBuiltinAttribute {
  name := `dyn_sem
  descr := "the Lean rule that gives a Dyn instruction its meaning"
  add := fun decl stx kind => do
    unless kind == .global do throwError "dyn_sem must be global"
    let `(attr| dyn_sem $k:ident) := stx | throwUnsupportedSyntax
    let (key, d) ← resolveKey k
    let .op _ o := d | throwErrorAt k "`{k.getId}` is a type, not an instruction"
    checkNoDuplicates o.owner
    if let some r := findSemRule? (← getEnv) key then
      throwError "{showEnvName o.envName} already has the rule {.ofConstName r.decl}"
    let r ← (checkSemRule o decl).run'
    modifyEnv (semExt.addEntry · r)
}

end Strata.Dyn.Exec

end
