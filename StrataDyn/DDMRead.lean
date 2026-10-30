/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDyn.DDM
public import StrataDyn.Build
public import StrataDyn.WF
public import StrataDyn.Util.NameTable
public import StrataDyn.DomDiag
-- Private: reading builds checked IR, which needs the environment representation at codegen.
import StrataDyn.Env.WF
import StrataDyn.FloatText
import StrataDDM.Elab
import Lean.Parser.Extension
import Std.Data.HashMap
import Std.Data.HashSet

open StrataDDM

set_option autoImplicit false

/-!
# Reading printed IR back

`Module.read env text` parses `text` in the Dyn dialect of `StrataDyn/DDM.lean` and
returns the well-formed `Module` it denotes in `env`, annotated with `Info` (source ranges,
and each function's attributes), or diagnostics that say what is wrong and where.  It reads
both printed forms.  `Module.ofDDM` does the same from a DDM term.

* Lines that start with `--` are comments.
* A function's attributes are read into its `Info`, each key once; a function or a ghost they
  name must be in the module.
* Types and operations are looked up in `env`.  A list parameter's argument, of a type or of
  an operation, is a list literal `[τ, …]` of types, and an argument of the wrong kind is
  rejected.  `jump`, `branch` and
  `unreachable` are the base's, and `ret(args)` is a jump to `Label.exit`.
* A literal has the type its form fixes, which must be the type where it is used.  A function
  reference `@m.f` has the type where it is used, which must be `m.f`'s code type, read from
  its header.
* A constant written at a use becomes a `const` instruction just before it.
* Values get ids in the order of `Func.defs`: an extern's parameters, the body's values in
  printed order, then the contract's.  So the function read is canonical (`Func.Canonical`).
* The reader checks each function against `Func.WF` as it finishes it.  When its body, or a
  clause or frame region entered where only the parameters are visible, is not reachable and
  scoped, the reader names each block that the entry does not reach and each use out of scope
  (`Func.scopeDiagnostics`, `Region.scopeDiagnostics`).
* A contract clause or frame region uses only the function's parameters and its own values, and
  the body uses none of the contract's.  A contract region applies no operation declared
  `writes`, at any depth.  The clauses come in order: `requires`, `ensures`, then at most one
  `reads` and one `writes` frame, each naming distinct cells among the parameters, and frame
  regions, which take no arguments and return a `base.Loc`.
* An `extern func` has a signature and a contract, and no body.  Its `ensures` clauses are all
  `free`, and a defined function's are all checked.  The grammar has `free` only before
  `ensures`.
* A failure successor in a clause's own blocks goes to a failure block, which returns the
  clause's failure value, `false`, or `true` in a `free ensures` clause, or ends in
  `unreachable`.  One in a frame region's own blocks goes to a block that ends in `unreachable`.
  One in a region nested in a contract region goes to a block that ends in `unreachable` or, if
  the region may propagate, passes the failure on with `base.error`.  Every block of a contract
  region ends in control flow, and the blocks of a contract region have no cycle.  The reader
  names the first failure successor, block or cycle that breaks these rules.
* Only an `ensures` clause applies `base.old`, and an `old` region uses, from outside it, only
  the function's parameters, the clause's constants and the parameters of the regions that
  enclose it.  The reader names the first `base.old`, or the first use, that breaks these rules.
* A module's ghosts come before its functions.  No two ghosts share a name, and no ghost has the
  name of a function.  A ghost's initializer takes no arguments and returns the ghost's type, and
  its invariant takes the ghost's contents and returns a `base.Bool`.  Each uses only its own
  values, and follows the rules for a frame region.  A ghost's values get ids from `0`, the
  initializer's first, in the order of `Ghost.defs`.
* A ghost constant `ghost @m.g` names a ghost of the module, at the type of its cell, a
  `base.Ref` of the ghost's type.  Only a contract region names one, an initializer names only
  the ghosts declared before its own, and an invariant names none.  A ghost's regions refer to no
  function.  An attribute may name a ghost of the module too.

A name reads back as printed unless one of its string segments is empty, is all digits or
contains `.`.  A name spelled like one of the dialect's keywords is written pipe-delimited:
`module |ret| {`.
-/

namespace Strata.Dyn

/-- A problem found reading a module, and the source range it is about. -/
public structure ReadDiagnostic where
  range : SourceRange
  message : String

namespace Read

open DDM

/-! ## Names, literals and types -/

/-- The name a printed identifier denotes: dotted segments, all-digit ones numeric. -/
def nameOf (s : String) : Name :=
  if s == "_" then .base
  else
    (s.splitOn ".").foldl (init := .base) fun pre seg =>
      match if seg.all Char.isDigit then seg.toNat? else none with
      | some i => .num pre i
      | none => .str pre seg

/-- An identifier's text, for a message. -/
def identText (n : MName SourceRange) : String :=
  match n with
  | .name _ ⟨_, s⟩ => s

/-- A type, printed for a message. -/
def typeText {env : Env Unit} {scope : Array Kind} (e : TypeExpr env scope) : String :=
  e.fold (fun | i, .type => s!"#{i}" | i, .list => s!"*#{i}")
    (fun n as =>
      if as.isEmpty then ToDDM.nameText n
      else s!"{ToDDM.nameText n}({", ".intercalate as.toList})")
    -- `[*#i]` is the list variable `*#i`, as the printer shows it.
    (fun es => match es with
      | #[v] => if v.startsWith "*" then v else s!"[{v}]"
      | _ => s!"[{", ".intercalate es.toList}]")

/-- Types, printed for a message. -/
def typesText {env : Env Unit} (ts : Array (TypeExpr env)) : String :=
  s!"({", ".intercalate (ts.map typeText).toList})"

/-- What reading fails with. -/
abbrev Result (β : Type) := Except ReadDiagnostic β

/-- `n` applied to `args`, if `n` is a type of that arity whose parameters have the
arguments' kinds. -/
def typeApp {env : Env Unit} (ann : SourceRange) (n : MName SourceRange)
    (args : Array (TypeArg env)) : Result (TypeExpr env) :=
  let s := identText n
  let wrong (e : KindError) : Result (TypeExpr env) := .error ⟨ann, match e with
    | .count given expected => s!"type {s} takes {expected} argument(s), given {given}"
    | .kind i given expected => s!"argument {i + 1} of type {s} is \
      {KindedTypeArgs.kindText given}, but its parameter takes \
      {KindedTypeArgs.kindText expected}"⟩
  match env.get? (nameOf s) with
  | some (.type r) =>
    match TypeArgs.check? r.kinds args with
    | .ok targs => .ok (.appK r ⟨targs.args, targs.size_args.trans r.size_kinds⟩ targs.kinds)
    | .error e => wrong e
  | some (.insn _) => .error ⟨ann, s!"{s} is an operation, not a type"⟩
  | none => .error ⟨ann, s!"unknown type {s}"⟩

/-- The source range of a type. -/
def typeAnn : MType SourceRange → SourceRange
  | .tyVar a _ | .tyPrim a _ | .tyApp a _ _ | .tyList a _ | .tyListVar a _ => a

/-- A closed type argument: a type, or a list literal `[τ, …]` of types. -/
def typeArg {env : Env Unit} : MType SourceRange → Result (TypeArg env)
  | .tyVar ann ⟨_, i⟩ => .error ⟨ann, s!"type variable #{i} outside a signature"⟩
  | .tyListVar ann ⟨_, i⟩ => .error ⟨ann, s!"list variable *#{i} outside a signature"⟩
  | .tyPrim ann n => .ty <$> typeApp ann n #[]
  | .tyApp ann n ⟨_, args⟩ => do
    .ty <$> typeApp ann n (← args.attach.mapM fun ⟨a, _⟩ => typeArg a)
  | .tyList _ ⟨_, es⟩ => do
    let es ← es.attach.mapM fun ⟨e, _⟩ => do
      match ← typeArg e with
      | .ty t => pure (TypeList.Elem.ty t)
      | .list _ => .error ⟨typeAnn e, "a list of types may not hold a list"⟩
    pure (.list (.lit es))

/-- A closed type. -/
def type {env : Env Unit} (t : MType SourceRange) : Result (TypeExpr env) := do
  match ← typeArg t with
  | .ty e => pure e
  | .list _ => .error ⟨typeAnn t, "a list of types where a type is expected"⟩

/-- The operation `s` names, with its signature. -/
def insnRef {env : Env Unit} (ann : SourceRange) (s : String) :
    Result ((isig : InsnSig env) × InsnRef env isig) :=
  match env.get? (nameOf s) with
  | some (.insn r) => .ok ⟨_, r⟩
  | some (.type _) => .error ⟨ann, s!"{s} is a type, not an operation"⟩
  | none => .error ⟨ann, s!"unknown operation {s}"⟩

/-- An operation's name: the base's control flow is printed without its namespace. -/
def baseControl (s : String) : String :=
  if s == "jump" || s == "branch" || s == "unreachable" then s!"base.{s}" else s

/-- The integer an integer literal denotes. -/
def int : MInt SourceRange → Int
  | .natInt _ ⟨_, n⟩ => n
  | .negInt _ ⟨_, n⟩ => -(n : Int)

/-- The binary64 value a float literal denotes. -/
def float : MFloat SourceRange → Float
  | .floatPos _ ⟨_, d⟩ => FloatText.ofDecimal ⟨d.mantissa < 0, d.mantissa.natAbs, d.exponent⟩
  | .floatNeg _ ⟨_, d⟩ =>
    FloatText.ofDecimal ⟨!decide (d.mantissa < 0), d.mantissa.natAbs, d.exponent⟩
  | .floatInf _ => Float.ofBits 0x7FF0000000000000
  | .floatNegInf _ => Float.ofBits 0xFFF0000000000000
  | .floatNan _ => Float.ofBits 0x7FF8000000000000

/-- Where a literal is. -/
def constAnn : MConst SourceRange → SourceRange
  | .constUnit a | .constBool a _ | .constInt a _ | .constFloat a _ | .constStr a _
  | .constFunc a _ | .constGhost a _ => a

/-- The constant a literal denotes, with `funcs` the module's functions and `ghosts` its ghosts,
by name. -/
def constOf {β γ : Type} (funcs : NameTable β) (ghosts : NameTable γ) :
    MConst SourceRange → Result Const
  | .constUnit _ => pure .unit
  | .constBool _ ⟨_, b⟩ => pure (.bool b)
  | .constInt _ i => pure (.int (int i))
  | .constFloat _ f => pure (.float (float f))
  | .constStr _ ⟨_, s⟩ => pure (.str s)
  | .constFunc ann (.funcName _ n) =>
    let f := nameOf (identText n)
    if (funcs.get? f).isSome then pure (.func f)
    else throw ⟨ann, s!"no function @{identText n} in this module"⟩
  | .constGhost ann (.funcName _ n) =>
    let g := nameOf (identText n)
    if (ghosts.get? g).isSome then pure (.ghost g)
    else throw ⟨ann, s!"no ghost @{identText n}"⟩

/-- A module's functions, by name: where each is, and its code type, from its header, unless
the header's types do not read. -/
abbrev Funcs (env : Env Unit) := NameTable (SourceRange × Option (TypeExpr env))

/-- A module's ghosts, by name: where each is declared, its position among them, and the type of
its contents. -/
abbrev Ghosts (env : Env Unit) := NameTable (SourceRange × Nat × TypeExpr env)

/-- A literal, at `expected`, with `funcs` the module's functions and `ghosts` its ghosts.  A
literal's type is the one its form fixes, and must be `expected`.  A function reference has type
`expected`, which must be its target's code type.  A ghost reference names a ghost of the module,
and has type `expected`, which must be the type of the ghost's cell, a `base.Ref` of the ghost's
type. -/
def literal {env : Env Unit} [base ≼ env] (funcs : Funcs env) (ghosts : Ghosts env)
    (expected : TypeExpr env) (c : MConst SourceRange) : Result Const := do
  let k : Const ← match c with
    | .constFunc ann (.funcName _ n) =>
      let f := nameOf (identText n)
      let some (_, ct?) := funcs.get? f
        | throw ⟨ann, s!"no function @{identText n} in this module"⟩
      if ct? = some expected then return .func f
      let ct := (ct?.map typeText).getD "?"
      throw ⟨ann, s!"@{identText n} has type {ct}, where {typeText expected} is expected"⟩
    | .constGhost ann (.funcName _ n) =>
      let g := nameOf (identText n)
      let some (_, _, t) := ghosts.get? g | throw ⟨ann, s!"no ghost @{identText n}"⟩
      let cell := Base.Ref t
      if expected = cell then return .ghost g
      throw ⟨ann, s!"ghost @{identText n} holds {typeText t}, so its constant has type \
        {typeText cell}, not {typeText expected}"⟩
    | c => constOf funcs ghosts c
  let t? : Option (TypeExpr env) := k.typeOf?
  if t? = some expected then pure k
  else throw ⟨constAnn c, s!"a {(t?.map typeText).getD "?"} literal where {typeText expected} \
    is expected"⟩

/-! ## The state of reading a function -/

-- One walk over the text, in order.  A value gets the next id where it is defined, and a
-- folded constant where it is met; the constant is named after the walk.  A use before the
-- definition is recorded and resolved after the walk, so the walk builds `Late` parts.

/-- A part of the function that may name values defined further on: it is completed by the
id of every name. -/
abbrev Late (β : Type) := (Name → ValId) → β

/-- A use of the value `name` before its definition, at `range`, where the type `type` is
expected.  `what` says where, for the message. -/
structure Use (env : Env Unit) where
  name : Name
  type : TypeExpr env
  range : SourceRange
  what : String

/-- Reading a contract region of the function or the ghost `fn`: what it may use, the
parameters, ids below `params`, and its own values, ids from `start` on.  `place` names it in
messages: `clause` or `frame region`, or `initializer` or `invariant` for a ghost, which `ghost`
says `fn` is. -/
structure ClauseScope where
  fn : String
  params : Nat
  start : Nat
  place : String
  ghost : Bool := false

/-- What owns the contract region, for a message: `@m.f`, or `ghost @m.g`. -/
def ClauseScope.owner (c : ClauseScope) : String :=
  if c.ghost then s!"ghost @{c.fn}" else s!"@{c.fn}"

/-- What reading a function has found so far. -/
structure State (env : Env Unit) where
  /-- The values defined so far, by name, with a slot per id: a folded constant's is empty
  until the walk ends. -/
  values : NameTable ValId := ∅
  /-- The type of each value, by id. -/
  types : Array (TypeExpr env) := #[]
  /-- The uses of values not defined where they are used. -/
  uses : Array (Use env) := #[]
  /-- Every label defined so far. -/
  labels : Std.HashSet Name := {}
  /-- The clause being read, if any. -/
  clause : Option ClauseScope := none

/-- Reading a function: its state, and the first problem found. -/
abbrev ReadM (env : Env Unit) := StateT (State env) (Except ReadDiagnostic)

variable {env : Env Unit} [base ≼ env]

/-- Stop at the problem `msg`, at `range`. -/
def fail {β : Type} (range : SourceRange) (msg : String) : ReadM env β :=
  throw ⟨range, msg⟩

/-- The name a printed value denotes. -/
def valName : MVal SourceRange → Name
  | .valName _ n => nameOf (identText n)

/-- Define the value named `n`, of type `t`, at `range`: the next id. -/
def define (range : SourceRange) (n : Name) (t : TypeExpr env) : ReadM env ValId := do
  let s ← get
  let id : ValId := ⟨s.types.size⟩
  let some values := s.values.insert? n id
    | fail range s!"{ToDDM.valNameText n} is defined twice"
  set { s with values, types := s.types.push t }
  return id

/-- Define a folded constant of type `t`: the next id, named after the walk. -/
def defineConst (t : TypeExpr env) : ReadM env ValId := do
  let s ← get
  let id : ValId := ⟨s.types.size⟩
  -- Nothing reads `s` after this, so `push` updates the array in place.
  set { s with values := s.values.reserve, types := s.types.push t }
  return id

/-- A use of the value named `n` where the type `t` is expected, at `range`.  A value
defined already is checked at once; one defined further on is recorded. -/
def use (range : SourceRange) (what : String) (n : Name) (t : TypeExpr env) :
    ReadM env (Late ValId) := do
  let s ← get
  match s.values.get? n with
  | some id =>
    if let some c := s.clause then
      if c.params ≤ id.id ∧ id.id < c.start then
        if c.ghost then
          fail range s!"the {c.place} of ghost @{c.fn} uses {ToDDM.valNameText n}, which is not \
            one of its own values"
        fail range s!"a contract of @{c.fn} uses {ToDDM.valNameText n}, which is neither a \
          parameter of @{c.fn} nor defined in the {c.place}"
    let some t₁ := s.types[id.id]? | fail range s!"{ToDDM.valNameText n} has no type"
    if t₁ ≠ t then
      fail range s!"{ToDDM.valNameText n} has type {typeText t₁}, but {what} takes {typeText t}"
    return fun _ => id
  | none =>
    set { s with uses := s.uses.push ⟨n, t, range, what⟩ }
    return fun ids => ids n

/-- Record the label `l`, at `range`. -/
def defineLabel (range : SourceRange) (l : Name) : ReadM env Unit := do
  if l == .base then fail range "no block may be named _"
  if (← get).labels.contains l then
    fail range s!"block {ToDDM.nameText l} is defined twice"
  modify fun s => { s with labels := s.labels.insert l }

/-- A declaration, recorded as a definition. -/
def valDecl : MValDecl SourceRange → ReadM env (ValDecl env)
  | .valDecl ann v ty => do
    let t ← type ty
    return ⟨← define ann (valName v) t, t⟩

/-- Each of `ls`, completed. -/
def Late.all {β : Type} (ls : Array (Late β)) : Late (Array β) := fun ids => ls.map (· ids)

/-- Each of `ls`, completed, as an array. -/
def Late.list {β : Type} (ls : List (Late β)) : Late (Array β) :=
  fun ids => (ls.map (· ids)).toArray

/-- What the reader needs while it reads a function or a ghost.  `funcs` and `ghosts` are the
module's functions and ghosts.  `fn` is the name of the function, for a message.  `initOf` is set
while the reader reads the initializer of a ghost: the ghost's position and its name.
`invariantOf` is set while the reader reads the invariant of a ghost: the ghost's name.  `ownRet`
is set while the reader reads the own blocks of a frame region or of a ghost's region: the type
that their `ret` must pass, and the message for another type, given the text of that type. -/
structure FnCtx (env : Env Unit) where
  funcs : Funcs env
  ghosts : Ghosts env := NameTable.empty
  fn : String := ""
  initOf : Option (Nat × String) := none
  invariantOf : Option String := none
  ownRet : Option (TypeExpr env × (String → String)) := none

/-- A literal at `expected`, as `literal` reads it.  A ghost reference may appear only in a
contract region, in an initializer only for a ghost declared before the initializer's own, and
not in an invariant.  A ghost's regions hold no function reference. -/
def constant (fx : FnCtx env) (expected : TypeExpr env) (c : MConst SourceRange) :
    ReadM env Const := do
  match c with
  | .constGhost ann (.funcName _ n) =>
    if let some (_, i, _) := fx.ghosts.get? (nameOf (identText n)) then
      if (← get).clause.isNone then
        fail ann s!"@{fx.fn} uses ghost @{identText n} outside its contract"
      if let some own := fx.invariantOf then
        fail ann s!"the invariant of ghost @{own} names ghost @{identText n}; an invariant \
          receives the ghost's contents as its argument"
      if let some (j, own) := fx.initOf then
        if i == j then fail ann s!"the initializer of ghost @{own} names its own ghost"
        if j < i then
          fail ann s!"the initializer of ghost @{own} names ghost @{identText n}, which is \
            declared after it"
  | .constFunc ann (.funcName _ n) =>
    let region := match fx.initOf, fx.invariantOf with
      | some (_, own), _ => some s!"the initializer of ghost @{own}"
      | none, some own => some s!"the invariant of ghost @{own}"
      | none, none => none
    if let some r := region then
      fail ann s!"{r} refers to function @{identText n}; a ghost region may not refer to a \
        function"
  | _ => pure ()
  literal fx.funcs fx.ghosts expected c

/-- Operands at the types `expected`, one each: the constants to emit before their user,
and the ids.  `what` says whose operands they are. -/
def operands (fx : FnCtx env) (what : String) (expected : Array (TypeExpr env))
    (ops : Array (MOperand SourceRange)) :
    ReadM env (Array (Instruction env SourceRange) × Late (Array ValId)) := do
  if ops.size ≠ expected.size then
    fail .none s!"{what} takes {expected.size} operand(s), given {ops.size}"
  let mut pre := #[]
  let mut ids := #[]
  for (op, t, i) in ops.zip (expected.zip (.range expected.size)) do
    match op with
    | .operandVal ann v => ids := ids.push (← use ann s!"{what}, operand {i + 1}" (valName v) t)
    | .operandConst ann c =>
      let k ← constant fx t c
      let id ← defineConst t
      pre := pre.push (.const ann ⟨id, t⟩ k)
      ids := ids.push fun _ => id
  return (pre, Late.all ids)

/-- The parameter types of the blocks a transfer may name: the non-entry blocks of one body,
and its exit, `_`, which takes the body's result. -/
abbrev Scope (env : Env Unit) := Std.HashMap Name (Array (TypeExpr env))

/-- The scope of a body with blocks `blocks` and result `result`, and its entry block's
parameter types. -/
def scopeOf (ann : SourceRange) (result : TypeExpr env) (blocks : List (MBlock SourceRange)) :
    Result (Scope env × Array (TypeExpr env)) := do
  let headers ← blocks.mapM fun
    | .block bann l ⟨_, ps⟩ _ _ => do
      return (bann, nameOf (identText l), ← ps.mapM fun | .valDecl _ _ ty => type ty)
  let some (_, _, entry) := headers.head?
    | throw ⟨ann, "a body needs an entry block"⟩
  -- A repeated label, or `_`, is reported at its header, before any transfer to it.
  let scope ← (headers.drop 1).foldlM (init := ({} : Scope env).insert .base #[result])
    fun m (bann, l, ps) => do
      if l == .base then throw ⟨bann, "no block may be named _"⟩
      if m.contains l then throw ⟨bann, s!"block {ToDDM.nameText l} is defined twice"⟩
      return m.insert l ps
  return (scope, entry)

/-- Successors, against the payloads `payloads` the operation `what` declares. -/
def succs (fx : FnCtx env) (scope : Scope env) (ann : SourceRange) (what : String)
    (payloads : Array (Array (TypeExpr env))) (ss : Array (MSucc SourceRange)) :
    ReadM env (Array (Instruction env SourceRange) × Late (Array Target.Raw)) := do
  if ss.size ≠ payloads.size then
    fail ann s!"{what} takes {payloads.size} successor(s), given {ss.size}"
  let mut pre := #[]
  let mut ks : Array (Late Target.Raw) := #[]
  for (s, payload) in ss.zip payloads do
    let .succ sann l ⟨_, args⟩ := s
    let target := nameOf (identText l)
    let some params := scope[target]?
      | fail sann s!"no block {identText l} to transfer to here"
    if args.size + payload.size ≠ params.size then
      fail sann s!"block {identText l} takes {params.size} argument(s), given {args.size} \
        here and {payload.size} by {what}"
    if params.extract args.size ≠ payload then
      fail sann s!"{what} passes {typesText payload} to block {identText l}, which takes \
        {typesText (params.extract args.size)} there"
    let (p, ids) ← operands fx s!"{what}, successor ^{identText l}" (params.extract 0 args.size)
      args
    pre := pre ++ p
    ks := ks.push fun r => ⟨⟨target⟩, ids r⟩
  return (pre, Late.all ks)

/-- The type arguments of an application of `isig`: one per type parameter, each of its
kind. -/
def typeArgs (ann : SourceRange) (what : String) (isig : InsnSig env)
    (ta : Option (MTypeArgs SourceRange)) : ReadM env (TypeArgs env isig.scope) := do
  let ts ← match ta with
    | none => pure #[]
    | some (.typeArgs _ ⟨_, ts⟩) => ts.mapM fun t => (typeArg t : Result _)
  match TypeArgs.check? isig.scope ts with
  | .ok targs => return targs
  | .error (.count given expected) =>
    fail ann s!"{what} takes {expected} type argument(s), given {given}"
  | .error (.kind i given expected) =>
    fail ann s!"type argument {i + 1} of {what} is {KindedTypeArgs.kindText given}, but its \
      parameter takes {KindedTypeArgs.kindText expected}"

/-- The operands of an application of `isig`. -/
def callOperands (fx : FnCtx env) (ann : SourceRange) (what : String)
    (isig : InsnSig env) (targs : TypeArgs env isig.scope)
    (args : Option (MOperands SourceRange)) :
    ReadM env (Array (Instruction env SourceRange) × Late (Array ValId)) := do
  let ops := match args with
    | none => #[]
    | some (.operands _ ⟨_, ops⟩) => ops
  let n := isig.argTypes.size
  let some expected := isig.operandTypes? targs ops.size
    | let takes := match isig.variadic with
        | none => s!"{n}"
        | some ⟨_, .each _⟩ => s!"{n} or more"
        | some ⟨_, .spread cs⟩ => s!"{n + (cs.instantiate targs).elems.size}"
      fail ann s!"{what} takes {takes} operand(s), given {ops.size}"
  operands fx what expected ops

/-- In a contract region, an application of `isig`, the operation `what`, may not change state:
`isig` may not be declared `writes`. -/
def checkEffect (ann : SourceRange) (what : String) (isig : InsnSig env) : ReadM env Unit := do
  if let some c := (← get).clause then
    if isig.effect == .writes then
      fail ann s!"a contract region of {c.owner} may not change state, but {what} is declared \
        writes"

/-! ## Instructions, blocks and regions -/

/-- The type of an operand, if it is known where the operand is read: the type of a literal other
than a function reference, the type of the cell of the ghost that a ghost reference names, or the
type of a value defined already. -/
def operandType? (fx : FnCtx env) : MOperand SourceRange → ReadM env (Option (TypeExpr env))
  | .operandVal _ v => do
    let s ← get
    return (s.values.get? (valName v)).bind fun id => s.types[id.id]?
  | .operandConst _ (.constFunc ..) => return none
  | .operandConst _ (.constGhost _ (.funcName _ n)) =>
    return (fx.ghosts.get? (nameOf (identText n))).map fun (_, _, t) => Base.Ref t
  | .operandConst _ c => return (constOf fx.funcs fx.ghosts c).toOption.bind (·.typeOf?)

mutual

-- Each returns one completion per element, and `Late.list` completes them all at once.  Building
-- the array at each step would copy the rest of the array for each element, which takes quadratic
-- time.

/-- Instructions, each preceded by the constants folded into it. -/
def insnList (fx : FnCtx env) (scope : Scope env) :
    List (MInsn SourceRange) → ReadM env (List (Late (Instruction env SourceRange)))
  | [] => return []
  | .insnConst ann d c :: is => do
    let .valDecl _ v ty := d
    let t ← type ty
    let k ← constant fx t c
    let id ← define ann (valName v) t
    let rest ← insnList fx scope is
    return (fun _ => .const ann ⟨id, t⟩ k) :: rest
  | .insnApply ann d n ⟨_, ta⟩ ⟨_, args⟩ ⟨_, ss⟩ ⟨_, ⟨regions⟩⟩ :: is => do
    let s := baseControl (identText n)
    let ⟨isig, op⟩ ← (insnRef ann s : Result _)
    if isig.returnType.isNone then fail ann s!"{s} ends a block, so it defines no value"
    checkEffect ann s isig
    let targs ← typeArgs ann s isig ta
    let (pre, ids) ← callOperands fx ann s isig targs args
    let (pre₁, ks) ← succs fx scope ann s (isig.succTypes targs) ss
    let .valDecl dann v _ := d
    let ⟨id, t⟩ ← valDecl d
    let ret := (isig.returnType.map (·.instantiate targs)).getD t
    if ret ≠ t then
      fail dann s!"{s} returns {typeText ret}, but {ToDDM.valNameText (valName v)} is declared \
        {typeText t}"
    let sigs := isig.regionTypes targs
    if sigs.length ≠ regions.length then
      fail ann s!"{s} takes {sigs.length} region(s), given {regions.length}"
    let rs ← regionList fx sigs regions
    let rest ← insnList fx scope is
    return (pre ++ pre₁).toList.map (fun i _ => i) ++
      (fun r => .apply ann ⟨id, t⟩ op targs (ids r) (ks r) (Late.list rs r)) :: rest

/-- A terminator, preceded by the constants folded into it. -/
def term (fx : FnCtx env) (scope : Scope env) : MTerm SourceRange →
    ReadM env (Array (Instruction env SourceRange) × Late (Terminator env SourceRange))
  | .termRet ann ⟨_, args⟩ => do
    let args := match args with
      | none => #[]
      | some (.operands _ ⟨_, ops⟩) => ops
    -- A region whose result has a meaning of its own, such as a frame region, which returns a
    -- `base.Loc`: if the type of what its own `ret` passes is known here and is another, the
    -- message says so.
    if let (some (want, msg), #[op]) := (fx.ownRet, args) then
      if let some t ← operandType? fx op then
        if t ≠ want then fail ann (msg (typeText t))
    let result := (scope[Name.base]?).getD #[]
    if args.size ≠ result.size then
      fail ann s!"ret takes {result.size} operand(s), given {args.size}"
    let (pre, ids) ← operands fx "ret" result args
    return (pre, fun r => .jump ann ⟨Label.exit, ids r⟩)
  | .termApply ann n ⟨_, ta⟩ ⟨_, args⟩ ⟨_, ss⟩ ⟨_, ⟨regions⟩⟩ => do
    let s := baseControl (identText n)
    let ⟨isig, op⟩ ← (insnRef ann s : Result _)
    if isig.returnType.isSome then fail ann s!"{s} returns a value, so it cannot end a block"
    checkEffect ann s isig
    let targs ← typeArgs ann s isig ta
    let (pre, ids) ← callOperands fx ann s isig targs args
    let (pre₁, ks) ← succs fx scope ann s (isig.succTypes targs) ss
    let sigs := isig.regionTypes targs
    if sigs.length ≠ regions.length then
      fail ann s!"{s} takes {sigs.length} region(s), given {regions.length}"
    let rs ← regionList fx sigs regions
    return (pre ++ pre₁, fun r => .apply ann op targs (ids r) (ks r) (Late.list rs r))

/-- Blocks, against the scope of their body. -/
def blockList (fx : FnCtx env) (scope : Scope env) :
    List (MBlock SourceRange) → ReadM env (List (Late (Block env SourceRange)))
  | [] => return []
  | .block ann l ⟨_, ps⟩ ⟨_, ⟨instrs⟩⟩ t :: bs => do
    let label := nameOf (identText l)
    defineLabel ann label
    let params ← ps.mapM valDecl
    let is ← insnList fx scope instrs
    let (pre, t) ← term fx scope t
    let rest ← blockList fx scope bs
    return (fun r => ⟨⟨label⟩, params, Late.list is r ++ pre, t r, ann⟩) :: rest

/-- Regions, against their signatures, one each. -/
def regionList (fx : FnCtx env) : List (RegionType env) → List (MRegion SourceRange) →
    ReadM env (List (Late (Region env SourceRange)))
  | sig :: sigs, .region ann ⟨_, ⟨blocks⟩⟩ :: rs => do
    let (scope, entry) ← (scopeOf ann sig.2 blocks : Result _)
    if entry ≠ sig.1 then
      fail ann s!"the region's entry block takes {typesText entry}, but {typesText sig.1} \
        is expected"
    let bs ← blockList { fx with ownRet := none } scope blocks
    let rest ← regionList fx sigs rs
    return (fun r => ⟨Late.list bs r⟩) :: rest
  | _, _ => return []

end

/-! ## Functions and modules -/

/-- Resolve the uses recorded before their definitions: each value is defined, at the type
its use expects. -/
def checkUses : ReadM env Unit := do
  let s ← get
  for u in s.uses do
    let some id := s.values.get? u.name
      | fail u.range s!"{ToDDM.valNameText u.name} is not defined"
    let t := s.types[id.id]?
    if t ≠ some u.type then
      fail u.range s!"{ToDDM.valNameText u.name} has type \
        {(t.map typeText).getD "?"}, but {u.what} takes {typeText u.type}"

/-- What a function's contract consists of, as read: its `requires` and `ensures` clauses and
its frames. -/
structure ContractParts (env : Env Unit) where
  requires : Array (Late (Array (Clause env SourceRange))) := #[]
  ensures : Array (Late (Array (Clause env SourceRange))) := #[]
  reads : Option (Late (Array (FrameEntry env SourceRange))) := none
  writes : Option (Late (Array (FrameEntry env SourceRange))) := none

/-- The kinds of contract clause, in the order they must come. -/
inductive ClauseKind where
  | requires | ensures | reads | writes
deriving DecidableEq

/-- A kind's place in the order. -/
def ClauseKind.rank : ClauseKind → Nat
  | .requires => 0 | .ensures => 1 | .reads => 2 | .writes => 3

/-- A kind, as a message names one clause of it: "a requires clause". -/
def ClauseKind.oneText : ClauseKind → String
  | .requires => "a requires clause" | .ensures => "an ensures clause"
  | .reads => "a reads clause" | .writes => "a writes clause"

/-- A kind, as a message names all its clauses: one frame, or every `requires` or `ensures`
clause. -/
def ClauseKind.allText : ClauseKind → String
  | .requires => "the requires clauses" | .ensures => "the ensures clauses"
  | .reads => "the reads clause" | .writes => "the writes clause"

/-- A frame's kind, `reads` or `writes`, as its clause is named. -/
def ClauseKind.frameName : ClauseKind → Option String
  | .reads => some "reads" | .writes => some "writes" | _ => none

/-- A clause's kind, and where it is. -/
def clauseKind : MClause SourceRange → ClauseKind × SourceRange
  | .clauseRequires ann .. => (.requires, ann)
  | .clauseEnsures ann .. => (.ensures, ann)
  | .clauseReads ann _ => (.reads, ann)
  | .clauseWrites ann _ => (.writes, ann)

/-- A clause's message, as written. -/
def messageOf : Option (MMessage SourceRange) → Option String
  | none => none
  | some (.message _ ⟨_, s⟩) => some s

/-- Read a contract region of the function `fn`, whose parameters are the ids below `params`,
with `read`, or of the ghost `fn` if `ghost` is set.  The region uses only the parameters and its
own values.  `place` names it in messages: `clause` or `frame region`, or `initializer` or
`invariant`. -/
def inContract {β : Type} (fn : String) (params : Nat) (place : String) (read : ReadM env β)
    (ghost : Bool := false) : ReadM env β := do
  let s ← get
  let usesBefore := s.uses.size
  set { s with clause := some ⟨fn, params, s.types.size, place, ghost⟩ }
  let r ← read
  -- A use not defined by the region's end is not the region's own.
  let s ← get
  for u in s.uses.extract usesBefore do
    if (s.values.get? u.name).isNone then
      fail u.range s!"{ToDDM.valNameText u.name} is not defined in its {place}"
  set { s with clause := none }
  return r

/-- The region of a `requires` or `ensures` clause of the function `fn`, at `sig`.  It uses only
the parameters, the ids below `params`, and its own values. -/
def clauseRegion (fx : FnCtx env) (fn : String) (params : Nat) (sig : RegionType env)
    (r : MRegion SourceRange) : ReadM env (Late (Array (Region env SourceRange))) :=
  inContract fn params "clause" (Late.list <$> regionList fx [sig] [r])

/-- A frame region of the function `fn`, at `ann`, with the blocks `blocks`: it takes no arguments
and returns a `base.Loc`, and uses only the parameters, the ids below `params`, and its own
values. -/
def frameRegion (fx : FnCtx env) (fn : String) (params : Nat) (ann : SourceRange)
    (blocks : List (MBlock SourceRange)) : ReadM env (Late (Region env SourceRange)) :=
  inContract fn params "frame region" do
    let (scope, entry) ← (scopeOf ann Base.Loc blocks : Result _)
    unless entry.isEmpty do fail ann "a frame region takes no arguments"
    let msg (t : String) :=
      s!"a frame region of @{fn} returns {t}, but a frame region returns a base.Loc"
    let bs ← blockList { fx with ownRet := some (Base.Loc, msg) } scope blocks
    return fun r => ⟨Late.list bs r⟩

/-- A frame of the function `fn`, whose parameters are the ids below `params`.  Each cell it names
is a parameter of type `base.Ref`, and none is named twice; each region is a frame region.  `what`
names the frame, for a message. -/
def frame (fx : FnCtx env) (fn what : String) (params : Nat)
    (entries : Array (MFrameEntry SourceRange)) :
    ReadM env (Late (Array (FrameEntry env SourceRange))) := do
  -- The ids of the cells named so far.
  let mut cells : Std.HashSet Nat := {}
  let mut out : Array (Late (FrameEntry env SourceRange)) := #[]
  for e in entries do
    match e with
    | .frameCell _ v =>
      let s ← get
      let n := valName v
      let .valName ann _ := v
      let some id := (s.values.get? n).filter (·.id < params)
        | fail ann s!"{what} names {ToDDM.valNameText n}, which is not a parameter of @{fn}"
      let t := s.types[id.id]?
      unless t.any (·.isRef) do
        fail ann s!"{what} names {ToDDM.valNameText n}, of type {(t.map typeText).getD "?"}, \
          but a frame names only cells, of type base.Ref"
      if cells.contains id.id then fail ann s!"{what} names {ToDDM.valNameText n} twice"
      cells := cells.insert id.id
      out := out.push fun _ => .cell id
    | .frameRegion ann ⟨_, ⟨blocks⟩⟩ =>
      let r ← frameRegion fx fn params ann blocks
      out := out.push fun ids => .region (r ids)
  return Late.all out

/-- The contract of the function `fn`, whose parameters are the ids below `params`.  The
clauses come in the order of `ClauseKind`, with at most one frame of each kind.  Each clause
uses only the parameters and its own values.  The `ensures` clauses are `free` if the function
is `extern`, and checked if it is not. -/
def clauseList (fx : FnCtx env) (fn : String) (extern : Bool) (params : Nat)
    (retType : TypeExpr env) (clauses : List (MClause SourceRange)) :
    ReadM env (ContractParts env) := do
  let mut parts : ContractParts env := {}
  let mut last : Option ClauseKind := none
  for c in clauses do
    let (k, ann) := clauseKind c
    if let some l := last then
      if k.rank < l.rank then fail ann s!"{k.oneText} must come before {l.allText}"
      if let some f := k.frameName then
        if k == l then fail ann s!"@{fn} has two {f} clauses"
    last := some k
    match c with
    | .clauseReads _ ⟨_, entries⟩ =>
      parts := { parts with reads := some (← frame fx fn "reads" params entries) }
    | .clauseWrites _ ⟨_, entries⟩ =>
      parts := { parts with writes := some (← frame fx fn "writes" params entries) }
    | .clauseRequires _ ⟨_, msg⟩ r =>
      let rs ← clauseRegion fx fn params (#[], Base.Bool) r
      let message := messageOf msg
      parts := { parts with
        requires := parts.requires.push fun ids => (rs ids).map fun region => { region, message } }
    | .clauseEnsures _ ⟨_, free⟩ ⟨_, msg⟩ r =>
      let free := free.isSome
      if extern && !free then fail ann s!"@{fn} is extern, so its ensures clauses must be free"
      if free && !extern then
        fail ann s!"free ensures is allowed only on an extern function, but @{fn} has a body"
      let rs ← clauseRegion fx fn params (#[retType], Base.Bool) r
      let message := messageOf msg
      parts := { parts with
        ensures := parts.ensures.push fun ids =>
          (rs ids).map fun region => { region, free, message } }
  return parts

/-! ## Failures and cycles in contract regions

The diagnostics of `Func.ContractRegionsWF` and `Ghost.ContractRegionsWF`: they only explain why
it fails. -/

/-- The name of the value `v`, with `names` the names of the values of its function or ghost,
as printed, for a message. -/
def valText (names : Array Name) (v : ValId) : String :=
  ToDDM.valNameText (names[v.id]?.getD (.str .base s!"?{v.id}"))

/-- The blocks of `bs`, by label. -/
def blocksByLabel (bs : List (Block env Info)) : LabelMap (Block env Info) :=
  bs.foldl (fun m b => m.insert b.label b) ∅

/-- The first failure successor of the region's own blocks that goes where `ok` rejects: its
instruction, and the block it goes to, or `none` if it goes to no block of the region, such as
the exit. -/
def badFailure? (ok : Block env Info → Bool) (r : Region env Info) :
    Option (Instruction env Info × Option (Block env Info)) :=
  let byLabel := blocksByLabel r.blocks.toList
  r.blocks.toList.findSome? fun b => b.instrs.toList.findSome? fun i =>
    i.succs.toList.findSome? fun k =>
      match byLabel.find? k.label with
      | some t => if ok t then none else some (i, some t)
      | none => some (i, none)

/-- Where an instruction is. -/
def instrRange : Instruction env Info → SourceRange
  | .const info .. | .apply info .. => info.range

/-- Where a terminator is, and the name of its operation. -/
def termSite : Terminator env Info → SourceRange × Name
  | .apply info r .. => (info.range, r.name)

/-- The constant that a block made only of constants returns, if it ends in `ret` of a boolean
constant that it defines. -/
def constReturned? (b : Block env Info) : Option Bool := do
  guard (b.instrs.all fun | .const .. => true | .apply .. => false)
  let v ← b.term.retValue?
  b.instrs.toList.findSome? fun
    | .const _ d (.bool c) => if d.id == v then some c else none
    | _ => none

/-- Why the failure successors of `r`, the contract region `what` (such as "a requires clause")
of `owner` (such as "@m.f" or "ghost @m.g"), break `Region.FailsWith value`, if they do.  `names`
are the names of the owner's values. -/
def failsWithDiagnostic? (names : Array Name) (owner what : String) (value : Option Bool)
    (r : Region env Info) : Option ReadDiagnostic := do
  let (i, t) ← badFailure? (Block.isFailure value) r
  let must := match value with
    | some c => s!"a failure must give {c} or be unreachable"
    | none => "a failure must be unreachable"
  let start := s!"in {what} of {owner}, the failure successor of {valText names i.result.id}"
  -- Where no failure value is allowed, returning a constant does not help either.
  let more := match value with
    | some _ => ""
    | none => s!"; {must}"
  pure ⟨instrRange i, match t with
    | none => s!"{start} leaves the region; {must}"
    | some t =>
      let to := s!"{start} goes to {ToDDM.nameText t.label.name}"
      match constReturned? t with
      | some c => s!"{to}, which returns {c}; {must}"
      | none =>
        if !t.instrs.all fun | .const .. => true | .apply .. => false then
          s!"{to}, which does more than define constants{more}"
        else match value with
          | some _ => s!"{to}, which does not end in unreachable or in ret of a constant that it \
            defines"
          | none => s!"{to}, which does not end in unreachable{more}"⟩

/-- Whether the only instruction of `b` applies `base.error` to its last parameter, as that of a
propagating block does, whatever `b` returns. -/
def errorsOnFailure (b : Block env Info) : Bool :=
  match b.instrs.toList, b.params.back? with
  | [.apply _ _ r _ args _ _], some p => r.name == bn "error" && args == #[p.id]
  | _, _ => false

/-- Why a region nested in the regions `rs` of `owner` breaks `Region.Propagates`, if one
does. -/
def propagatesDiagnostic? (names : Array Name) (owner : String) (rs : List (Region env Info)) :
    Option ReadDiagnostic :=
  (Region.nestedList rs).findSome? fun (r, may) => do
    let (i, t) ← badFailure? (fun t => t.isFailure none || (may && t.isPropagating)) r
    let start := s!"in a region nested in a contract of {owner}, the failure successor of \
      {valText names i.result.id}"
    pure ⟨instrRange i, match t with
      | none => s!"{start} leaves its region, so it does not pass the failure on with base.error"
      | some t =>
        if t.isPropagating then
          s!"{start} goes to {ToDDM.nameText t.label.name}, but this region's operation does not \
            pass failures on, so the failure must be unreachable"
        else if errorsOnFailure t then
          s!"{start} goes to {ToDDM.nameText t.label.name}, which does not return the result of \
            its base.error"
        else
          s!"{start} goes to {ToDDM.nameText t.label.name}, which does not pass the failure on \
            with base.error"⟩

/-- Why a block of the regions `rs` of `owner` breaks `Region.EndsInControl`, if one does. -/
def endsInControlDiagnostic? (owner : String) (rs : List (Region env Info)) :
    Option ReadDiagnostic :=
  (Region.allList rs).findSome? fun r => r.blocks.toList.findSome? fun b =>
    if b.term.isControl then none
    else
      let (range, op) := termSite b.term
      some ⟨range, s!"a contract region of {owner} ends {ToDDM.nameText b.label.name} with \
        {ToDDM.nameText op}; a contract region may end a block only with ret, jump, branch, \
        unreachable or a case instruction"⟩

/-- A block on a cycle of the blocks `bs`, if they have one.  The blocks that Kahn's algorithm
does not remove each transfer to one of them, so following such transfers from any of them
reaches a cycle within as many steps as there are of them. -/
def cycleBlock? (bs : List (Block env Info)) : Option (Block env Info) :=
  let rest := Body.unremovedBy bs (Body.sinkOrder bs.toArray)
  let byLabel := blocksByLabel rest
  let next (b : Block env Info) : Option (Block env Info) :=
    (Body.edges b).findSome? fun e => byLabel.find? e.2
  match rest with
  | [] => none
  | b :: _ => rest.foldl (fun ob _ => ob.bind next) (some b)

/-- Why the contract regions `rs` of `owner` break the rules for contract regions, if they do:
the first of `regions`, each a region of `rs` with how it is named and its failure value, whose
failures go elsewhere than `Region.FailsWith` asks, then the first nested region that does not
pass its failures on, then the first block that does not end in control flow, then a cycle. -/
def regionsDiagnostic? (names : Array Name) (owner : String)
    (regions : List (String × Option Bool × Region env Info)) (rs : List (Region env Info)) :
    Option ReadDiagnostic :=
  (regions.findSome? fun (what, value, r) => failsWithDiagnostic? names owner what value r) <|>
    propagatesDiagnostic? names owner rs <|>
    endsInControlDiagnostic? owner rs <|>
    ((Region.allList rs).findSome? fun r =>
      if Body.acyclicB r.blocks.toList then none else cycleBlock? r.blocks.toList).map fun b =>
      ⟨b.info.range, s!"a contract region of {owner} has a cycle through \
        {ToDDM.nameText b.label.name}"⟩

/-- Why the contract regions of `fn` break `Func.ContractRegionsWF`, if they do: the first
clause or frame region whose failures go elsewhere than the rules ask, then the first nested
region that does not pass its failures on, then the first block that does not end in control
flow, then a cycle. -/
def contractRegionsDiagnostic? (fn : Func env Info) (fnName : String) :
    Option ReadDiagnostic :=
  regionsDiagnostic? fn.names s!"@{fnName}"
    (fn.contract.requires.toList.map (("a requires clause", some false, ·.region)) ++
      fn.contract.ensures.toList.map (fun c =>
        (if c.free then "a free ensures clause" else "an ensures clause", some c.free, c.region)) ++
      fn.contract.frameRegions.map (("a frame region", none, ·)))
    fn.contract.regions

/-! ## Scoping in contract regions -/

/-- Why the clauses and frame regions of `fn` break the scoping part of `Func.ClauseWF`, which
asks each to be reachable and scoped as a body entered where only the parameters are visible: for
each region that is not, the messages of `Region.scopeDiagnostics`, each led by the kind of the
region. -/
def clauseScopeDiagnostics (fn : Func env Info) : Array String :=
  let params := fn.params.map (·.id)
  let regions := fn.contract.requires.toList.map (("a requires clause", ·.region)) ++
    fn.contract.ensures.toList.map (fun c =>
      (if c.free then "a free ensures clause" else "an ensures clause", c.region)) ++
    fn.contract.frameRegions.map (("a frame region", ·))
  regions.foldl (init := #[]) fun out (what, r) =>
    if r.domOK fn.isParam then out
    else out ++ (r.scopeDiagnostics fn.names params).map (s!"in {what}, " ++ ·)

/-! ## `old` in `ensures` clauses

The diagnostics of `Func.OldWF`: they only explain why it fails. -/

/-- The first application of `base.old` in the regions `rs`, at any depth. -/
def firstOld? (rs : List (Region env Info)) : Option (Instruction env Info) :=
  (Region.allList rs).findSome? fun r => r.blocks.toList.findSome? fun b =>
    b.instrs.toList.find? (·.isOld)

/-- The diagnostic of an application `i` of `base.old` in `place` of `owner`. -/
def oldFound (owner place : String) (i : Instruction env Info) : ReadDiagnostic :=
  ⟨instrRange i, s!"base.old is allowed only in an ensures clause, but {owner} uses it in {place}"⟩

/-- Why `fn` breaks `Func.OldPlaced`, if it does: the first application of `base.old` in its body,
or else in a `requires` clause, or else in a frame region. -/
def oldPlacedDiagnostic? (fn : Func env Info) (fnName : String) : Option ReadDiagnostic :=
  let found := oldFound s!"@{fnName}"
  ((firstOld? [⟨fn.blocks⟩]).map (found "its body")) <|>
    (fn.contract.requires.toList.findSome? fun c =>
      (firstOld? [c.region]).map (found "a requires clause")) <|>
    fn.contract.frameRegions.findSome? fun r => (firstOld? [r]).map (found "a frame region")

/-- The values that an instruction or a terminator uses: its operands `args`, then the arguments
of its successors `succs`. -/
def usedValues (args : Array ValId) (succs : Array Target.Raw) : List ValId :=
  args.toList ++ succs.toList.flatMap (·.args.toList)

/-- Why an `ensures` clause of `fn` breaks `Region.OldScoped`, if one does: the first use, in an
outermost `old` region at any depth, of a value that the region neither sees from outside it nor
defines.  Such a value is the result, or another value that the clause defines outside the `old`
region. -/
def oldScopedDiagnostic? (fn : Func env Info) (fnName : String) : Option ReadDiagnostic :=
  fn.contract.ensures.toList.findSome? fun c =>
    let consts := Region.constIds [c.region]
    let result := Body.entryParams c.region.blocks.toList
    (Block.oldRegionsList [] c.region.blocks.toList).findSome? fun (o, ps) =>
      let own : Std.HashSet Nat := (Region.defsList [o]).foldl (fun s d => s.insert d.id.id) {}
      let bad (vs : List ValId) : Option ValId :=
        vs.find? fun x => !(Region.oldSees fn.isParam consts ps x || own.contains x.id)
      let use? (b : Block env Info) : Option (SourceRange × ValId) :=
        (b.instrs.toList.findSome? fun i => (bad (usedValues i.args i.succs)).map (instrRange i, ·))
          <|> (bad (usedValues b.term.args b.term.succs)).map ((termSite b.term).1, ·)
      ((Region.allList [o]).findSome? fun r => r.blocks.toList.findSome? use?).map fun (range, x) =>
        let what := if result.contains x then "is the result"
          else "the clause defines outside the old region"
        ⟨range, s!"the old region in @{fnName} uses {valText fn.names x}, which {what}"⟩

/-- The name of the folded constant chosen `k`-th: `c.k`. -/
def constName (k : Nat) : Name := .num (.str .base "c") k

/-- What a function's text consists of: where it is, its name, whether it is extern, its
parameters, its return type, its contract's clauses, its attributes and its blocks. -/
structure Header where
  ann : SourceRange
  name : MName SourceRange
  extern : Bool
  params : Array (MValDecl SourceRange)
  retType : MType SourceRange
  clauses : List (MClause SourceRange)
  attrs : Option (MAttrs SourceRange)
  blocks : List (MBlock SourceRange)

/-- The parts of a function's text.  An extern has no attributes and no blocks. -/
def header : MFunc SourceRange → Header
  | .func ann (.funcName _ n) ⟨_, ps⟩ retTy ⟨_, attrs⟩ ⟨_, blocks⟩ =>
    ⟨ann, n, false, ps, retTy, [], attrs, blocks.toList⟩
  | .funcContract ann (.funcName _ n) ⟨_, ps⟩ retTy c ⟨_, cs⟩ ⟨_, attrs⟩ ⟨_, blocks⟩ =>
    ⟨ann, n, false, ps, retTy, c :: cs.toList, attrs, blocks.toList⟩
  | .funcExtern ann (.funcName _ n) ⟨_, ps⟩ retTy ⟨_, cs⟩ =>
    ⟨ann, n, true, ps, retTy, cs.toList, none, []⟩

/-- The name a function header gives. -/
def headerName (f : MFunc SourceRange) : Name := nameOf (identText (header f).name)

/-- Where a function is. -/
def headerAnn (f : MFunc SourceRange) : SourceRange := (header f).ann

/-- The code type a function's header gives: `base.Fn` of its parameters' types and its
return type, unless they do not read.  Reading the function checks it against its body. -/
def headerCodeType? (f : MFunc SourceRange) : Option (TypeExpr env) := do
  let ts ← (header f).params.mapM fun | .valDecl _ _ ty => (type ty).toOption
  let r ← (type (header f).retType).toOption
  pure (Base.Fn (TypeList.ofTypes ts) r)

/-- The pairs of `kvs`, with their keys read as names, or an error at the second use of a
key.  `what` names the keys in the message. -/
def unique {β : Type} (what : String) (kvs : Array (SourceRange × MName SourceRange × β)) :
    Result (Array (Name × β)) :=
  let named := kvs.toList.map fun (ann, k, v) => (nameOf (identText k), (ann, k, v))
  match NameTable.empty.insertAll? named with
  | .ok _ => pure (kvs.map fun (_, k, v) => (nameOf (identText k), v))
  | .error (_, ann, k, _) => throw ⟨ann, s!"{what} {identText k} is given twice"⟩

/-- An attribute's value, with `funcs` the module's functions and `ghosts` its ghosts.  A ghost
named in a value is not a use of the ghost by the function. -/
def attrValue (funcs : Funcs env) (ghosts : Ghosts env) :
    MAttrValue SourceRange → Result AttrValue
  | .attrConst _ c => .const <$> constOf funcs ghosts c
  | .attrList _ ⟨_, vs⟩ => .list <$> vs.attach.mapM fun ⟨v, _⟩ => attrValue funcs ghosts v
  | .attrRecord _ ⟨_, fs⟩ => do
    let kvs ← fs.attach.mapM fun
      | ⟨.attrField a k v, h⟩ =>
        have hv : sizeOf v < 1 + sizeOf fs := by
          have hlt := Array.sizeOf_lt_of_mem h
          simp only [MAttrField.attrField.sizeOf_spec] at hlt
          omega
        return (a, k, ← attrValue funcs ghosts v)
    .record <$> unique "field" kvs

/-- A function's attributes. -/
def attrsOf (funcs : Funcs env) (ghosts : Ghosts env) :
    Option (MAttrs SourceRange) → Result (Array Attr)
  | none => pure #[]
  | some (.attrs _ ⟨_, as⟩) => do
    unique "attribute" (← as.mapM fun | .attr a k v => return (a, k, ← attrValue funcs ghosts v))

/-- A well-formed function, with `funcs` the module's functions and `ghosts` its ghosts.  An
extern's parameters are read first, then the body, then the contract, so that the values get ids
in the order of `Func.defs`. -/
def func (funcs : Funcs env) (ghosts : Ghosts env) (f : MFunc SourceRange) :
    Result {fn : Func env Info // fn.name = headerName f ∧ fn.WF} :=
  match hf : header f with
  | ⟨ann, n, extern, ps, retTy, clauses, attrs, blocks⟩ => do
    let attrs ← attrsOf funcs ghosts attrs
    let fx : FnCtx env := { funcs, ghosts, fn := identText n }
    let retType ← type retTy
    let (scope, entryParams) ← if extern then pure ({}, #[]) else scopeOf ann retType blocks
    let run : ReadM env (Array (ValDecl env) × Late (Array (Block env SourceRange)) ×
        ContractParts env) := do
      let params ← if extern then ps.mapM valDecl else pure #[]
      let bs := Late.list (← blockList fx scope blocks)
      let bodyEnd := (← get).types.size
      let bodyUses := (← get).uses.size
      let parts ← clauseList fx (identText n) extern
        (if extern then params.size else entryParams.size) retType clauses
      -- The body may not use a value of the contract.
      let s ← get
      for u in s.uses.extract 0 bodyUses do
        if let some id := s.values.get? u.name then
          if bodyEnd ≤ id.id then
            fail u.range s!"the body of @{identText n} uses {ToDDM.valNameText u.name}, a \
              value of its contract"
      checkUses
      return (params, bs, parts)
    let ((params, bs, parts), s) ← run.run {}
    let ids : Name → ValId := fun n => (s.values.get? n).getD ⟨0⟩
    let blocks := (bs ids).map (Block.map fun range => ({ range } : Info))
    -- A defined function's signature repeats its entry block's parameters.
    let params ← if extern then pure params else do
      let sig ← ps.mapM fun | .valDecl _ v ty => return (valName v, ← type ty)
      let entry := (blocks[0]?.map (·.params)).getD #[]
      let named ← entry.mapM fun d =>
        match s.values.slots[d.id.id]? with
        | some (some v) => pure (v, d.type)
        | _ => throw ⟨ann, s!"a parameter of @{identText n} has no name"⟩
      if sig ≠ named then
        throw ⟨ann, s!"the parameters of @{identText n} differ from its entry block's"⟩
      pure entry
    let some ⟨names, hnames⟩ := s.values.fill? constName ⟨0⟩
      | throw ⟨ann, s!"no fresh name for a constant of @{identText n}"⟩
    let toInfo (c : Clause env SourceRange) : Clause env Info := c.map fun range => { range }
    let frameInfo (l : Late (Array (FrameEntry env SourceRange))) : Array (FrameEntry env Info) :=
      (l ids).map (FrameEntry.map fun range => { range })
    let fn : Func env Info :=
      { name := nameOf (identText n), params, retType, extern, blocks,
        contract := { requires := (parts.requires.flatMap (· ids)).map toInfo
                      ensures := (parts.ensures.flatMap (· ids)).map toInfo
                      reads := parts.reads.map frameInfo, writes := parts.writes.map frameInfo }
        names, info := { range := ann, attrs } }
    -- The value names' table proves the names distinct; the rest of `Func.WF` is decided.
    if h : fn.extern = fn.blocks.isEmpty ∧
        (fn.extern = false → ∀ b ∈ fn.blocks[0]?, b.params = fn.params) ∧
        Label.Distinct (Label.exit :: fn.labels) ∧ ValDecl.idBound fn.defs ≤ fn.names.size ∧
        fn.BodyWF ∧ (fn.Reachable ∧ fn.Scopable) ∧ fn.ContractWF ∧ fn.ClauseModesWF ∧
        fn.ContractRegionsWF ∧ fn.OldWF ∧ fn.GhostsInContract then
      return ⟨fn, by simp [headerName, hf, fn], by
        obtain ⟨a, b, c, d, e, ⟨g, i⟩, j, k, l, m, o⟩ := h
        exact ⟨a, b, c, hnames, d, e, g, i, j, k, l, m, o⟩⟩
    else
      let why := (if fn.Reachable ∧ fn.Scopable then #[] else fn.scopeDiagnostics) ++
        clauseScopeDiagnostics fn
      if why.isEmpty then
        if let some d := contractRegionsDiagnostic? fn (identText n) <|>
            oldPlacedDiagnostic? fn (identText n) <|> oldScopedDiagnostic? fn (identText n) then
          throw d
      throw ⟨ann, s!"@{identText n} is not well formed" ++
        String.join (why.toList.map ("\n  " ++ ·))⟩

/-- The functions `l` denotes, each well formed, or the diagnostics of all that are not.  The
diagnostics are collected in a list, because adding each one to the front of an array would copy
the array each time. -/
def funcsOrDiagnostics (funcs : Funcs env) (ghosts : Ghosts env) :
    (l : List (MFunc SourceRange)) →
    Except (List ReadDiagnostic) {fs : List (Func env Info) //
      fs.map (·.name) = l.map headerName ∧ ∀ f ∈ fs, f.WF}
  | [] => .ok ⟨[], rfl, by simp⟩
  | f :: l =>
    match func funcs ghosts f, funcsOrDiagnostics funcs ghosts l with
    | .ok ⟨fn, hn, hw⟩, .ok ⟨fs, hs, hws⟩ =>
      .ok ⟨fn :: fs, by simp [hn, hs], List.forall_mem_cons.mpr ⟨hw, hws⟩⟩
    | .error e, .ok _ => .error [e]
    | .ok _, .error es => .error es
    | .error e, .error es => .error (e :: es)

/-- The functions `l` denotes, each well formed, or the diagnostics of all that are not. -/
def funcList (funcs : Funcs env) (ghosts : Ghosts env) (l : List (MFunc SourceRange)) :
    Except (Array ReadDiagnostic) {fs : List (Func env Info) //
      fs.map (·.name) = l.map headerName ∧ ∀ f ∈ fs, f.WF} :=
  (funcsOrDiagnostics funcs ghosts l).mapError List.toArray

/-! ## Ghosts -/

/-- What a ghost's text consists of: where it is, its name, the type of its contents, and its
initializer and its invariant, each if it has one. -/
structure GhostHeader where
  ann : SourceRange
  name : MName SourceRange
  type : MType SourceRange
  init : Option (MRegion SourceRange)
  invariant : Option (MRegion SourceRange)

/-- The parts of a ghost's text. -/
def ghostHeader : MGhost SourceRange → GhostHeader
  | .ghost ann (.funcName _ n) ty ⟨_, init⟩ ⟨_, inv⟩ =>
    ⟨ann, n, ty, init.map fun | .ghostInit _ r => r, inv.map fun | .ghostInvariant _ r => r⟩

/-- The module's ghosts `gs`, by name, with `funcs` its functions: where each is declared, its
position, and the type of its contents.  Or the diagnostic of the first ghost that has the name of
a function, whose type does not read, or that has the name of a ghost before it. -/
def ghostTable (funcs : Funcs env) (gs : Array (MGhost SourceRange)) : Result (Ghosts env) :=
  gs.zipIdx.foldlM (init := NameTable.empty) fun t (g, i) => do
    let h := ghostHeader g
    let n := nameOf (identText h.name)
    if (funcs.get? n).isSome then
      throw ⟨h.ann, s!"@{identText h.name} names both a ghost and a function"⟩
    let ty ← type h.type
    match t.insert? n (h.ann, i, ty) with
    | some t => pure t
    | none => throw ⟨h.ann, s!"ghost @{identText h.name} is declared twice"⟩

/-- A region of the ghost `g`, its `place` (`initializer` or `invariant`), at `sig`.  It takes
`sig`'s arguments, `entryMsg` giving the message for others from their text, returns `sig`'s
result, `retMsg` giving the message for another type from its text, and uses only its own
values. -/
def ghostRegion (fx : FnCtx env) (g place : String) (sig : RegionType env)
    (entryMsg retMsg : String → String) :
    MRegion SourceRange → ReadM env (Late (Region env SourceRange))
  | .region ann ⟨_, ⟨blocks⟩⟩ =>
    inContract g 0 place (ghost := true) do
      let (scope, entry) ← (scopeOf ann sig.2 blocks : Result _)
      if entry ≠ sig.1 then fail ann (entryMsg (typesText entry))
      let bs ← blockList { fx with ownRet := some (sig.2, retMsg) } scope blocks
      return fun r => ⟨Late.list bs r⟩

/-- Why the ghost `g` breaks `Ghost.WF`, if one of these explains it: the first problem with the
failures, the blocks or the transfers of its regions, as `regionsDiagnostic?` finds it, then the
first application of `base.old`, then each block that a region's entry does not reach and each
use out of scope.  `owner` names the ghost in messages: `ghost @m.g`. -/
def ghostDiagnostic? (g : Ghost env Info) (owner : String) : Option ReadDiagnostic :=
  let named := g.init.toList.map ("the initializer", none, ·) ++
    g.invariant.toList.map ("the invariant", none, ·)
  regionsDiagnostic? g.names owner named g.regions <|>
    (g.init.bind fun r => (firstOld? [r]).map (oldFound owner "its initializer")) <|>
    (g.invariant.bind fun r => (firstOld? [r]).map (oldFound owner "its invariant")) <|>
    let why := g.regions.foldl (fun out r => out ++ r.scopeDiagnostics g.names) #[]
    if why.isEmpty then none
    else some ⟨g.info.range, s!"{owner} is not well formed" ++
      String.join (why.toList.map ("\n  " ++ ·))⟩

/-- A well-formed ghost, the one at position `idx` of its module, with `funcs` the module's
functions and `ghosts` its ghosts.  Its initializer is read first, then its invariant, so that the
values get ids in the order of `Ghost.defs`.  An initializer names only the ghosts before
`idx`. -/
def ghost (funcs : Funcs env) (ghosts : Ghosts env) (idx : Nat) (g : MGhost SourceRange) :
    Result {gh : Ghost env Info // gh.WF} := do
  let h := ghostHeader g
  let gn := identText h.name
  let t ← type h.type
  let fx : FnCtx env := { funcs, ghosts }
  let run : ReadM env (Option (Late (Region env SourceRange)) ×
      Option (Late (Region env SourceRange))) := do
    let init ← h.init.mapM (ghostRegion { fx with initOf := some (idx, gn) } gn "initializer"
      (#[], t)
      (fun e => s!"the initializer of ghost @{gn} takes {e}, but an initializer takes no \
        arguments")
      (fun r => s!"the initializer of ghost @{gn} returns {r}, but the ghost holds {typeText t}"))
    let inv ← h.invariant.mapM (ghostRegion { fx with invariantOf := some gn } gn "invariant"
      (#[t], Base.Bool)
      (fun e => s!"the invariant of ghost @{gn} takes {e}, but an invariant takes the ghost's \
        contents, ({typeText t})")
      (fun r => s!"the invariant of ghost @{gn} returns {r}, but an invariant returns a \
        base.Bool"))
    checkUses
    return (init, inv)
  let ((init, inv), s) ← run.run {}
  let ids : Name → ValId := fun n => (s.values.get? n).getD ⟨0⟩
  let some ⟨names, hnames⟩ := s.values.fill? constName ⟨0⟩
    | throw ⟨h.ann, s!"no fresh name for a constant of ghost @{gn}"⟩
  let toInfo (l : Late (Region env SourceRange)) : Region env Info :=
    (l ids).map fun range => { range }
  let gh : Ghost env Info :=
    { name := nameOf gn, type := t, init := init.map toInfo, invariant := inv.map toInfo, names,
      info := { range := h.ann } }
  -- The value names' table proves the names distinct; the rest of `Ghost.WF` is decided.
  if hw : Label.Distinct (Label.exit :: gh.labels) ∧ ValDecl.idBound gh.defs ≤ gh.names.size ∧
      gh.RegionsWF ∧ gh.ContractRegionsWF ∧ Region.NoOld gh.regions ∧ gh.InvariantNamesNoGhost ∧
      gh.NoFuncRefs then
    let ⟨a, b, c, d, e, f, k⟩ := hw
    return ⟨gh, ⟨a, hnames, b, c, d, e, f, k⟩⟩
  else
    throw ((ghostDiagnostic? gh s!"ghost @{gn}").getD
      ⟨h.ann, s!"ghost @{gn} is not well formed"⟩)

/-- The ghosts `l` denotes, each well formed, the first at position `k`, or the diagnostics of all
that are not.  The diagnostics are collected in a list, as `funcsOrDiagnostics` collects them. -/
def ghostsOrDiagnostics (funcs : Funcs env) (ghosts : Ghosts env) :
    Nat → (l : List (MGhost SourceRange)) →
    Except (List ReadDiagnostic) {gs : List (Ghost env Info) // ∀ g ∈ gs, g.WF}
  | _, [] => .ok ⟨[], by simp⟩
  | k, g :: l =>
    match ghost funcs ghosts k g, ghostsOrDiagnostics funcs ghosts (k + 1) l with
    | .ok ⟨gh, hw⟩, .ok ⟨gs, hws⟩ => .ok ⟨gh :: gs, List.forall_mem_cons.mpr ⟨hw, hws⟩⟩
    | .error e, .ok _ => .error [e]
    | .ok _, .error es => .error es
    | .error e, .error es => .error (e :: es)

end Read

open Read in
/-- The module a DDM term of the Dyn dialect denotes in `env`, or the diagnostics. -/
public def Module.ofDDM {env : Env Unit} [base ≼ env] (c : DDM.Command SourceRange) :
    Except (Array ReadDiagnostic) (Module env Info) := do
  let .moduleDecl ann n ⟨_, gs⟩ ⟨_, fs⟩ := c
  let headers := fs.toList
  let ⟨funcs, _⟩ ← (NameTable.empty.insertAll? (headers.map fun f =>
      (headerName f, (headerAnn f, headerCodeType? (env := env) f)))).mapError
    fun (f, r, _) => #[⟨r, s!"function @{ToDDM.nameText f} is defined twice"⟩]
  let ghosts ← (ghostTable funcs gs).mapError (#[·])
  -- The diagnostics of every ghost and every function that do not read, the ghosts' first.
  let (⟨gl, hgwf⟩, ⟨list, _, hwf⟩) ←
    match (ghostsOrDiagnostics funcs ghosts 0 gs.toList).mapError List.toArray,
        funcList funcs ghosts headers with
    | .ok a, .ok b => pure (a, b)
    | .error e, .ok _ => throw e
    | .ok _, .error e => throw e
    | .error e₁, .error e₂ => throw (e₁ ++ e₂)
  let m : Module.Raw env Info :=
    { name := nameOf (identText n), ghosts := gl.toArray, funcs := list.toArray,
      info := { range := ann } }
  -- Reading checks the names, and that each reference names a function or a ghost at a type that
  -- fits; this decides the module's own rules again for the proof, as `Module.Raw.check` does.
  -- Each function and ghost is well formed as it is read.
  if h : m.OwnWFIn m.codeTypes m.ghostTable then
    return ⟨m, .of_own h (fun f hf => hwf f (by simpa [m] using hf))
      (fun g hg => hgwf g (by simpa [m] using hg))⟩
  else throw #[⟨ann, s!"module {identText n} is not well formed: a name is given twice, a \
    reference names no function or ghost of the module or names one at a type that does not \
    fit, or an initializer names a ghost that is not declared before its own"⟩]

namespace Read

/-- The Dyn dialect, loaded for parsing. -/
def loaded : Except String Elab.LoadedDialects := do
  let ds := DDM.Dyn_map.toList.toArray
  return { dialects := DDM.Dyn_map, dialectParsers := ← Elab.DialectParsers.ofDialects ds,
           syntaxElabMap := ← Elab.SyntaxElabMap.ofDialects ds }

/-- `line:column`, one-based line, zero-based column, of a byte position of `text`. -/
def position (fileMap : Lean.FileMap) (p : String.Pos.Raw) : String :=
  let q := fileMap.toPosition p
  s!"{q.line}:{q.column}"

/-- Parse errors, each as `file:line:column: message`. -/
def messages (fileName : String) (msgs : Array Lean.Message) : IO (Array String) :=
  msgs.mapM fun m => do return s!"{fileName}:{m.pos.line}:{m.pos.column}: {← m.data.toString}"

/-- `text` with each comment line, one that starts with `--` after its indentation, made
blank, so that positions do not move.  A printed line never starts so: a string literal
escapes its newlines. -/
def blankComments (text : String) : String :=
  "\n".intercalate <| (text.splitOn "\n").map fun l =>
    if l.trimAsciiStart.startsWith "--" then "" else l

/-- Parse `text` as one Dyn module, or give the parse errors. -/
def parse (text fileName : String) : IO (Except (Array String) (DDM.Command SourceRange)) := do
  let loader ← match loaded with
    | .ok l => pure l
    | .error e => return .error #[s!"{fileName}: {e}"]
  if mem : "Dyn" ∈ loader.dialects then
    let input := Lean.Parser.mkInputContext (blankComments text) fileName
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Elab.elabProgramRest loader leanEnv input "Dyn" mem 0 with
    | .error msgs => return .error (← messages fileName msgs)
    | .ok p =>
      let #[op] := p.commands
        | return .error #[s!"{fileName}: expected one module, found {p.commands.size}"]
      return (DDM.Command.ofAst op).mapError fun e => #[s!"{fileName}: {e}"]
  else
    return .error #[s!"{fileName}: the Dyn dialect is not loaded"]

end Read

/-- Error messages: at least one. -/
public structure Read.Errors where
  /-- The messages, in order. -/
  toArray : Array String
  nonempty : toArray.size ≠ 0

/-- The messages, a line each. -/
public instance : ToString Read.Errors := ⟨fun e => "\n".intercalate e.toArray.toList⟩

open Read in
/-- Parse `text` in the Dyn dialect and read the module it denotes in `env`: the module,
annotated with source ranges and attributes, or the diagnostics, each as
`file:line:column: message`. -/
public def Module.read (env : Env Unit) [base ≼ env] (text : String)
    (fileName : String := "<input>") :
    IO (Except Read.Errors (Module env Info)) := do
  let msgs : Array String ← match ← parse text fileName with
    | .error msgs => pure msgs
    | .ok c =>
      match Module.ofDDM (env := env) c with
      | .ok m => return .ok m
      | .error ds =>
        let fileMap := Lean.FileMap.ofString (blankComments text)
        pure (ds.map fun d => s!"{fileName}:{position fileMap d.range.start}: {d.message}")
  if h : msgs.size = 0 then return .error ⟨#[s!"{fileName}: cannot read"], by simp⟩
  else return .error ⟨msgs, h⟩

end Strata.Dyn
