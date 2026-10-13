/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataMantle.DDM
public import StrataMantle.Build
public import StrataMantle.WF
public import StrataMantle.Util.NameTable
-- Private: reading builds checked IR, which needs the environment representation at codegen.
import StrataMantle.Env.WF
import StrataMantle.FloatText
import StrataDDM.Elab
import Lean.Parser.Extension
import Std.Data.HashMap
import Std.Data.HashSet

open StrataDDM

set_option autoImplicit false

/-!
# Reading printed IR back

`Module.read env text` parses `text` in the Mantle dialect of `StrataMantle/DDM.lean` and
returns the well-formed `Module` it denotes in `env`, annotated with source ranges, or
diagnostics that say what is wrong and where.  It reads both printed forms.  `Module.ofDDM`
does the same from a DDM term.

* Lines that start with `--` are comments.
* Types and operations are looked up in `env`.  `jump`, `branch` and `unreachable` are the
  base's, and `ret(args)` is a jump to `Label.exit`.
* A literal has the type its form fixes, which must be the type where it is used.
* A constant written at a use becomes a `const` instruction just before it.
* Values get ids in printed order, so the function read is canonical (`Func.Canonical`).

A name reads back as printed unless one of its string segments is empty, is all digits or
contains `.`, or the whole name is one of the dialect's keywords.
-/

namespace Strata.Mantle

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
def typeText {env : Env Unit} {scope : Nat} (e : TypeExpr env scope) : String :=
  e.fold (fun i => s!"#{i}") fun n as =>
    if as.isEmpty then ToDDM.nameText n
    else s!"{ToDDM.nameText n}({", ".intercalate as.toList})"

/-- Types, printed for a message. -/
def typesText {env : Env Unit} (ts : Array (TypeExpr env 0)) : String :=
  s!"({", ".intercalate (ts.map typeText).toList})"

/-- What reading fails with. -/
abbrev Result (β : Type) := Except ReadDiagnostic β

/-- `n` applied to `args`, if `n` is a type of that arity. -/
def typeApp {env : Env Unit} (ann : SourceRange) (n : MName SourceRange)
    (args : Array (TypeExpr env 0)) : Result (TypeExpr env 0) :=
  let s := identText n
  match env.get? (nameOf s) with
  | some (.type (arity := a) r) =>
    if h : args.size = a then .ok (.app r ⟨args, h⟩)
    else .error ⟨ann, s!"type {s} takes {a} argument(s), given {args.size}"⟩
  | some (.insn _) => .error ⟨ann, s!"{s} is an operation, not a type"⟩
  | none => .error ⟨ann, s!"unknown type {s}"⟩

/-- A closed type. -/
def type {env : Env Unit} : MType SourceRange → Result (TypeExpr env 0)
  | .tyVar ann ⟨_, i⟩ => .error ⟨ann, s!"type variable #{i} outside a signature"⟩
  | .tyPrim ann n => typeApp ann n #[]
  | .tyApp ann n ⟨_, args⟩ => do typeApp ann n (← args.attach.mapM fun ⟨a, _⟩ => type a)

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
  | .constFunc a _ => a

/-- A literal, with `funcs` the module's functions.  Its type is the one its form fixes, and
must be `expected`. -/
def literal {env : Env Unit} [base ⊑ env] (funcs : NameTable SourceRange)
    (expected : TypeExpr env 0)
    (c : MConst SourceRange) : Result Const := do
  let k ← match c with
    | .constUnit _ => pure .unit
    | .constBool _ ⟨_, b⟩ => pure (.bool b)
    | .constInt _ i => pure (.int (int i))
    | .constFloat _ f => pure (.float (float f))
    | .constStr _ ⟨_, s⟩ => pure (.str s)
    | .constFunc ann (.funcName _ n) =>
      let f := nameOf (identText n)
      if (funcs.get? f).isSome then pure (.func f)
      else throw ⟨ann, s!"no function @{identText n} in this module"⟩
  if k.typeOf = expected then pure k
  else throw ⟨constAnn c, s!"a {typeText (k.typeOf (env := env))} literal where \
    {typeText expected} is expected"⟩

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
  type : TypeExpr env 0
  range : SourceRange
  what : String

/-- What reading a function has found so far. -/
structure State (env : Env Unit) where
  /-- The values defined so far, by name, with a slot per id: a folded constant's is empty
  until the walk ends. -/
  values : NameTable ValId := ∅
  /-- The type of each value, by id. -/
  types : Array (TypeExpr env 0) := #[]
  /-- The uses of values not defined where they are used. -/
  uses : Array (Use env) := #[]
  /-- Every label defined so far. -/
  labels : Std.HashSet Name := {}

/-- Reading a function: its state, and the first problem found. -/
abbrev ReadM (env : Env Unit) := StateT (State env) (Except ReadDiagnostic)

variable {env : Env Unit} [base ⊑ env]

/-- Stop at the problem `msg`, at `range`. -/
def fail {β : Type} (range : SourceRange) (msg : String) : ReadM env β :=
  throw ⟨range, msg⟩

/-- The name a printed value denotes. -/
def valName : MVal SourceRange → Name
  | .valName _ n => nameOf (identText n)

/-- Define the value named `n`, of type `t`, at `range`: the next id. -/
def define (range : SourceRange) (n : Name) (t : TypeExpr env 0) : ReadM env ValId := do
  let s ← get
  let id : ValId := ⟨s.types.size⟩
  let some values := s.values.insert? n id
    | fail range s!"{ToDDM.valNameText n} is defined twice"
  set { s with values, types := s.types.push t }
  return id

/-- Define a folded constant of type `t`: the next id, named after the walk. -/
def defineConst (t : TypeExpr env 0) : ReadM env ValId := do
  let s ← get
  set { s with values := s.values.reserve, types := s.types.push t }
  return ⟨s.types.size⟩

/-- A use of the value named `n` where the type `t` is expected, at `range`.  A value
defined already is checked at once; one defined further on is recorded. -/
def use (range : SourceRange) (what : String) (n : Name) (t : TypeExpr env 0) :
    ReadM env (Late ValId) := do
  let s ← get
  match s.values.get? n with
  | some id =>
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

/-- Operands at the types `expected`, one each: the constants to emit before their user,
and the ids.  `what` says whose operands they are. -/
def operands (funcs : NameTable SourceRange) (what : String) (expected : Array (TypeExpr env 0))
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
      let k ← literal funcs t c
      let id ← defineConst t
      pre := pre.push (.const ann ⟨id, k.typeOf⟩ k)
      ids := ids.push fun _ => id
  return (pre, Late.all ids)

/-- The parameter types of the blocks a transfer may name: the non-entry blocks of one body,
and its exit, `_`, which takes the body's result. -/
abbrev Scope (env : Env Unit) := Std.HashMap Name (Array (TypeExpr env 0))

/-- The scope of a body with blocks `blocks` and result `result`, and its entry block's
parameter types. -/
def scopeOf (ann : SourceRange) (result : TypeExpr env 0) (blocks : List (MBlock SourceRange)) :
    Result (Scope env × Array (TypeExpr env 0)) := do
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
def succs (funcs : NameTable SourceRange) (scope : Scope env) (ann : SourceRange) (what : String)
    (payloads : Array (Array (TypeExpr env 0))) (ss : Array (MSucc SourceRange)) :
    ReadM env (Array (Instruction env SourceRange) × Late (Array BlockValue)) := do
  if ss.size ≠ payloads.size then
    fail ann s!"{what} takes {payloads.size} successor(s), given {ss.size}"
  let mut pre := #[]
  let mut ks : Array (Late BlockValue) := #[]
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
    let (p, ids) ← operands funcs s!"{what}, successor ^{identText l}" (params.extract 0 args.size)
      args
    pre := pre ++ p
    ks := ks.push fun r => ⟨⟨target⟩, ids r⟩
  return (pre, Late.all ks)

/-- The type arguments of an application of `isig`. -/
def typeArgs (ann : SourceRange) (what : String) (isig : InsnSig env)
    (ta : Option (MTypeArgs SourceRange)) : ReadM env (Vector (TypeExpr env 0) isig.typeArgc) := do
  let ts ← match ta with
    | none => pure #[]
    | some (.typeArgs _ ⟨_, ts⟩) => ts.mapM fun t => (type t : Result _)
  if h : ts.size = isig.typeArgc then return ⟨ts, h⟩
  else fail ann s!"{what} takes {isig.typeArgc} type argument(s), given {ts.size}"

/-- The operands of an application of `isig`. -/
def callOperands (funcs : NameTable SourceRange) (ann : SourceRange) (what : String)
    (isig : InsnSig env) (targs : Vector (TypeExpr env 0) isig.typeArgc)
    (args : Option (MOperands SourceRange)) :
    ReadM env (Array (Instruction env SourceRange) × Late (Array ValId)) := do
  let ops := match args with
    | none => #[]
    | some (.operands _ ⟨_, ops⟩) => ops
  let some expected := isig.operandTypes? targs ops.size
    | fail ann s!"{what} takes {isig.argTypes.size}{if isig.variadic.isSome then " or more"
        else ""} operand(s), given {ops.size}"
  operands funcs what expected ops

/-! ## Instructions, blocks and regions -/

/-- What a function's body may refer to: the module's functions. -/
structure FnCtx where
  funcs : NameTable SourceRange

mutual

/-- Instructions, each preceded by the constants folded into it. -/
def insnList (fx : FnCtx) (scope : Scope env) :
    List (MInsn SourceRange) → ReadM env (Late (Array (Instruction env SourceRange)))
  | [] => return fun _ => #[]
  | .insnConst ann d c :: is => do
    let .valDecl _ v ty := d
    let t ← type ty
    let k ← literal fx.funcs t c
    let id ← define ann (valName v) t
    let rest ← insnList fx scope is
    return fun r => #[.const ann ⟨id, t⟩ k] ++ rest r
  | .insnApply ann d n ⟨_, ta⟩ ⟨_, args⟩ ⟨_, ss⟩ ⟨_, ⟨regions⟩⟩ :: is => do
    let s := baseControl (identText n)
    let ⟨isig, op⟩ ← (insnRef ann s : Result _)
    if isig.returnType.isNone then fail ann s!"{s} ends a block, so it defines no value"
    let targs ← typeArgs ann s isig ta
    let (pre, ids) ← callOperands fx.funcs ann s isig targs args
    let (pre₁, ks) ← succs fx.funcs scope ann s (isig.succTypes targs) ss
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
    return fun r => pre ++ pre₁ ++ #[.apply ann ⟨id, t⟩ op targs (ids r) (ks r) (rs r)] ++ rest r

/-- A terminator, preceded by the constants folded into it. -/
def term (fx : FnCtx) (scope : Scope env) : MTerm SourceRange →
    ReadM env (Array (Instruction env SourceRange) × Late (Terminator env SourceRange))
  | .termRet ann ⟨_, args⟩ => do
    let args := match args with
      | none => #[]
      | some (.operands _ ⟨_, ops⟩) => ops
    let result := (scope[Name.base]?).getD #[]
    if args.size ≠ result.size then
      fail ann s!"ret takes {result.size} operand(s), given {args.size}"
    let (pre, ids) ← operands fx.funcs "ret" result args
    return (pre, fun r => .jump ann ⟨Label.exit, ids r⟩)
  | .termApply ann n ⟨_, ta⟩ ⟨_, args⟩ ⟨_, ss⟩ ⟨_, ⟨regions⟩⟩ => do
    let s := baseControl (identText n)
    let ⟨isig, op⟩ ← (insnRef ann s : Result _)
    if isig.returnType.isSome then fail ann s!"{s} returns a value, so it cannot end a block"
    let targs ← typeArgs ann s isig ta
    let (pre, ids) ← callOperands fx.funcs ann s isig targs args
    let (pre₁, ks) ← succs fx.funcs scope ann s (isig.succTypes targs) ss
    let sigs := isig.regionTypes targs
    if sigs.length ≠ regions.length then
      fail ann s!"{s} takes {sigs.length} region(s), given {regions.length}"
    let rs ← regionList fx sigs regions
    return (pre ++ pre₁, fun r => .apply ann op targs (ids r) (ks r) (rs r))

/-- Blocks, against the scope of their body. -/
def blockList (fx : FnCtx) (scope : Scope env) :
    List (MBlock SourceRange) → ReadM env (Late (Array (Block env SourceRange)))
  | [] => return fun _ => #[]
  | .block ann l ⟨_, ps⟩ ⟨_, ⟨instrs⟩⟩ t :: bs => do
    let label := nameOf (identText l)
    defineLabel ann label
    let params ← ps.mapM valDecl
    let is ← insnList fx scope instrs
    let (pre, t) ← term fx scope t
    let rest ← blockList fx scope bs
    return fun r => #[⟨⟨label⟩, params, is r ++ pre, t r, ann⟩] ++ rest r

/-- Regions, against their signatures, one each. -/
def regionList (fx : FnCtx) : List (RegionType env) → List (MRegion SourceRange) →
    ReadM env (Late (Array (Region env SourceRange)))
  | sig :: sigs, .region ann ⟨_, ⟨blocks⟩⟩ :: rs => do
    let (scope, entry) ← (scopeOf ann sig.2 blocks : Result _)
    if entry ≠ sig.1 then
      fail ann s!"the region's entry block takes {typesText entry}, but {typesText sig.1} \
        is expected"
    let bs ← blockList fx scope blocks
    let rest ← regionList fx sigs rs
    return fun r => #[⟨bs r⟩] ++ rest r
  | _, _ => return fun _ => #[]

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

/-- The name of the folded constant chosen `k`-th: `c.k`. -/
def constName (k : Nat) : Name := .num (.str .base "c") k

/-- The name a function header gives. -/
def headerName : MFunc SourceRange → Name
  | .func _ (.funcName _ n) .. => nameOf (identText n)

/-- Where a function is. -/
def headerAnn : MFunc SourceRange → SourceRange
  | .func ann .. => ann

/-- A well-formed function, with `funcs` the module's functions and `fset` the set of their
names. -/
def func (funcs : NameTable SourceRange) (fset : NameSet) (f : MFunc SourceRange) :
    Result {fn : Func env SourceRange // fn.name = headerName f ∧ fn.WF fset} :=
  match f with
  | .func ann (.funcName _ n) ⟨_, ps⟩ retTy ⟨_, ⟨blocks⟩⟩ => do
    let retType ← type retTy
    let (scope, _) ← scopeOf ann retType blocks
    let run : ReadM env (Late (Array (Block env SourceRange))) := do
      let bs ← blockList ⟨funcs⟩ scope blocks
      checkUses
      return bs
    let (bs, s) ← run.run {}
    let ids : Name → ValId := fun n => (s.values.get? n).getD ⟨0⟩
    let blocks := bs ids
    -- The signature repeats the entry block's parameters.
    let sig ← ps.mapM fun | .valDecl _ v ty => return (valName v, ← type ty)
    let entry ← (blocks[0]?.map (·.params) |>.getD #[]).mapM fun d =>
      match s.values.slots[d.id.id]? with
      | some (some v) => pure (v, d.type)
      | _ => throw ⟨ann, s!"a parameter of @{identText n} has no name"⟩
    if sig ≠ entry then
      throw ⟨ann, s!"the parameters of @{identText n} differ from its entry block's"⟩
    let some ⟨names, hnames⟩ := s.values.fill? constName ⟨0⟩
      | throw ⟨ann, s!"no fresh name for a constant of @{identText n}"⟩
    let fn : Func env SourceRange :=
      { name := nameOf (identText n), retType, blocks, names, info := ann }
    -- The value names' table proves the names distinct; the rest of `Func.WF` is decided.
    if h : 0 < fn.blocks.size ∧ Label.Distinct (Label.exit :: fn.labels) ∧
        ValDecl.idBound fn.defs ≤ fn.names.size ∧ fn.BodyWF fset then
      return ⟨fn, rfl, ⟨h.1, h.2.1, hnames, h.2.2.1, h.2.2.2⟩⟩
    else throw ⟨ann, s!"@{identText n} is not well formed"⟩

/-- The functions `l` denotes, each well formed, or the diagnostics of all that are not. -/
def funcList (funcs : NameTable SourceRange) (fset : NameSet) : (l : List (MFunc SourceRange)) →
    Except (Array ReadDiagnostic) {fs : List (Func env SourceRange) //
      fs.map (·.name) = l.map headerName ∧ ∀ f ∈ fs, f.WF fset}
  | [] => .ok ⟨[], rfl, by simp⟩
  | f :: l =>
    match func funcs fset f, funcList funcs fset l with
    | .ok ⟨fn, hn, hw⟩, .ok ⟨fs, hs, hws⟩ =>
      .ok ⟨fn :: fs, by simp [hn, hs], List.forall_mem_cons.mpr ⟨hw, hws⟩⟩
    | .error e, .ok _ => .error #[e]
    | .ok _, .error es => .error es
    | .error e, .error es => .error (#[e] ++ es)

end Read

open Read in
/-- The module a DDM term of the Mantle dialect denotes in `env`, or the diagnostics. -/
public def Module.ofDDM {env : Env Unit} [base ⊑ env] (c : DDM.Command SourceRange) :
    Except (Array ReadDiagnostic) (Module env SourceRange) := do
  let .moduleDecl ann n ⟨_, fs⟩ := c
  let headers := fs.toList
  let ⟨funcs, hfuncs⟩ ← (NameTable.empty.insertAll? (headers.map fun f => (headerName f, headerAnn f))).mapError
    fun (f, r) => #[⟨r, s!"function @{ToDDM.nameText f} is defined twice"⟩]
  let fset := (NameSet.of? (headers.map headerName).toArray).getD ∅
  let ⟨list, hnames, hwf⟩ ← funcList (env := env) funcs fset headers
  let m : Module.Raw env SourceRange := { name := nameOf (identText n), funcs := list.toArray, info := ann }
  have hm : m.funcNames = (headers.map headerName).toArray := by
    simp [m, Module.Raw.funcNames, Array.mapK_eq_map_fun, hnames]
  have hnodup : (headers.map headerName).Nodup := by
    simpa [hfuncs, Function.comp_def] using funcs.nodup
  -- Well formed: the function names are distinct by their table, and each function is well
  -- formed as it is read.
  return ⟨m, { funcNamesUnique := by simpa [hm] using hnodup
               funcs := fun f hf => by
                 simpa [Module.Raw.funcSet, hm] using hwf f (by simpa [m] using hf) }⟩

namespace Read

/-- The Mantle dialect, loaded for parsing. -/
def loaded : Except String Elab.LoadedDialects := do
  let ds := DDM.Mantle_map.toList.toArray
  return { dialects := DDM.Mantle_map, dialectParsers := ← Elab.DialectParsers.ofDialects ds,
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

/-- Parse `text` as one Mantle module, or give the parse errors. -/
def parse (text fileName : String) : IO (Except (Array String) (DDM.Command SourceRange)) := do
  let loader ← match loaded with
    | .ok l => pure l
    | .error e => return .error #[s!"{fileName}: {e}"]
  if mem : "Mantle" ∈ loader.dialects then
    let input := Lean.Parser.mkInputContext (blankComments text) fileName
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Elab.elabProgramRest loader leanEnv input "Mantle" mem 0 with
    | .error msgs => return .error (← messages fileName msgs)
    | .ok p =>
      let #[op] := p.commands
        | return .error #[s!"{fileName}: expected one module, found {p.commands.size}"]
      return (DDM.Command.ofAst op).mapError fun e => #[s!"{fileName}: {e}"]
  else
    return .error #[s!"{fileName}: the Mantle dialect is not loaded"]

end Read

open Read in
/-- Parse `text` in the Mantle dialect and read the module it denotes in `env`: the module,
annotated with source ranges, or the diagnostics, each as `file:line:column: message`. -/
public def Module.read (env : Env Unit) [base ⊑ env] (text : String)
    (fileName : String := "<input>") :
    IO (Except Build.Errors (Module env SourceRange)) := do
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

end Strata.Mantle
