/-
Ordered, first-order plans for the rule interpreter.

Plans are data. Only the executor and its explicit Services boundary contain
Lean functions over analysis states.
-/
import Pylate.Transfers.Flow
import Pylate.Tables.ShapePolicy

namespace Pylate.RuleDriven

open Pylate

-- ---------------------------------------------------------------- signatures

inductive ParamKind
  | positionalOnly
  | positionalOrKeyword
  | keywordOnly
deriving Repr, Inhabited, BEq

structure Parameter where
  name     : String
  kind     : ParamKind
  required : Bool := true
deriving Repr, Inhabited

structure Signature where
  parameters : List Parameter := []
  varPos     : Bool := false
  varKw      : Bool := false
deriving Repr, Inhabited

structure CallInput where
  positional : List AbsVal := []
  keywords   : List (String × AbsVal) := []
deriving Repr, Inhabited

structure BoundCall where
  parameters : List (String × AbsVal) := []
  varPos     : List AbsVal := []
  varKw      : List (String × AbsVal) := []
  input      : CallInput := {}
deriving Repr, Inhabited

structure BindError where
  detail : String
deriving Repr, Inhabited

def Signature.bind (signature : Signature) (input : CallInput) :
    Except BindError BoundCall := Id.run do
  let positionalParameters := signature.parameters.filter fun parameter =>
    parameter.kind != .keywordOnly
  if input.positional.length > positionalParameters.length && !signature.varPos then
    return .error ⟨s!"expected at most {positionalParameters.length} positional arguments, got {input.positional.length}"⟩
  let mut assigned := (positionalParameters.zip input.positional).map fun
    (parameter, value) => (parameter.name, value)
  let mut extraKeywords : List (String × AbsVal) := []
  let mut seenKeywords : List String := []
  for (name, value) in input.keywords do
    if seenKeywords.contains name then
      return .error ⟨s!"duplicate keyword argument '{name}'"⟩
    seenKeywords := name :: seenKeywords
    match signature.parameters.find? (·.name == name) with
    | some parameter =>
      match parameter.kind with
      | .positionalOnly =>
        if signature.varKw then
          extraKeywords := extraKeywords ++ [(name, value)]
        else
          return .error ⟨s!"positional-only argument '{name}' passed by keyword"⟩
      | .positionalOrKeyword | .keywordOnly =>
        if assigned.any (·.1 == name) then
          return .error ⟨s!"multiple values for argument '{name}'"⟩
        assigned := assigned ++ [(name, value)]
    | none =>
      if signature.varKw then
        extraKeywords := extraKeywords ++ [(name, value)]
      else
        return .error ⟨s!"unexpected keyword argument '{name}'"⟩
  match signature.parameters.find? fun parameter =>
      parameter.required && !(assigned.any (·.1 == parameter.name)) with
  | some missing =>
    return .error ⟨s!"missing required argument '{missing.name}'"⟩
  | none =>
    return .ok {
      parameters := assigned
      varPos := input.positional.drop positionalParameters.length
      varKw := extraKeywords
      input
    }

def Signature.errors (signature : Signature) : List String := Id.run do
  let mut errors : List String := []
  let mut names : List String := []
  let mut previousRank := 0
  let mut optionalPositional := false
  for parameter in signature.parameters do
    if names.contains parameter.name then
      errors := errors ++ [s!"duplicate parameter '{parameter.name}'"]
    names := parameter.name :: names
    let rank := match parameter.kind with
      | .positionalOnly => 0
      | .positionalOrKeyword => 1
      | .keywordOnly => 2
    if rank < previousRank then
      errors := errors ++ ["parameter kinds are out of Python binding order"]
    previousRank := rank
    if parameter.kind != .keywordOnly then
      if optionalPositional && parameter.required then
        errors := errors ++ [s!"required parameter '{parameter.name}' follows a default"]
      optionalPositional := optionalPositional || !parameter.required
  return errors

-- ------------------------------------------------------- argument contracts

/-- A builtin argument's runtime semantic contract. This is closed data; the
    executor is installed through `Services.applyContracts`. -/
inductive ArgContract
  | any
  | runtimeTags (tags : Fset Tag)
  | optional (inner : ArgContract)
  | supportsIndex
  | iterable
  | hashable
  | string
  | stringOrTupleOfStrings
  | callableOrNone
  | mappingOrIterablePairs
  /-- Iterate, then require every yielded element to satisfy `inner`. -/
  | iterableOf (inner : ArgContract)
  /-- Truth conversion, running `__bool__`/`__len__` and their exceptions. -/
  | truthValue
  /-- A set element: hashable, except that CPython looks a `set` up as its
      frozenset equivalent instead of raising TypeError. -/
  | setElement
  /-- The operation calls this method on the argument; its effects and
      exceptions belong to the call. -/
  | invokesHook (method : String)
  /-- Consume a mapping or iterable of pairs into the receiver. -/
  | mappingPairsInto
  /-- A padding fill: exactly one character, else TypeError. -/
  | fillCharacter
  /-- A separator, of the receiver's own string kind: `str.split` wants a `str`
      and `bytes.split` wants a `bytes`. An empty separator raises ValueError
      rather than TypeError, which is why this is not `runtimeTags`.

      The kind is a parameter because it was not: a single str-only separator
      made `b.split(b" ")` a TypeError with no normal completion, so a call
      CPython answers with a list looked like unreachable code. -/
  | separatorString (kind : Tag)
  | recursiveAnnotation (annotation : Ann)
deriving Repr, Inhabited

def ArgContract.label : ArgContract -> String
  | .any => "Any"
  | .runtimeTags tags =>
    s!"RuntimeTags({",".intercalate (tags.map Tag.render)})"
  | .optional inner => s!"Optional({inner.label})"
  | .supportsIndex => "SupportsIndex"
  | .iterable => "Iterable"
  | .hashable => "Hashable"
  | .string => "String"
  | .stringOrTupleOfStrings => "StringOrTupleOfStrings"
  | .callableOrNone => "CallableOrNone"
  | .mappingOrIterablePairs => "MappingOrIterablePairs"
  | .iterableOf inner => s!"IterableOf({inner.label})"
  | .truthValue => "TruthValue"
  | .setElement => "SetElement"
  | .invokesHook method => s!"Invokes({method})"
  | .mappingPairsInto => "MappingOrIterablePairsInto"
  | .fillCharacter => "FillCharacter"
  | .separatorString kind => s!"Separator({kind.render})"
  | .recursiveAnnotation _ => "RecursiveAnnotation"

structure ContractArgument where
  name     : String
  contract : ArgContract
  value    : AbsVal
  /-- The destination of a consuming contract, normally the receiver. -/
  target   : AbsVal := AbsVal.bot
deriving Repr, Inhabited

structure ContractArguments where
  /-- Converted values in declaration order with their shared post-contract
      state. Absence means no normal entry to the rule body. -/
  normal : Option (List (String × AbsVal) × AState) := none
  raised : RaisedFlow := {}
deriving Repr, Inhabited

-- ---------------------------------------------------------------- expressions

inductive ValueRef
  | receiver
  | parameter (name : String)
  | argument (index : Nat)
  | keyword (name : String)
  | local (index : Nat)
  /-- The result of the child evaluated at this position, so a plan can name a
      subterm's value without the rule knowing how it was produced. -/
  | evaluated (index : Nat)
deriving Repr, Inhabited, BEq

/-- A node's unevaluated children. A syntax rule must be able to name them
    before they are values, which is what `Plan` could not express: it could
    invoke operations but not evaluate subterms, so the recursion had to stay in
    Lean. -/
inductive Subterm
  | expr (e : Expr)
  | target (t : Target)
  | body (b : List Stmt)
  | ann (a : Ann)
deriving Inhabited

/-- Non-value data a node carries: an operator, a field or variable name, a
    flag. Kept beside the subterms so one key can serve every node of a kind
    with its operator as data, rather than one key per operator. -/
inductive Attr
  | constant (value : Const)
  /-- A literal subscript index, which proves a tuple read in bounds and gives a
      mapping store its own per-key cell. -/
  | index (value : Nat)
  | binOp (op : BinOp)
  | cmpOp (op : CmpOp)
  | unOp (op : UnOp)
  | name (x : String)
  | flag (b : Bool)
deriving Inhabited

structure Frame where
  receiver : AbsVal := AbsVal.bot
  call     : BoundCall := {}
  locals   : List AbsVal := []
  /-- The node's children, in source order. -/
  subterms : List Subterm := []
  /-- Operator, field, or variable name. -/
  attributes : List (String × Attr) := []
  /-- Results of the children evaluated so far, in evaluation order. -/
  evaluated : List AbsVal := []
deriving Inhabited

def replaceAt (values : List AbsVal) (index : Nat) (value : AbsVal) : List AbsVal :=
  match values, index with
  | [], _ => []
  | _ :: rest, 0 => value :: rest
  | old :: rest, index + 1 => old :: replaceAt rest index value

def replaceNamed (values : List (String × AbsVal)) (name : String)
    (value : AbsVal) : List (String × AbsVal) :=
  values.map fun (oldName, oldValue) =>
    if oldName == name then (oldName, value) else (oldName, oldValue)

def Frame.read (frame : Frame) : ValueRef -> AbsVal
  | .evaluated index => frame.evaluated[index]?.getD AbsVal.bot
  | .receiver => frame.receiver
  | .parameter name =>
    (frame.call.parameters.find? (·.1 == name)).map (·.2) |>.getD AbsVal.bot
  | .argument index => frame.call.input.positional[index]?.getD AbsVal.bot
  | .keyword name =>
    (frame.call.input.keywords.find? (·.1 == name)).map (·.2) |>.getD AbsVal.bot
  | .local index => frame.locals[index]?.getD AbsVal.bot

def Frame.write (frame : Frame) (source : ValueRef) (value : AbsVal) : Frame :=
  match source with
  | .evaluated index =>
    { frame with evaluated := replaceAt frame.evaluated index value }
  | .receiver => { frame with receiver := value }
  | .parameter name =>
    { frame with call := { frame.call with
        parameters := replaceNamed frame.call.parameters name value } }
  | .argument index =>
    { frame with call := { frame.call with input := { frame.call.input with
        positional := replaceAt frame.call.input.positional index value } } }
  | .keyword name =>
    { frame with call := { frame.call with input := { frame.call.input with
        keywords := replaceNamed frame.call.input.keywords name value } } }
  | .local index => { frame with locals := replaceAt frame.locals index value }

def Frame.push (frame : Frame) (value : AbsVal) : Frame :=
  { frame with locals := value :: frame.locals }

inductive ValueExpr
  | bottom
  | none
  | bool
  | int
  | str
  | bytes
  | any
  | notImplemented
  | read (source : ValueRef)
  | elements (source : ValueRef)
  | argumentElements
  /-- The smashed summary of every evaluated child, which is what a collection
      literal's element cell holds. -/
  | joinEvaluated
  /-- The value a literal constant denotes, named by attribute. A constant is not
      an operation and has no children; its value is the node's own data. -/
  | constantOf (attrName : String)
  | join (left right : ValueExpr)
  | without (value : ValueExpr) (tags : Fset Tag)
  | restrict (value : ValueExpr) (tags : Fset Tag)
deriving Repr, Inhabited

partial def ValueExpr.eval (expression : ValueExpr) (frame : Frame)
    (state : AState) : AbsVal :=
  match expression with
  | .constantOf name =>
    match (frame.attributes.find? (·.1 == name)).map (·.2) with
    | some (Attr.constant value) => constV value
    -- An attribute the node does not carry yields bottom, which the rule
    -- compiler rejects statically, so this is unreachable for a compiled rule.
    | _ => AbsVal.bot
  | .joinEvaluated =>
    frame.evaluated.foldl AbsVal.join AbsVal.bot
  | .bottom => AbsVal.bot
  | .none => V [.tnone]
  | .bool => V [.tbool]
  | .int => V [.tint]
  | .str => V [.tstr]
  | .bytes => V [.tbytes]
  | .any => anyV
  | .notImplemented => V [.tnotimpl]
  | .read source => frame.read source
  | .elements source => elemOf state (frame.read source)
  | .argumentElements =>
    frame.call.input.positional.foldl
      (fun out value => out.join (elemOf state value)) AbsVal.bot
  | .join left right => (left.eval frame state).join (right.eval frame state)
  | .without value tags => (value.eval frame state).withoutTags tags
  | .restrict value tags => (value.eval frame state).restrictTags tags

-- ------------------------------------------------------------- refinements

/-- What a rule can ask about a declared TypedDict field. These four are what
    the hand-written `shape-break` sites branch on. -/
inductive FieldPredicate
  | declared
  | required
  | readOnly
  /-- Declared, but not proven present in this object: the key may be absent. -/
  | mayBeAbsent
deriving Repr, Inhabited, BEq

inductive Condition
  | hasTag (source : ValueRef) (tag : Tag)
  | hashable (value : ValueExpr)
  | definitelyNonempty (value : ValueExpr)
  /-- Whether the call supplied this optional parameter. -/
  | supplied (name : String)
  /-- A proof that the collection has no elements. -/
  | definitelyEmpty (value : ValueExpr)
  /-- Whether the node had any children to evaluate. A variadic literal needs it
      and no value-level condition can give it: `[]` allocates Empty and `[x]`
      NonEmpty, and the child count is a property of the node. -/
  | anyEvaluated
  /-- A predicate on the TypedDict field the named key attribute resolves to,
      against the receiver's declared class. False when the receiver is not a
      TypedDict or the key is dynamic, so a rule that branches on this cannot
      accidentally treat an unknown key as a declared one. -/
  | field (attrName : String) (predicate : FieldPredicate)
deriving Repr, Inhabited

structure Split where
  yes : Option Frame := none
  no  : Option Frame := none
deriving Inhabited

def keepTags (value : AbsVal) (keep : Tag -> Bool) : AbsVal :=
  { value with tags := value.tags.filter keep } |>.reduce

def frameWithValue? (frame : Frame) (source : ValueRef)
    (value : AbsVal) : Option Frame :=
  if value.isBot then none else some (frame.write source value)

def tagUnhashable : Tag -> Bool
  | .tlist | .tdict | .tset => true
  | _ => false

def tagHashabilityUnknown : Tag -> Bool
  | .tobj _ | .tany => true
  | _ => false

/-- Every location the value may denote is definitely nonempty. A value with no
    locations does not qualify: nothing is known to be nonempty. -/
def valueDefinitelyNonempty (value : AbsVal) (state : AState) : Bool :=
  !value.locs.isEmpty &&
    value.locs.all (fun location =>
      state.emptinessGet location == .nonempty)

/-- The declared TypedDict field a key attribute names, against the receiver's
    class. `none` when the receiver is not a TypedDict or the key is not a
    literal, so a rule branching on a field predicate cannot mistake an unknown
    key for a declared one. -/
def declaredField (classes : ClassTable) (frame : Frame)
    (attrName : String) : Option FieldDecl :=
  let key := match (frame.attributes.find? (·.1 == attrName)).map (·.2) with
    | some (.name key) => some key
    | some (.constant (.cstr key)) => some key
    | _ => none
  match key with
  | none => none
  | some key =>
    frame.receiver.locs.findSome? fun location =>
      match location.cls with
      | .td typeName =>
        match classes.getCls? typeName with
        | some info => if info.isTypedDict then info.fields.find? (·.name == key)
                       else none
        | none => none
      | _ => none

def Condition.split (condition : Condition) (classes : ClassTable)
    (frame : Frame) (state : AState) : Split :=
  match condition with
  | .field attrName predicate =>
    let holds := match declaredField classes frame attrName with
      | none => false
      | some decl =>
        match predicate with
        | .declared => true
        | .required => decl.required
        | .readOnly => decl.readOnly
        | .mayBeAbsent =>
          -- Presence is cell existence, the same rule the join and the
          -- entailment check use. A declared field with no cell may be absent.
          frame.receiver.locs.any fun location =>
            !state.heapHas location (.literalKey decl.name) ||
              (state.heapGet location (.literalKey decl.name)).tags.contains
                Tag.tmissing
    if holds then ⟨some frame, none⟩ else ⟨none, some frame⟩
  | .anyEvaluated =>
    if frame.evaluated.isEmpty then ⟨none, some frame⟩ else ⟨some frame, none⟩
  | .hasTag source tag =>
    let value := frame.read source
    let yes := keepTags value fun candidate =>
      candidate == tag || candidate == .tany
    let no := keepTags value fun candidate =>
      candidate != tag || candidate == .tany
    ⟨frameWithValue? frame source yes, frameWithValue? frame source no⟩
  | .hashable expression =>
    let value := expression.eval frame state
    if value.isBot then
      -- An empty element summary is vacuously hashable, as in set().
      ⟨some frame, none⟩
    else
      let yes := keepTags value fun tag =>
        !tagUnhashable tag || tagHashabilityUnknown tag
      let no := keepTags value fun tag =>
        tagUnhashable tag || tagHashabilityUnknown tag
      ⟨if yes.isBot then none else some frame,
        if no.isBot then none else some frame⟩
  | .definitelyNonempty expression =>
    if valueDefinitelyNonempty (expression.eval frame state) state then
      ⟨some frame, none⟩
    else
      ⟨none, some frame⟩
  | .supplied name =>
    if (frame.call.parameters.find? (·.1 == name)).isSome then
      ⟨some frame, none⟩
    else
      ⟨none, some frame⟩
  | .definitelyEmpty expression =>
    let value := expression.eval frame state
    if !value.locs.isEmpty &&
        value.locs.all (fun location =>
          state.emptinessGet location == .empty) then
      ⟨some frame, none⟩
    else
      ⟨none, some frame⟩

-- -------------------------------------------------------------------- plans

/-- Which cell a mutation names.

`CellSelector` alone is a fixed constructor, so a rule could only ever name a
cell whose identity is baked into the rule. The per-key cell of a mapping store
is not like that: its name comes from the program, and it is already in the
frame's attributes -- `Operation.resolve` reads the same attributes to pick up a
literal subscript index. Reusing that mechanism keeps the fact stated in one
place rather than passed around. -/
inductive CellRef
  | fixed (cell : CellSelector)
  /-- The per-key cell whose key is the named frame attribute, falling back to
      the given summary cell when that attribute is absent or is not a literal.
      A dynamic key has no single per-key cell, and dropping the write would be
      unsound, so it lands on the summary exactly as a dynamic store does. -/
  | literalKeyOf (attrName : String) (fallback : CellSelector)
deriving Repr, Inhabited

/-- The cell a `CellRef` denotes. Total: an unresolvable key yields the declared
    summary cell rather than nothing, so a mutation can never silently vanish. -/
def CellRef.resolve (reference : CellRef)
    (attributes : List (String × Attr)) : CellSelector :=
  match reference with
  | .fixed cell => cell
  | .literalKeyOf attrName fallback =>
    match (attributes.find? (·.1 == attrName)).map (·.2) with
    | some found =>
      match found with
      | .name key => .literalKey key
      | .constant (.cstr key) => .literalKey key
      | _ => fallback
    | none => fallback

/-- Static validity, and static rendering, so the validator and the compiler ask
    a `CellRef` the same questions they asked a `CellSelector`. Every cell a
    reference *can* resolve to must be one the class can hold: the choice happens
    at analysis time and validation runs before, so checking only one branch
    would let the other through. -/
def CellRef.validFor (reference : CellRef) (cls : LocCls) : Bool :=
  match reference with
  | .fixed cell => cell.validFor cls
  | .literalKeyOf _ fallback =>
    (CellSelector.literalKey "").validFor cls && fallback.validFor cls

def CellRef.render : CellRef -> String
  | .fixed cell => cell.render
  | .literalKeyOf attrName fallback =>
    s!"key from {attrName}, else {fallback.render}"

/-- Whether a reference can land on a given cell, which is how the emptiness
    condition catches a legacy `nonempty` write through either branch. -/
def CellRef.canReach (reference : CellRef) (cell : CellSelector) : Bool :=
  match reference with
  | .fixed only => only == cell
  | .literalKeyOf _ fallback =>
    fallback == cell || match cell with | .literalKey _ => true | _ => false

inductive Mutation
  | grow (target : ValueExpr) (cls : LocCls)
      (cell : CellRef) (value : ValueExpr)
  | clear (target : ValueExpr) (cls : LocCls) (cell : CellRef)
  /-- Declare a collection's emptiness postcondition. -/
  | emptiness (target : ValueExpr) (cls : LocCls) (value : Emptiness)
  /-- Declare that the collection holds exactly as many elements as the node has
      children. Only sound where the constructor preserves the count: a `list`
      does, a `set` and a `dict` do not, since `{1, 1}` has one element. -/
  | sizeOfChildren (target : ValueExpr) (cls : LocCls)
  | bind (name : String) (value : ValueExpr)
  | unbind (name : String)
deriving Repr, Inhabited

inductive RaiseKind
  | machine
  | user
  /-- Raised and consumed inside one transfer, so it is never an outcome of the
      enclosing statement and never reaches the abort policy. -/
  | internal
deriving Repr, Inhabited, BEq

structure RaiseSpec where
  kind    : RaiseKind
  classes : Fset String
  value   : Option ValueExpr := none
  /-- Raise the classes this value denotes, as `generator.throw(exc)` does. -/
  classesOf : Option ValueRef := none
deriving Repr, Inhabited

def RaiseSpec.machine (cls : String) : RaiseSpec :=
  { kind := .machine, classes := [cls] }

/-- A signal a transfer raises and catches itself, such as the exhaustion that
    ends an iteration. -/
def RaiseSpec.internal (cls : String) : RaiseSpec :=
  { kind := .internal, classes := [cls] }

/-- Re-raise whatever exception object the operand denotes. -/
def RaiseSpec.ofOperand (name : String) : RaiseSpec :=
  { kind := .user, classes := [], classesOf := some (.parameter name) }

inductive DictMethod
  | get
  | pop
  | keys
  | values
  | items
  | setdefault
  | update
  | copy
  | fromkeys
  | clear
deriving Repr, Inhabited, BEq

def DictMethod.name : DictMethod -> String
  | .get => "get"
  | .pop => "pop"
  | .keys => "keys"
  | .values => "values"
  | .items => "items"
  | .setdefault => "setdefault"
  | .update => "update"
  | .copy => "copy"
  | .fromkeys => "fromkeys"
  | .clear => "clear"

inductive OpaqueBuiltinMethod
  | dictPopitem
  | setDifferenceUpdate
  | setIntersectionUpdate
  | setSymmetricDifferenceUpdate
  | strEncode
  | strFormatMap
  | strMaketrans
  | strPartition
  | strRpartition
  | strTranslate
  | genClose
  | genSend
  | genThrow
deriving Repr, Inhabited, BEq

/-- The exceptions an unmodeled builtin may still raise, from CPython 3.13.
    An opaque result is not a licence to drop its failures. -/
def OpaqueBuiltinMethod.documentedExceptions :
    OpaqueBuiltinMethod -> List String
  | .dictPopitem => ["KeyError"]
  | .setDifferenceUpdate | .setIntersectionUpdate
  | .setSymmetricDifferenceUpdate => ["TypeError"]
  | .strEncode => ["TypeError", "LookupError", "UnicodeEncodeError"]
  | .strFormatMap =>
    ["TypeError", "KeyError", "IndexError", "ValueError", "AttributeError"]
  | .strMaketrans => ["TypeError", "ValueError"]
  | .strPartition | .strRpartition => ["TypeError", "ValueError"]
  | .strTranslate => ["TypeError", "LookupError", "ValueError"]
  | .genClose => ["RuntimeError"]
  | .genSend | .genThrow => ["StopIteration", "RuntimeError", "TypeError"]

def OpaqueBuiltinMethod.receiver : OpaqueBuiltinMethod -> Tag
  | .dictPopitem => .tdict
  | .setDifferenceUpdate | .setIntersectionUpdate
  | .setSymmetricDifferenceUpdate => .tset
  | .strEncode | .strFormatMap | .strMaketrans | .strPartition
  | .strRpartition | .strTranslate => .tstr
  | .genClose | .genSend | .genThrow => .tgen

def OpaqueBuiltinMethod.name : OpaqueBuiltinMethod -> String
  | .dictPopitem => "popitem"
  | .setDifferenceUpdate => "difference_update"
  | .setIntersectionUpdate => "intersection_update"
  | .setSymmetricDifferenceUpdate => "symmetric_difference_update"
  | .strEncode => "encode"
  | .strFormatMap => "format_map"
  | .strMaketrans => "maketrans"
  | .strPartition => "partition"
  | .strRpartition => "rpartition"
  | .strTranslate => "translate"
  | .genClose => "close"
  | .genSend => "send"
  | .genThrow => "throw"

inductive Operation
  | function (name : String)
  | method (name : String)
  | dictMethod (method : DictMethod)
  | opaqueBuiltinMethod (method : OpaqueBuiltinMethod)
  | builtinLen
  | builtinStr
  | builtinRepr
  | builtinIter
  | builtinNext
  | attributeRead (name : String)
  | attributeWrite (name : String)
  /-- An item read or write whose literal key and index travel with it. Carrying
      them here rather than deriving them in the dispatcher is what makes a plan a
      complete description of the node: `pair[1]` reads slot `t:1` and proves the
      read in bounds, and `d["k"] = v` records a `k:k` cell a later read can prove
      present. -/
  | itemReadAt (literalKey : Option String) (literalIndex : Option Nat)
  | itemWriteAt (literalKey : Option String) (literalIndex : Option Nat)
  | itemRead
  | itemWrite
  | truth
  | binary (operator : BinOp)
  | unary (operator : UnOp)
  | compare (operator : CmpOp)
  | membership (negated : Bool)
  /-- The operator is frame data, named by attribute, so one syntax plan serves
      every operator of its kind instead of one key per operator. Resolved
      against `frame.attributes` when the invocation runs. -/
  | attributeReadOfAttr (attrName : String)
  | attributeWriteOfAttr (attrName : String)
  | binaryOfAttr (attrName : String)
  | compareOfAttr (attrName : String)
  | unaryOfAttr (attrName : String)
deriving Repr, Inhabited

/-- Resolve an operator named by attribute against the frame. An attribute the
    node does not carry is a rule error rather than a default: defaulting would
    silently analyse `a - b` as `a + b`. -/
def Operation.resolve (operation : Operation)
    (attributes : List (String × Attr)) : Option Operation :=
  match operation with
  | .binaryOfAttr name =>
    match (attributes.find? (·.1 == name)).map (·.2) with
    | some (Attr.binOp op) => some (.binary op)
    | _ => none
  | .compareOfAttr name =>
    match (attributes.find? (·.1 == name)).map (·.2) with
    -- `in` and `not in` are comparison operators syntactically but go to the
    -- membership protocol, so the operator decides the operation here rather
    -- than a condition deciding it in the plan.
    | some (Attr.cmpOp .inOp) => some (.membership false)
    | some (Attr.cmpOp .notInOp) => some (.membership true)
    | some (Attr.cmpOp op) => some (.compare op)
    | _ => none
  | .attributeReadOfAttr name =>
    match (attributes.find? (·.1 == name)).map (·.2) with
    | some (Attr.name field) => some (.attributeRead field)
    | _ => none
  | .attributeWriteOfAttr name =>
    match (attributes.find? (·.1 == name)).map (·.2) with
    | some (Attr.name field) => some (.attributeWrite field)
    | _ => none
  -- The literal key and index are read from the frame, so the operation carries
  -- what the node knows and the dispatcher derives nothing.
  | .itemReadAt _ _ =>
    some (.itemReadAt
      (match (attributes.find? (·.1 == "literalKey")).map (·.2) with
       | some (Attr.name key) => some key | _ => none)
      (match (attributes.find? (·.1 == "literalIndex")).map (·.2) with
       | some (Attr.index value) => some value | _ => none))
  | .itemWriteAt _ _ =>
    some (.itemWriteAt
      (match (attributes.find? (·.1 == "literalKey")).map (·.2) with
       | some (Attr.name key) => some key | _ => none)
      (match (attributes.find? (·.1 == "literalIndex")).map (·.2) with
       | some (Attr.index value) => some value | _ => none))
  | .unaryOfAttr name =>
    match (attributes.find? (·.1 == name)).map (·.2) with
    | some (Attr.unOp op) => some (.unary op)
    | _ => none
  | other => some other

structure Invocation where
  operation : Operation
  receiver  : Option ValueExpr := none
  arguments : List ValueExpr := []
  keywords  : List (String × ValueExpr) := []
  forwardInput : Bool := false
deriving Repr, Inhabited

inductive Plan
  | normal (value : ValueExpr)
  | stop
  | raise (spec : RaiseSpec)
  | bind (first next : Plan)
  | mutate (effect : Mutation) (next : Plan)
  | letValue (value : ValueExpr) (next : Plan)
  | allocate (cls : LocCls)
      (initializers : List (CellSelector × ValueExpr)) (next : Plan)
  | require (condition : Condition) (failure : RaiseSpec) (next : Plan)
  | branch (condition : Condition) (yes no : Plan)
  | truthBranch (source : ValueRef) (truthy falsy : Plan)
  | alternatives (plans : List Plan)
  | invoke (call : Invocation) (next : Plan)
  | protocolChain (candidates : List Plan) (fallback : Plan)
  /-- Evaluate subterm `index` through the engine's recursive evaluator from the
      current state. On normal completion its result is appended to
      `frame.evaluated` and the post-state threads into `next`. A raised
      partition becomes part of this plan's flow and `next` does not run for it,
      so left-to-right order and abandon-on-exception hold by construction for
      every syntax rule instead of being re-established in each `match` arm. -/
  | evalChild (index : Nat) (next : Plan)
  /-- The same for every remaining subterm from `index`, in order. Covers the
      variadic nodes: the collection literals, call arguments, f-string parts,
      and `boolop` values. -/
  | evalChildren (index : Nat) (next : Plan)
  /-- An explicit, counted escape hatch to a named Lean transfer, for the nodes
      ENGINE.md section 3 states should stay engine code. -/
  | engine (name : String)
  /-- Finish with an abnormal statement completion rather than a value.
      `Plan` returns a `Flow`, which has room for a normal completion and raised
      ones but not for `return`, `break` or `continue`, so a statement could not
      be a plan at all. These three make the remaining two expressible; the
      executor lifts them into the `Completion` the statement kernel consumes.

      `returnValue` names what to return, and `.none` covers a bare `return`. -/
  | returnWith (value : ValueExpr)
  | breakLoop
  | continueLoop
  /-- Evaluate subterm `index`, test its truth through the subterm-keyed service,
      refine the state syntactically, and run each side on its own refined state.
      This is what every branching node needs and what `truthBranch` cannot give,
      because `truthBranch` names a value and the refinement names syntax. -/
  | refineBranch (index : Nat) (truthy falsy : Plan)
  /-- Record an obligation, then continue. -/
  | obligate (kind detail : String) (next : Plan)
  /-- Run body child `index`. Its four abnormal completions become the plan's;
      only its normal state threads into `next`. -/
  | evalBody (index : Nat) (next : Plan)
  /-- Allocate `cls`, write each evaluated child to its own positional slot, and
      set the element summary from their join. `allocate` takes a fixed
      initializer list, and a tuple's arity is a property of the node. -/
  | allocateSlots (cls : LocCls) (next : Plan)
  /-- Allocate `cls` from evaluated key/value pairs: even children are keys, odd
      ones values. Literal keys additionally get their own cell, which is what
      lets a later read prove the key present. -/
  | allocateMapping (cls : LocCls) (next : Plan)
  /-- Bind `value` to the name this attribute holds: the store a target
      performs. -/
  | storeName (attrName : String) (value : ValueExpr) (next : Plan)
  /-- Bind `value` to every target child from `index`, which is what a tuple
      target does with the element summary of the value it unpacks. -/
  | bindEach (index : Nat) (value : ValueExpr) (next : Plan)
  /-- Read the name this attribute holds, with its unbound partitions. A name is
      not an operation: the read can raise, and which of `NameError` and
      `UnboundLocalError` it raises depends on scope the engine tracks. -/
  | readName (attrName : String) (next : Plan)
  /-- Delete target child `index`, then continue. -/
  | deleteTarget (index : Nat) (next : Plan)
  /-- Bind `value` to target child `index`, then continue. Python evaluates the
      right-hand side before binding, and a failing right-hand side performs no
      binding -- both facts are visible in a plan that evaluates the value child
      first and names it here. -/
  | bindTarget (index : Nat) (value : ValueExpr) (next : Plan)
deriving Repr, Inhabited

structure Services where
  invoke : Pos -> Operation -> Option AbsVal -> List AbsVal ->
    List (String × AbsVal) -> AState -> M Flow
  truth : Pos -> AbsVal -> AState -> M TruthFlow
  /-- Recursive evaluation of one of the node's children. Fails closed: without
      an installed evaluator a syntax plan cannot evaluate its subterms, so it
      must not proceed as though it had. -/
  evalSubterm : Pos -> Subterm -> AState -> M Flow :=
    fun position _ _ => do
      oblige position "subterm-evaluator-missing"
        "no recursive evaluator installed: a syntax plan cannot evaluate its children"
      pure {}
  /-- Truth-test a subterm's value. Distinct from `truth`, which takes only a
      value: the kernel keys a truth row on the *expression* it was given, so a
      plan offering the node's own position mints a second row per branch. That
      is one extra dispatch site per `ifexp`, which is how the first attempt at
      routing the branching nodes drifted. -/
  truthSubterm : Pos -> Subterm -> AbsVal -> AState -> M TruthFlow :=
    fun _ _ value state =>
      pure { truthy := some (value, state), falsy := some (value, state) }
  /-- Refine a subterm syntactically into its truthy and falsy states, as the
      `isinstance` narrowing already does for the hand-written branching nodes.
      A value-level test cannot do this: narrowing `x` to `obj:A` is a statement
      about the environment, not about the value the test produced. Declining to
      split is the unrefined and therefore sound default. -/
  refineSubterm : Pos -> Subterm -> AState -> M (Option AState × Option AState) :=
    fun _ _ state => pure (some state, some state)
  /-- Execute a body child, producing all five completions. `evalSubterm` returns
      a `Flow`, and a body can return, break or continue, so bodies need their own
      service. Fails closed: without one a plan naming a body must not proceed as
      though the body were empty. -/
  executeBodyPlan : Pos -> List Stmt -> AState -> M Completion :=
    fun position _ _ => do
      oblige position "body-executor-missing"
        "no body executor installed: a plan cannot run a statement body"
      pure {}
  /-- Delete a target child's binding. Separate from `bindTargetValue` because
      deletion carries no value and its failure modes differ. Fails closed. -/
  deleteTargetAt : Pos -> Target -> AState -> M Flow :=
    fun position _ _ => do
      oblige position "target-binder-missing"
        "no target binder installed: a plan cannot delete an assignment target"
      pure {}
  /-- Store a value under a name. Fails closed. -/
  storeNameValue : Pos -> String -> AbsVal -> AState -> M AState :=
    fun position name _ state => do
      oblige position "name-store-missing"
        s!"no name store installed: a plan cannot bind {name}"
      pure state
  /-- Read a name, with its unbound partitions and obligations. -/
  readNameValue : Pos -> String -> AState -> M Flow :=
    fun position name _ => do
      oblige position "name-reader-missing"
        s!"no name reader installed: a plan cannot read {name}"
      pure {}
  /-- Bind an already-evaluated value to a target child. A target is not an
      expression and the value it binds comes from elsewhere in the plan, so this
      cannot be an `evalChild`. Fails closed the same way. -/
  bindTargetValue : Pos -> Target -> AbsVal -> AState -> M Flow :=
    fun position _ _ _ => do
      oblige position "target-binder-missing"
        "no target binder installed: a plan cannot bind an assignment target"
      pure {}
  /-- Record a proof obligation. Some hand-written transfers record one -- an
      `assert` states that its condition holds -- and a rule with no way to say so
      loses it silently when routed. -/
  recordObligation : Pos -> String -> String -> M Unit :=
    fun _ _ _ => pure ()
  /-- The named Lean transfers a `.engine` plan escapes to. Fails closed the
      same way, so an unrouted escape hatch is visible rather than silent. -/
  engineTransfer : Pos -> String -> Frame -> AState -> M Flow :=
    fun position name _ _ => do
      oblige position "engine-transfer-missing"
        s!"no engine transfer installed for {name}"
      pure {}
  /-- Runs a rule's argument contracts in declaration order before its body.
      The default fails closed: without an installed executor a declared
      contract is unchecked, so the rule body must not run. -/
  applyContracts : Pos -> List ContractArgument -> AState ->
      M ContractArguments :=
    fun position arguments _ => do
      oblige position "contract-service-missing"
        s!"no argument-contract executor installed for {", ".intercalate (arguments.map (fun argument => argument.contract.label))}"
      pure {}

def tagMayBeTruthy : Tag -> Bool
  | .tnone | .tunbound | .tuninit | .tmissing => false
  | _ => true

def tagMayBeFalsy : Tag -> Bool
  | .tnone | .tbool | .tint | .tfloat | .tcomplex | .tstr
  | .tlist | .tdict | .tdictkeys | .tdictitems | .tdictvalues
  | .tset | .ttuple | .trange | .tobj _ | .tany => true
  | _ => false

def opaqueTruth (_ : Pos) (value : AbsVal) (state : AState) : M TruthFlow :=
  let truthy := keepTags value tagMayBeTruthy
  let falsy := keepTags value tagMayBeFalsy
  pure {
    truthy := if truthy.isBot then none else some (truthy, state)
    falsy := if falsy.isBot then none else some (falsy, state)
  }

def Services.opaque : Services where
  invoke := fun _ _ _ _ _ state => pure (Flow.ofNormal anyV state)
  truth := opaqueTruth

-- One definition, in `Cells/State.lean` beside `heapSet` and `heapJoin`, because
-- choosing between them is what this predicate is for. Four identical copies
-- lived in four files and no test distinguished them.
abbrev completeStrongTarget := @Pylate.strongUpdateTarget

def growCell (receiver : AbsVal) (cls : LocCls) (cell : CellSelector)
    (value : AbsVal) (state : AState) : AState := Id.run do
  let mut result := state
  for location in receiver.locs do
    if location.cls == cls then
      result := result.heapJoin location cell value
  return result

def clearCell (receiver : AbsVal) (cls : LocCls) (cell : CellSelector)
    (state : AState) : AState :=
  match receiver.locs with
  | [location] =>
    if location.cls == cls && completeStrongTarget receiver location then
      state.heapSet location cell AbsVal.bot
    else state
  | _ => state

def executeMutation (effect : Mutation) (frame : Frame)
    (state : AState) : AState :=
  match effect with
  | .grow target cls reference value =>
    let cell := reference.resolve frame.attributes
    let receiver := target.eval frame state
    let updated :=
      growCell receiver cls cell (value.eval frame state) state
    if cell == .elem then
      collectionBecomesNonempty updated receiver cls
    else updated
  | .clear target cls reference =>
    let cell := reference.resolve frame.attributes
    let receiver := target.eval frame state
    let updated := clearCell receiver cls cell state
    if cell == .elem then
      collectionBecomesEmpty updated receiver cls
    else updated
  | .emptiness target cls value =>
    updateCollectionEmptiness state (target.eval frame state) cls value
  | .sizeOfChildren target cls =>
    updateCollectionSize state (target.eval frame state) cls
      (.exact frame.subterms.length)
  | .bind name value => state.envSet name (value.eval frame state)
  | .unbind name => state.envKill name

def exceptionValue (p : Pos) (spec : RaiseSpec) (cls : String)
    (frame : Frame) (state : AState) : AbsVal × AState :=
  match spec.value with
  | some expression => (expression.eval frame state, state)
  | none => allocate state p.id (.obj cls) []

/-- The residual row a raised alternative belongs to: a method's row is keyed
    by its receiver tag, a function's by `func`, as the call site records it. -/
private def raiseRowTag (frame : Frame) : String :=
  match frame.receiver.tags with
  | [tag] => tag.render
  | [] => "func"
  | tags => String.intercalate "|" (tags.map Tag.render)

def executeRaise (p : Pos) (spec : RaiseSpec) (frame : Frame)
    (state : AState) : M Flow := do
  let mut raised : RaisedFlow := {}
  let operandClasses := match spec.classesOf with
    | none => []
    | some source =>
      let value := frame.read source
      value.tags.foldl (fun names candidate =>
        match candidate with
        | .tobj className => Fset.insert className names
        | _ => names) value.classes
  let provenance : Provenance := match spec.kind with
    | .machine => .machine
    | .user => .user
    | .internal => .internal
  for cls in Fset.union spec.classes operandClasses do
    if spec.kind == .machine then
      let modeled <- mraise p {} state [cls]
      if cls ∈ modeled.tags then
        let (value, raisedState) := exceptionValue p spec cls frame state
        raised := raised.add ⟨cls, value, raisedState, p, provenance⟩
    else
      let (value, raisedState) := exceptionValue p spec cls frame state
      raised := raised.add ⟨cls, value, raisedState, p, provenance⟩
  pure { raised }

def evalInvocation (call : Invocation) (frame : Frame) (state : AState) :
    Option AbsVal × List AbsVal × List (String × AbsVal) :=
  let receiver := call.receiver.map (·.eval frame state)
  if call.forwardInput then
    (receiver, frame.call.input.positional, frame.call.input.keywords)
  else
    (receiver,
     call.arguments.map (·.eval frame state),
     call.keywords.map fun (name, value) => (name, value.eval frame state))

/-- What executing a plan produces.

    `Flow` has room for a normal completion and raised ones, which is all an
    expression needs. A statement also finishes by returning, breaking or
    continuing, so a plan that can express those needs somewhere to put them.
    Keeping them beside the flow rather than inside it means the expression
    rules are untouched: they produce a `PlanResult` whose three extra slots are
    always empty, and `toCompletion` is what the statement kernel consumes. -/
structure PlanResult where
  flow      : Flow := {}
  returned  : Option Normal := none
  broke     : Option AState := none
  continued : Option AState := none
deriving Inhabited

namespace PlanResult

def ofFlow (flow : Flow) : PlanResult := { flow }

def join (left right : PlanResult) : PlanResult :=
  { flow := left.flow.join right.flow
    returned := joinNormal left.returned right.returned
    broke := joinOpt left.broke right.broke
    continued := joinOpt left.continued right.continued }

/-- Continue on the normal partition only, exactly as `Flow.bindNormal` does,
    and carry the abnormal completions past the continuation untouched -- they
    have already finished and must not be re-entered. -/
def bindNormal (result : PlanResult)
    (next : AbsVal -> AState -> M PlanResult) : M PlanResult := do
  match result.flow.normal with
  | none => pure result
  | some (value, state) =>
    let rest <- next value state
    pure (join { result with flow := { raised := result.flow.raised } } rest)

/-- The statement view. A normal completion contributes its state; the value it
    carried belongs to expressions and is dropped here. -/
def toCompletion (result : PlanResult) : Completion :=
  { normal := result.flow.normal.map (·.2)
    returned := result.returned
    broke := result.broke
    continued := result.continued
    raised := result.flow.raised }

end PlanResult

/-- Can the unpack of `container` into `targets` names be shown to match?

    Unpacking is arity-checked at runtime: `a, b = [1, 2, 3]` is a `ValueError`.
    The element summary a tuple target binds carries no length, so the check
    cannot be answered from it.

    A tuple all of whose slots are tracked answers it exactly, which is what
    keeps `a, b = 1, 2` free of a spurious raise. Anything else -- a list, a
    tuple joined from two literals of different arity, an unknown -- leaves the
    length unproven, and the raise stands with an obligation beside it. -/
private def provenUnpackArity (container : AbsVal) (state : AState)
    (targets : Nat) : Bool :=
  match container.tags, container.locs with
  | [.ttuple], [location] => state.tupleSlotCount location == targets
  | _, _ => false

mutual

partial def executePlan (services : Services) (p : Pos) (plan : Plan)
    (frame : Frame) (state : AState) : M PlanResult := do
  match plan with
  | .normal expression =>
    pure (.ofFlow (Flow.ofNormal (expression.eval frame state) state))
  | .stop => pure {}
  | .raise spec => .ofFlow <$> executeRaise p spec frame state
  | .bind first next =>
    let result <- executePlan services p first frame state
    result.bindNormal fun value nextState =>
      executePlan services p next (frame.push value) nextState
  | .mutate effect next =>
    executePlan services p next frame (executeMutation effect frame state)
  | .letValue value next =>
    executePlan services p next (frame.push (value.eval frame state)) state
  | .allocate cls initializers next =>
    let values := initializers.map fun (cell, value) =>
      (cell, value.eval frame state)
    let (fresh, nextState) := allocate state p.id cls []
    let location : Loc := ⟨p.id, cls, true⟩
    let nextState := values.foldl
      (fun current (cell, value) =>
        current.heapSet location cell value) nextState
    -- Allocation starts Empty; an element initializer contradicts that, and
    -- a non-bottom element summary alone cannot prove NonEmpty.
    let nextState :=
      if cls.tracksEmptiness then
        match values.find? (·.1 == CellSelector.elem) with
        | some (_, elements) =>
          if elements.isBot then nextState
          else strongEmptinessUpdate nextState location .top
        | none => nextState
      else nextState
    let nextState := values.foldl
      (fun current (cell, value) =>
        if cell == .nonempty && !value.isBot then
          strongEmptinessUpdate current location .nonempty
        else current) nextState
    executePlan services p next (frame.push fresh) nextState
  | .require condition failure next =>
    let split := condition.split (← get).classes frame state
    let mut result : PlanResult := {}
    if let some yes := split.yes then
      result := result.join (← executePlan services p next yes state)
    if let some no := split.no then
      result := result.join (.ofFlow (← executeRaise p failure no state))
    pure result
  | .branch condition yes no =>
    let split := condition.split (← get).classes frame state
    let mut result : PlanResult := {}
    if let some yesFrame := split.yes then
      result := result.join (← executePlan services p yes yesFrame state)
    if let some noFrame := split.no then
      result := result.join (← executePlan services p no noFrame state)
    pure result
  | .truthBranch source truthy falsy =>
    let tested <- services.truth p (frame.read source) state
    let mut result : PlanResult := { flow := { raised := tested.raised } }
    if let some (value, truthyState) := tested.truthy then
      result := result.join (← executePlan services p truthy
        (frame.write source value) truthyState)
    if let some (value, falsyState) := tested.falsy then
      result := result.join (← executePlan services p falsy
        (frame.write source value) falsyState)
    pure result
  | .alternatives plans =>
    let mut result : PlanResult := {}
    for alternative in plans do
      result := result.join (← executePlan services p alternative frame state)
    pure result
  | .invoke call next =>
    let (receiver, arguments, keywords) := evalInvocation call frame state
    match call.operation.resolve frame.attributes with
    | none =>
      oblige p "operator-attribute"
        "invocation names an operator attribute the node does not carry"
      pure {}
    | some operation =>
      let invoked <- services.invoke p operation receiver arguments keywords state
      (PlanResult.ofFlow invoked).bindNormal fun value nextState =>
        executePlan services p next (frame.push value) nextState
  | .protocolChain candidates fallback =>
    executeProtocol services p candidates fallback frame state
  | .evalChild index next =>
    executeChildren services p [index] next frame state
  | .evalChildren index next =>
    -- Every remaining subterm, in order.
    let indices := (List.range frame.subterms.length).drop index
    executeChildren services p indices next frame state
  | .engine name =>
    .ofFlow <$> services.engineTransfer p name frame state
  | .returnWith value =>
    pure { returned := some (value.eval frame state, state) }
  | .breakLoop => pure { broke := some state }
  | .continueLoop => pure { continued := some state }
  | .obligate kind detail next => do
    services.recordObligation p kind detail
    executePlan services p next frame state
  | .evalBody index next =>
    match frame.subterms[index]? with
    | some (.body body) =>
      let completion <- services.executeBodyPlan p body state
      let abnormal : PlanResult :=
        { flow := { raised := completion.raised }
          returned := completion.returned
          broke := completion.broke
          continued := completion.continued }
      match completion.normal with
      | none => pure abnormal
      | some bodyState =>
        pure (abnormal.join (<- executePlan services p next frame bodyState))
    | some _ =>
      oblige p "subterm-kind"
        s!"plan runs child {index} as a body, but it is not one"
      pure {}
    | none =>
      oblige p "subterm-index"
        s!"plan runs body child {index} of a node with {frame.subterms.length}"
      pure {}
  | .allocateSlots cls next =>
    let (fresh, allocated) := allocate state p.id cls []
    let location : Loc := ⟨p.id, cls, true⟩
    let elements := frame.evaluated.foldl AbsVal.join AbsVal.bot
    let withSlots := frame.evaluated.zipIdx.foldl
      (fun current (value, index) =>
        current.heapSet location (.tupleSlot index) value) allocated
    let initialized := withSlots.heapSet location .elem elements
    let initialized := strongEmptinessUpdate initialized location
      (if frame.evaluated.isEmpty then .empty else .nonempty)
    executePlan services p next (frame.push fresh) initialized
  | .allocateMapping cls next =>
    let (fresh, allocated) := allocate state p.id cls []
    let location : Loc := ⟨p.id, cls, true⟩
    let pairs := frame.evaluated.zipIdx
    let keys := pairs.foldl
      (fun out (value, index) =>
        if index % 2 == 0 then out.join value else out) AbsVal.bot
    let values := pairs.foldl
      (fun out (value, index) =>
        if index % 2 == 1 then out.join value else out) AbsVal.bot
    let initialized :=
      (allocated.heapSet location .dictKeys keys).heapSet location .dictValues
        values
    -- A literal key gets its own cell, so a later read can prove it present.
    let initialized := pairs.foldl
      (fun current (value, index) =>
        if index % 2 == 0 then
          match value.strLits with
          | [only] =>
            if value.strOpen then current
            else
              match frame.evaluated[index + 1]? with
              | some paired => current.heapSet location (.literalKey only) paired
              | none => current
          | _ => current
        else current) initialized
    let initialized := strongEmptinessUpdate initialized location
      (if frame.evaluated.isEmpty then .empty else .nonempty)
    executePlan services p next (frame.push fresh) initialized
  | .storeName name value next =>
    match (frame.attributes.find? (·.1 == name)).map (·.2) with
    | some (Attr.name x) =>
      let stored <- services.storeNameValue p x (value.eval frame state) state
      executePlan services p next frame stored
    | _ =>
      oblige p "name-attribute"
        "plan stores to a name attribute the node does not carry"
      pure {}
  | .bindEach index value next =>
    let bound := value.eval frame state
    let indices := (List.range frame.subterms.length).drop index
    let mut current : PlanResult := { flow := Flow.ofNormal bound state }
    -- The container is what has a length; `value` is its element summary, and
    -- `.elements` is what names the slot the container came from.
    if let .elements source := value then
      unless provenUnpackArity (frame.read source) state indices.length do
        oblige p "unpack-arity"
          s!"unpack into {indices.length} targets: source length not proven"
        let modeled <- mraise p {} state ["ValueError"]
        if "ValueError" ∈ modeled.tags then
          current := { current with flow := { current.flow with
            raised := current.flow.raised.add
              ⟨"ValueError", AbsVal.bot, state, p, .machine⟩ } }
    for childIndex in indices do
      match frame.subterms[childIndex]? with
      | some (.target child) =>
        match current.flow.normal with
        | none => pure ()
        | some (_, currentState) =>
          let step <- services.bindTargetValue p child bound currentState
          -- Join the raise instead of replacing the flow. Overwriting it here
          -- dropped every raised case recorded before this target bound: the
          -- arity `ValueError` above, and a raise from an earlier nested target
          -- such as the attribute store in `o.x, o.y = pair`.
          current := { current with
            flow := { normal := step.normal
                      raised := current.flow.raised.join step.raised } }
      | _ =>
        oblige p "subterm-kind"
          s!"plan binds child {childIndex} as a target, but it is not one"
    current.bindNormal fun _ afterState =>
      executePlan services p next frame afterState
  | .readName name next =>
    match (frame.attributes.find? (·.1 == name)).map (·.2) with
    | some (Attr.name x) =>
      let read <- services.readNameValue p x state
      (PlanResult.ofFlow read).bindNormal fun value nextState =>
        executePlan services p next (frame.push value) nextState
    | _ =>
      oblige p "name-attribute"
        "plan reads a name attribute the node does not carry"
      pure {}
  | .deleteTarget index next =>
    match frame.subterms[index]? with
    | some (.target target) =>
      let removed <- services.deleteTargetAt p target state
      (PlanResult.ofFlow removed).bindNormal fun _ afterState =>
        executePlan services p next frame afterState
    | some _ =>
      oblige p "subterm-kind"
        s!"plan deletes child {index} as a target, but it is not one"
      pure {}
    | none =>
      oblige p "subterm-index"
        s!"plan deletes target child {index} of a node with {frame.subterms.length}"
      pure {}
  | .bindTarget index value next =>
    match frame.subterms[index]? with
    | some (.target target) =>
      let bound <- services.bindTargetValue p target (value.eval frame state)
        state
      (PlanResult.ofFlow bound).bindNormal fun _ boundState =>
        executePlan services p next frame boundState
    | some _ =>
      oblige p "subterm-kind"
        s!"plan binds child {index} as a target, but it is not one"
      pure {}
    | none =>
      oblige p "subterm-index"
        s!"plan binds target child {index} of a node with {frame.subterms.length}"
      pure {}
  | .refineBranch index truthy falsy =>
    match frame.subterms[index]? with
    | none =>
      oblige p "subterm-index"
        s!"plan refines child {index} of a node with {frame.subterms.length}"
      pure {}
    | some subterm =>
      let evaluated <- services.evalSubterm p subterm state
      let mut result : PlanResult := { flow := { raised := evaluated.raised } }
      match evaluated.normal with
      | none => pure result
      | some (value, postState) =>
        let tested <- services.truthSubterm p subterm value postState
        result := { result with
          flow := { result.flow with
            raised := result.flow.raised.join tested.raised } }
        -- Refinement applies to the state the truth test left; each side then
        -- sees only its own narrowing.
        let reached := match tested.truthy, tested.falsy with
          | some (_, s), _ => some s
          | _, some (_, s) => some s
          | _, _ => none
        match reached with
        | none => pure result
        | some truthState =>
          let (trueState, falseState) <-
            services.refineSubterm p subterm truthState
          let grown := { frame with evaluated := frame.evaluated ++ [value] }
          if tested.truthy.isSome then
            if let some branchState := trueState then
              result := result.join
                (<- executePlan services p truthy grown branchState)
          if tested.falsy.isSome then
            if let some branchState := falseState then
              result := result.join
                (<- executePlan services p falsy grown branchState)
          -- The merge of the two arms, named so a claim can be attached to it.
          -- Every branching node routes through `refineBranch` -- the `if`
          -- statement, `and`/`or`, the conditional expression -- so this is where
          -- all of their post-states join.
          if let some (_, merged) := result.flow.normal then
            snapJoin .ifMerge p merged
          pure result

/-- Evaluate the named subterms left to right, threading the state, and run
    `next` only on the path where all of them completed normally. A raised
    partition from any child is part of the result and abandons the rest: the
    ordering and abandon-on-exception discipline lives here once, instead of
    being re-established in every syntax rule. -/
partial def executeChildren (services : Services) (p : Pos)
    (indices : List Nat) (next : Plan) (frame : Frame)
    (state : AState) : M PlanResult := do
  match indices with
  | [] => executePlan services p next frame state
  | index :: rest =>
    match frame.subterms[index]? with
    | none =>
      oblige p "subterm-index"
        s!"plan names child {index} of a node with {frame.subterms.length}"
      pure {}
    | some subterm =>
      let child <- services.evalSubterm p subterm state
      let raisedOnly : PlanResult := { flow := { raised := child.raised } }
      match child.normal with
      | none => pure raisedOnly
      | some (value, childState) =>
        let grown := { frame with evaluated := frame.evaluated ++ [value] }
        let rest <- executeChildren services p rest next grown childState
        pure (raisedOnly.join rest)

partial def executeProtocol (services : Services) (p : Pos)
    (candidates : List Plan) (fallback : Plan) (frame : Frame)
    (state : AState) : M PlanResult := do
  match candidates with
  | [] => executePlan services p fallback frame state
  | candidate :: rest =>
    let first <- executePlan services p candidate frame state
    match first.flow.normal with
    | none => pure first
    | some (value, nextState) =>
      let ordinary := value.withoutTags [.tnotimpl]
      let success : PlanResult :=
        { first with flow :=
            { normal := if ordinary.isBot then none else some (ordinary, nextState)
              raised := first.flow.raised } }
      if Tag.tnotimpl ∈ value.tags || Tag.tany ∈ value.tags then
        pure (success.join
          (← executeProtocol services p rest fallback frame nextState))
      else
        pure success

end

-- --------------------------------------------------------------- rule entry

structure CallableRule where
  signature : Signature
  body      : Plan
  /-- Per-parameter runtime contracts, run in this order before the body. A
      parameter the call did not supply is skipped. -/
  contracts : List (String × ArgContract) := []
  /-- The contract every extra positional argument must satisfy. -/
  variadic  : Option ArgContract := none
  isOpaque  : Bool := false
deriving Repr, Inhabited

/-- The contract prelude of one bound call: only supplied parameters take
    part, and the body sees each contract's converted value. -/
private def contractArguments (rule : CallableRule) (frame : Frame) :
    List ContractArgument :=
  let call := frame.call
  (rule.contracts.filterMap fun (name, contract) =>
    (call.parameters.find? (·.1 == name)).map fun (_, value) =>
      { name, contract, value, target := frame.receiver }) ++
  (match rule.variadic with
   | none => []
   | some contract =>
     call.varPos.zipIdx.map fun (value, position) =>
       { name := s!"arg{position}", contract, value
         target := frame.receiver })

private def withConverted (call : BoundCall)
    (converted : List (String × AbsVal)) : BoundCall :=
  { call with
    parameters := call.parameters.map fun (name, value) =>
      match converted.find? (·.1 == name) with
      | some (_, refined) => (name, refined)
      | none => (name, value) }

def executeRule (services : Services) (p : Pos) (rule : CallableRule)
    (receiver : AbsVal) (input : CallInput) (state : AState) : M Flow := do
  match rule.signature.bind input with
  | .ok call =>
    let arguments := contractArguments rule { receiver, call }
    -- A callable rule finishes with a value or an exception. `return`, `break`
    -- and `continue` are statement completions, so a callable rule producing one
    -- is a rule error rather than something to route silently.
    let callableFlow := fun (result : PlanResult) => do
      if result.returned.isSome || result.broke.isSome
          || result.continued.isSome then
        oblige p "statement-completion-in-callable"
          "callable rule produced a return, break or continue"
      pure result.flow
    if arguments.isEmpty then
      callableFlow (← executePlan services p rule.body { receiver, call } state)
    else
      let checked ← services.applyContracts p arguments state
      match checked.normal with
      | none => pure { raised := checked.raised }
      | some (converted, postState) =>
        let body ← callableFlow (← executePlan services p rule.body
          { receiver, call := withConverted call converted } postState)
        pure { body with raised := body.raised.join checked.raised }
  | .error _ =>
    executeRaise p (RaiseSpec.machine "TypeError")
      { receiver, call := { input := input } } state

end Pylate.RuleDriven
