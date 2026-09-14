/-
Per-tag builtin outcomes as one keyed table.

Every transfer for a builtin protocol -- subscript, attribute, length,
membership, iteration -- ends in a `match` over the receiver's tag, and every
such `match` ends in a fall-through arm that *asserts* an outcome for every tag
it does not name. That is a claim, not a safe default, and it is the shape of
every soundness hole found in this area:

  * `bytes` had no `+`, because `fallbackImpl` named `str`, `list` and `tuple`.
  * `bytes` was absent from the membership arm, so `1 in b"ab"` was a TypeError.
  * `n.real` fell through `attributeRead` to `AttributeError`.
  * a sequence indexed by a non-integral key claimed a normal completion.

All four are missing rows. None was a wrong algorithm, and none was reachable by
reading the code -- each was found by probing CPython. So the outcomes become a
table with a declared coverage obligation over `builtinTags × BuiltinOp`, and
`RuleValidate` fails a rule set that omits a pair. A pair that is intentionally
handled elsewhere says so with `.deferred`, which is a decision rather than a
silence.

The table answers only what is decidable from the tags: whether a normal
completion exists at all, and which exceptions the operation can raise. Where the
value comes from a heap cell -- a list element, a dict value, a tuple slot -- the
table says `fromCell` and the transfer reads it, because that is a query over the
state and not a property of the tag.
-/
import Pylate.Domains.Value

namespace Pylate

/-- The builtin protocols whose outcome depends on the receiver's tag. -/
inductive BuiltinOp
  | subscriptRead
  | subscriptWrite
  | attribute
  | length
  | membership
  | iterate
deriving Repr, BEq, Inhabited

def BuiltinOp.render : BuiltinOp -> String
  | .subscriptRead => "subscript read"
  | .subscriptWrite => "subscript write"
  | .attribute => "attribute read"
  | .length => "len()"
  | .membership => "in"
  | .iterate => "iteration"

/-- Where a normal completion's value comes from. -/
inductive OutcomeValue
  /-- A fixed tag set, decided by the receiver's tag alone. -/
  | tags (tags : List Tag)
  /-- A heap cell of the receiver: the element summary, a dict value, a slot. The
      transfer reads it, because it is a query over the state. -/
  | fromCell
  /-- No normal completion: the operation always raises. -/
  | never
  /-- The attribute name decides, not the tag: the property table and the method
      inventory answer it, and a name in neither is the `AttributeError`. The tag
      still decides *that* those two tables are the answer, which is what this
      row states. -/
  | byName
  /-- Unknown, and declared so. Not the same as `never`. -/
  | unknown
deriving Repr, BEq, Inhabited

/-- One row: what this operation on this tag can do. -/
structure Outcome where
  value : OutcomeValue := .never
  /-- Exceptions the operation can raise on this tag. -/
  raises : List String := []
  /-- The pair is handled by a richer transfer than a tag lookup, and this row
      records that as a decision. `itemRead` on a TypedDict is the example: the
      outcome depends on the declared key set, not on the tag. -/
  deferred : Bool := false
  /-- The obligation an indexed read owes for staying in bounds, when it owes
      one. Wording included, because it is per-tag and was hardcoded at each
      branch -- which is the same dual-source problem as the raise sets. -/
  bounds : Option String := none
  /-- Whether the operation's argument must be integral, so a non-integral one is
      a `TypeError` rather than a bounds question. Tuple omitted this check
      entirely: `("a", 1)[s]` reported an `IndexError` and no `TypeError`, where
      CPython raises `TypeError` and never `IndexError`. Wrong in both directions,
      and invisible while each branch carried its own copy of the rule. -/
  integralArgument : Bool := false
deriving Repr, Inhabited

/-- Always raises `TypeError`: the tag does not support the protocol at all. -/
def unsupported : Outcome := { value := .never, raises := ["TypeError"] }

/-- Declared as handled elsewhere. -/
def deferredOutcome : Outcome := { value := .unknown, deferred := true }

/-- The tags a program value can carry that this table must answer for.

    `tobj` is excluded because a user class's outcome comes from its MRO, not from
    its tag. The three non-values -- `tunbound`, `tuninit`, `tmissing` -- are
    excluded because they are not receivers: reading one is a boundness error that
    a different condition reports, before any protocol runs. -/
def builtinTags : List Tag :=
  [ .tnone, .tbool, .tint, .tfloat, .tcomplex, .tstr, .tbytes
  , .tlist, .tdict, .tdictkeys, .tdictitems, .tdictvalues
  , .tset, .ttuple, .trange, .tgen
  , .ttype, .tunion, .tfunc, .tnotimpl, .tany ]

def allBuiltinOps : List BuiltinOp :=
  [.subscriptRead, .subscriptWrite, .attribute, .length, .membership, .iterate]

/-- Attribute reads. The tag decides which *kind* of answer applies, and the name
    decides the answer: `builtinProperty` for the properties, `knownMethods` for
    the methods, `AttributeError` for a name in neither.

    Every builtin has attributes, which is what the hand-written fall-through got
    wrong -- `n.real` is an int and `xs.append` is a bound method, and both were
    reported as `AttributeError`. `none` has none at all, and that is a row rather
    than a fall-through. -/
def attributeOutcome : Tag -> Outcome
  | .tnone => { value := .never, raises := ["AttributeError"] }
  | .tbool | .tint | .tfloat | .tcomplex | .tstr | .tbytes
  | .tlist | .tdict | .tset | .ttuple | .trange =>
    { value := .byName, raises := ["AttributeError"] }
  -- A view's attribute surface is not enumerated, so this defers rather than
  -- claiming an AttributeError the interpreter may not raise.
  | .tdictkeys | .tdictitems | .tdictvalues => deferredOutcome
  | .tgen => deferredOutcome
  | .ttype | .tunion | .tfunc => deferredOutcome
  | .tnotimpl => { value := .never, raises := ["AttributeError"] }
  | .tany => deferredOutcome
  | .tobj _ => deferredOutcome
  | .tunbound | .tuninit | .tmissing =>
    { value := .never, raises := ["AttributeError"] }

/-- Subscript reads. Verified against CPython 3.13 by `tests/catchall_oracle.py`.

    Note `bytes` yields an int and `type` builds a generic alias, so neither is a
    TypeError-only claim: such a claim has no normal completion and would make the
    following statements unreachable. -/
def subscriptReadOutcome : Tag -> Outcome
  | .tstr =>
    { value := .tags [.tstr], raises := ["IndexError", "TypeError"]
      bounds := some "string index within length", integralArgument := true }
  | .tbytes =>
    { value := .tags [.tint], raises := ["IndexError", "TypeError"]
      bounds := some "bytes index within length", integralArgument := true }
  | .tlist =>
    { value := .fromCell, raises := ["IndexError", "TypeError"]
      bounds := some "sequence index within length", integralArgument := true }
  | .ttuple =>
    { value := .fromCell, raises := ["IndexError", "TypeError"]
      bounds := some "sequence index within length", integralArgument := true }
  -- A range owes no bounds obligation: its length is part of its own value
  -- rather than a fact about the heap.
  | .trange =>
    { value := .tags [.tint], raises := ["IndexError", "TypeError"]
      integralArgument := true }
  -- The declared key set decides this, not the tag.
  | .tdict => deferredOutcome
  -- `type[int]` is a generic alias, and a class may define `__class_getitem__`.
  | .ttype => deferredOutcome
  | .tany => deferredOutcome
  | .tnone | .tbool | .tint | .tfloat | .tcomplex
  | .tset | .tdictkeys | .tdictitems | .tdictvalues | .tgen
  | .tunion | .tfunc | .tnotimpl => unsupported
  | .tobj _ => deferredOutcome
  | .tunbound | .tuninit | .tmissing => unsupported

/-- Subscript writes. Only the mutable containers accept one; `str`, `bytes`,
    `tuple` and `range` are immutable, which is a `TypeError` and not an
    `IndexError`. -/
def subscriptWriteOutcome : Tag -> Outcome
  | .tlist => { value := .tags [.tnone], raises := ["IndexError", "TypeError"] }
  | .tdict => deferredOutcome
  | .tany => deferredOutcome
  | .tstr | .tbytes | .ttuple | .trange => unsupported
  | .tnone | .tbool | .tint | .tfloat | .tcomplex
  | .tset | .tdictkeys | .tdictitems | .tdictvalues | .tgen
  | .ttype | .tunion | .tfunc | .tnotimpl => unsupported
  | .tobj _ => deferredOutcome
  | .tunbound | .tuninit | .tmissing => unsupported

/-- `len()`. A generator has no length, which is the one that surprises people:
    `len(x for x in [])` is a TypeError, not 0. -/
def lengthOutcome : Tag -> Outcome
  | .tstr | .tbytes | .tlist | .tdict | .tset | .ttuple | .trange
  | .tdictkeys | .tdictitems | .tdictvalues =>
    { value := .tags [.tint] }
  | .tany => deferredOutcome
  | .tgen => unsupported
  | .tnone | .tbool | .tint | .tfloat | .tcomplex
  | .ttype | .tunion | .tfunc | .tnotimpl => unsupported
  | .tobj _ => deferredOutcome
  | .tunbound | .tuninit | .tmissing => unsupported

/-- `in`. Typed for `str` and `bytes` and untyped for everything else: `1 in "ab"`
    is a TypeError where `1 in (1, 2)` is `False`, and a `bytes` probe must be a
    single byte so an out-of-range int is a `ValueError`. -/
def membershipOutcome : Tag -> Outcome
  | .tstr => { value := .tags [.tbool], raises := ["TypeError"] }
  | .tbytes =>
    { value := .tags [.tbool], raises := ["TypeError", "ValueError"] }
  | .tlist | .ttuple | .trange | .tgen
  | .tdictkeys | .tdictitems | .tdictvalues =>
    { value := .tags [.tbool] }
  -- Probing an unhashable key is a TypeError.
  | .tdict | .tset => { value := .tags [.tbool], raises := ["TypeError"] }
  | .tany => deferredOutcome
  | .tnone | .tbool | .tint | .tfloat | .tcomplex
  | .ttype | .tunion | .tfunc | .tnotimpl => unsupported
  | .tobj _ => deferredOutcome
  | .tunbound | .tuninit | .tmissing => unsupported

/-- Iteration. `dict` iterates its keys, so the element is a cell read. -/
def iterateOutcome : Tag -> Outcome
  | .tstr => { value := .tags [.tstr] }
  | .tbytes => { value := .tags [.tint] }
  | .trange => { value := .tags [.tint] }
  | .tlist | .tset | .ttuple | .tdict
  | .tdictkeys | .tdictitems | .tdictvalues => { value := .fromCell }
  | .tgen => deferredOutcome
  | .tany => deferredOutcome
  | .tnone | .tbool | .tint | .tfloat | .tcomplex
  | .ttype | .tunion | .tfunc | .tnotimpl => unsupported
  | .tobj _ => deferredOutcome
  | .tunbound | .tuninit | .tmissing => unsupported

/-- The table. Total on `Tag × BuiltinOp` by construction: each arm above is an
    exhaustive `match`, so adding a `Tag` constructor is a compile error in five
    places rather than a silent fall-through in five transfers. -/
def builtinOutcome (tag : Tag) : BuiltinOp -> Outcome
  | .subscriptRead => subscriptReadOutcome tag
  | .subscriptWrite => subscriptWriteOutcome tag
  | .attribute => attributeOutcome tag
  | .length => lengthOutcome tag
  | .membership => membershipOutcome tag
  | .iterate => iterateOutcome tag

/-- The label a residual row shows for this outcome's normal completion. Derived
    from the row so the row is the only place it is written. -/
def Outcome.resultLabel (outcome : Outcome) : String :=
  match outcome.value with
  | .tags tags => "|".intercalate (tags.map Tag.render)
  | .fromCell => "elem"
  | .byName => "by name"
  | .never => "!"
  | .unknown => "deferred"

/-- Whether a normal completion is possible. This is the question the fall-through
    arms got wrong: claiming `.never` where CPython returns a value deletes the
    normal completion, which makes the following statements unreachable and
    discharges their obligations for free. -/
def Outcome.admitsNormal (outcome : Outcome) : Bool :=
  match outcome.value with
  | .never => false
  | _ => true

/-- A concrete builtin outcome: a normal completion decided by the tag itself,
    not deferred to a richer transfer. This is the question the hand-maintained
    tag lists were answering -- `builtinSized`, `builtinIterable` (twice) -- so it
    is what replaces them. -/
def Outcome.concrete (outcome : Outcome) : Bool :=
  outcome.admitsNormal && !outcome.deferred

/-- The non-callable public attributes of the builtin types, and their values.

    `dir()` lists these beside the methods, but they are properties, so reading
    one is a read with a result rather than a bound-method escape. `knownMethods`
    is a method inventory and rightly omits them, which is exactly why they need
    their own table instead of falling into the `AttributeError` arm.

    `True.real` is `1`, an int, so `bool` widens to int rather than staying
    `bool`. -/
def builtinProperty (tag : Tag) (name : String) : Option AbsVal :=
  match tag with
  | .tint | .tbool =>
    if name == "real" || name == "imag" || name == "numerator" ||
        name == "denominator" then some (V [.tint]) else none
  | .tfloat =>
    if name == "real" || name == "imag" then some (V [.tfloat]) else none
  | .trange =>
    if name == "start" || name == "stop" || name == "step"
    then some (V [.tint]) else none
  | _ => none

/-- The tags a `str`/`bytes` membership probe may have.

    `in` over the two string types is typed, unlike every other builtin
    container. A `bytes` probe additionally has to be a byte, so an out-of-range
    int is a `ValueError` -- and the magnitude is not tracked, so that one stays
    an obligation. -/
def stringProbeTags : Tag -> List Tag
  | .tstr => [.tstr, .tany]
  | .tbytes => [.tbytes, .tint, .tbool, .tany]
  | _ => []

/-- The tags whose `+` concatenates and whose `*` repeats, from CPython 3.13.

    `Binary.fallbackImpl` selects the implementation for these, and it is already
    table-shaped -- what it lacked was a statement of which tags belong in it.
    `bytes` was missing, so `b"a" + b"b"` was a TypeError, and nothing could
    notice because a missing arm and a genuinely unsupported operand are the same
    `none`. Declaring the set separately makes the omission checkable:
    `Tests/ShapePolicy.lean` asserts `fallbackImpl` answers for each.

    This is not the same question as `Binary.builtinEffect`'s coverage. The
    effects are *total* functions on tag pairs -- exhaustive matches returning
    `notImpl` -- so they have no missing-row failure mode. Only the selection step
    does. -/
def concatenatingTags : List Tag := [.tstr, .tbytes, .tlist, .ttuple]

def repeatingTags : List Tag := [.tstr, .tbytes, .tlist, .ttuple]

/-- Pairs the table has no row for. Empty by construction, because every arm is an
    exhaustive `match`; computed anyway so the property is asserted rather than
    assumed, and so `RuleValidate` has something to report if the shape of the
    table ever changes. -/
def missingBuiltinOutcomes : List (Tag × BuiltinOp) :=
  builtinTags.flatMap fun tag =>
    allBuiltinOps.filterMap fun operation =>
      let outcome := builtinOutcome tag operation
      -- A row that neither admits a normal completion nor raises anything is not
      -- a row: it claims the operation does nothing at all.
      if outcome.deferred || outcome.admitsNormal || !outcome.raises.isEmpty
      then none else some (tag, operation)

def builtinOutcomeCoverageComplete : Bool := missingBuiltinOutcomes.isEmpty

/-- The protocols dispatched by walking a class's dunders, and the order.

    Two kinds of chain exist and they are not interchangeable. A *static* chain
    advances because the method is absent from the MRO, decided before anything
    runs: `x in c` picks its method by what `type(c)` defines. A *runtime* chain
    advances because a candidate returned `NotImplemented`: `a + b` runs `__add__`
    and only then tries `__radd__`.

    Only the static ones belong here. The runtime chain's order is already data in
    `Binary.candidates`, and its advance rule has one definition in `binaryPair`.

    Being data was not enough on its own: a new protocol could still arrive
    hand-sequenced, with its order carried by nesting the way these two were.
    `RuleValidate` counts this list, so a protocol without a declared chain is
    visible. -/
inductive DunderProtocol
  | truth
  | membership
deriving Repr, BEq, Inhabited

def DunderProtocol.render : DunderProtocol -> String
  | .truth => "truth"
  | .membership => "membership"

/-- The chain for each protocol, in CPython's order. -/
def DunderProtocol.chain : DunderProtocol -> List String
  | .truth => ["__bool__", "__len__"]
  | .membership => ["__contains__", "__iter__", "__getitem__"]

def allDunderProtocols : List DunderProtocol := [.truth, .membership]

/-- A protocol whose chain is empty has no declared order, which means its
    dispatch is still sequenced somewhere by hand. -/
def undeclaredDunderChains : List DunderProtocol :=
  allDunderProtocols.filter fun protocol => protocol.chain.isEmpty

def dunderChainCoverageComplete : Bool := undeclaredDunderChains.isEmpty

/-- The transfer logic that stays hand-written, each with the reason.

    Distinct from the `engine-body` count in `RuleValidate`, which counts *syntax
    kinds* declared as escapes under ENGINE.md section 3, "What has to stay
    hard-coded, and why" -- a different
    population entirely. These are the protocol transfers that no table can
    express, and naming them here turns "three engine bodies remain" from a claim
    in a plan document into a list a condition can count.

    A fourth entry is not forbidden. It has to be argued for in this list, which
    is the point: the failure mode being prevented is logic staying hand-written
    because nobody noticed, not because someone decided. -/
def transferEngineBodies : List (String × String) :=
  [ ("narrowReceiver",
     "needs the receiver's syntax to narrow a variable on an exceptional edge, \
      not its value, so no value-keyed table can express it")
  , ("annEntailedDeep",
     "a fuel-bounded recursive descent over an annotation and the heap it \
      describes; the recursion is the content, not a row")
  , ("heap-shape queries",
     "allKeysPresent and the per-key cell walks ask questions of the state, so \
      their answers are not properties of a tag") ]

end Pylate
