/-
CPython-ordered binary dispatch shared by both executable analyzers.

The planner identifies builtin numeric slots separately from the sequence
fallbacks used by + and *. Every candidate has three possible abstract
completions: a normal value, an exception, or NotImplemented. Only the last
completion advances to the next candidate.
-/
import Pylate.Machine

namespace Pylate
namespace Binary

inductive BuiltinImpl
  | intNumber
  | floatNumber
  | complexNumber
  | strFormat
  | setNumber
  | dictUnion
  | keysNumber
  | itemsNumber
  | typeUnion
  | scalarConcat (tag : Tag)
  | scalarRepeat (tag : Tag) (countOnRight : Bool)
  | sequenceConcat (cls : LocCls)
  | sequenceRepeat (cls : LocCls) (countOnRight : Bool)
deriving Repr, DecidableEq

def BuiltinImpl.label : BuiltinImpl → String
  | .intNumber => "builtin int numeric slot"
  | .floatNumber => "builtin float numeric slot"
  | .complexNumber => "builtin complex numeric slot"
  | .strFormat => "builtin str.__mod__"
  | .setNumber => "builtin set numeric slot"
  | .dictUnion => "builtin dict.__or__"
  | .keysNumber => "builtin dict_keys numeric slot"
  | .itemsNumber => "builtin dict_items numeric slot"
  | .typeUnion => "builtin type union slot"
  | .scalarConcat tag => s!"builtin {tag.render} concatenation"
  | .scalarRepeat tag _ => s!"builtin {tag.render} repetition"
  | .sequenceConcat cls => s!"builtin {cls.render} concatenation"
  | .sequenceRepeat cls _ => s!"builtin {cls.render} repetition"

def isArithmetic : BinOp → Bool
  | .add | .sub | .mul | .div | .floordiv | .mod | .pow => true
  | _ => false

def isComplexArithmetic : BinOp → Bool
  | .add | .sub | .mul | .div | .pow => true
  | _ => false

def isSetOperator : BinOp → Bool
  | .sub | .bitAnd | .bitOr | .bitXor => true
  | _ => false

def isIntegral : Tag → Bool
  | .tbool | .tint => true
  | _ => false

def isNumeric : Tag → Bool
  | .tbool | .tint | .tfloat | .tcomplex => true
  | _ => false

def isIterable : Tag → Bool
  | .tstr | .tlist | .tdict | .tdictkeys | .tdictitems | .tdictvalues
  | .tset | .ttuple | .trange | .tgen => true
  | _ => false

def isSetLike : Tag → Bool
  | .tset | .tdictkeys | .tdictitems => true
  | _ => false

def forwardImpl (op : BinOp) : Tag → Option BuiltinImpl
  | .tbool | .tint => if isArithmetic op || op == .bitAnd ||
      op == .bitOr || op == .bitXor || op == .lshift || op == .rshift
    then some .intNumber else none
  | .tfloat => if isArithmetic op then some .floatNumber else none
  | .tcomplex => if isComplexArithmetic op then some .complexNumber else none
  | .tstr => if op == .mod then some .strFormat else none
  | .tset => if isSetOperator op then some .setNumber else none
  | .tdict => if op == .bitOr then some .dictUnion else none
  | .tdictkeys => if isSetOperator op then some .keysNumber else none
  | .tdictitems => if isSetOperator op then some .itemsNumber else none
  | .ttype | .tunion => if op == .bitOr then some .typeUnion else none
  | _ => none

def reflectedImpl (op : BinOp) : Tag → Option BuiltinImpl
  | .tbool | .tint => if isArithmetic op || op == .bitAnd ||
      op == .bitOr || op == .bitXor || op == .lshift || op == .rshift
    then some .intNumber else none
  | .tfloat => if isArithmetic op then some .floatNumber else none
  | .tcomplex => if isComplexArithmetic op then some .complexNumber else none
  | .tset => if isSetOperator op then some .setNumber else none
  | .tdict => if op == .bitOr then some .dictUnion else none
  | .tdictkeys => if isSetOperator op then some .keysNumber else none
  | .tdictitems => if isSetOperator op then some .itemsNumber else none
  | .ttype | .tunion => if op == .bitOr then some .typeUnion else none
  | _ => none

inductive ResultSpec
  | scalar (tags : Fset Tag)
  | sequence (cls : LocCls) (leftElems rightElems : Bool)
  | setValue
  | dictValue
  | typeUnion
  | formattedString
deriving Repr, Inhabited

structure Effect where
  results : List ResultSpec := []
  raises : Fset String := []
  notImplemented : Bool := false
deriving Repr, Inhabited

def notImpl : Effect := { notImplemented := true }

def intEffect (op : BinOp) (left right : Tag) : Effect :=
  if !isIntegral left || !isIntegral right then notImpl
  else
    match op with
    | .add | .sub | .mul =>
      { results := [.scalar [.tint]] }
    | .div =>
      { results := [.scalar [.tfloat]], raises := ["ZeroDivisionError"] }
    | .floordiv | .mod =>
      { results := [.scalar [.tint]], raises := ["ZeroDivisionError"] }
    | .pow =>
      let exponentCanBeNegative := right == .tint
      let tags : Fset Tag := if exponentCanBeNegative
        then [.tint, .tfloat] else [.tint]
      { results := [.scalar tags]
        raises := if exponentCanBeNegative then ["ZeroDivisionError"] else [] }
    | .bitAnd | .bitOr | .bitXor =>
      let result := if left == .tbool && right == .tbool
        then Tag.tbool else Tag.tint
      { results := [.scalar [result]] }
    | .lshift =>
      { results := [.scalar [.tint]]
        raises := if right == .tint
          then ["ValueError", "OverflowError"] else [] }
    | .rshift =>
      { results := [.scalar [.tint]]
        raises := if right == .tint then ["ValueError"] else [] }

def floatEffect (op : BinOp) (left right : Tag) : Effect :=
  if !isNumeric left || !isNumeric right ||
      left == .tcomplex || right == .tcomplex then notImpl
  else
    match op with
    | .add | .sub | .mul => { results := [.scalar [.tfloat]] }
    | .div | .floordiv | .mod =>
      { results := [.scalar [.tfloat]], raises := ["ZeroDivisionError"] }
    | .pow =>
      let exponentIsBool := right == .tbool
      let mayBeComplex := !exponentIsBool && right == .tfloat
      { results := [.scalar (if mayBeComplex
          then [.tfloat, .tcomplex] else [.tfloat])]
        raises := if exponentIsBool then []
          else ["ZeroDivisionError", "OverflowError"] }
    | _ => notImpl

def complexEffect (op : BinOp) (left right : Tag) : Effect :=
  if !isNumeric left || !isNumeric right then notImpl
  else
    match op with
    | .add | .sub | .mul => { results := [.scalar [.tcomplex]] }
    | .div =>
      { results := [.scalar [.tcomplex]], raises := ["ZeroDivisionError"] }
    | .pow =>
      { results := [.scalar [.tcomplex]]
        raises := ["ZeroDivisionError", "OverflowError"] }
    | _ => notImpl

def viewEffect (viewTag left right : Tag) : Effect :=
  let other := if left == viewTag then right else left
  if isIterable other then
    { results := [.setValue]
      -- Items and arbitrary iterables may expose unhashable elements.
      raises := if viewTag == .tdictkeys && isSetLike other
        then [] else ["TypeError"] }
  else if let .tobj _ := other then
    { results := [.setValue], raises := ["TypeError"] }
  else if other == .tany then
    { results := [.setValue], raises := ["TypeError"] }
  else
    { raises := ["TypeError"] }

def builtinEffect (impl : BuiltinImpl) (op : BinOp)
    (left right : Tag) : Effect :=
  match impl with
  | .intNumber => intEffect op left right
  | .floatNumber => floatEffect op left right
  | .complexNumber => complexEffect op left right
  | .strFormat => { results := [.formattedString] }
  | .setNumber =>
    if isSetLike left && isSetLike right then
      { results := [.setValue]
        raises := if left == .tdictitems || right == .tdictitems
          then ["TypeError"] else [] }
    else notImpl
  | .dictUnion =>
    if left == .tdict && right == .tdict
    then { results := [.dictValue] } else notImpl
  | .keysNumber => viewEffect .tdictkeys left right
  | .itemsNumber => viewEffect .tdictitems left right
  | .typeUnion =>
    if (left == .ttype || left == .tunion || left == .tnone) &&
        (right == .ttype || right == .tunion || right == .tnone) then
      { results := [.typeUnion] }
    else notImpl
  | .scalarConcat tag =>
    if left == tag && right == tag then
      { results := [.scalar [tag]] }
    else
      { raises := ["TypeError"] }
  | .scalarRepeat .. => notImpl -- handled with __index__ below
  | .sequenceConcat cls =>
    let expected := cls.tag
    if left == expected && right == expected then
      { results := [.sequence cls true true] }
    else
      { raises := ["TypeError"] }
  | .sequenceRepeat .. => notImpl -- handled with __index__ below

def fallbackImpl (op : BinOp) (left right : Tag) : Option BuiltinImpl :=
  match op with
  | .add =>
    match left with
    | .tstr => some (.scalarConcat .tstr)
    | .tbytes => some (.scalarConcat .tbytes)
    | .tlist => some (.sequenceConcat .list)
    | .ttuple => some (.sequenceConcat .tuple)
    | _ => none
  | .mul =>
    match left, right with
    | .tstr, _ => some (.scalarRepeat .tstr true)
    | .tbytes, _ => some (.scalarRepeat .tbytes true)
    | .tlist, _ => some (.sequenceRepeat .list true)
    | .ttuple, _ => some (.sequenceRepeat .tuple true)
    | _, .tstr => some (.scalarRepeat .tstr false)
    | _, .tbytes => some (.scalarRepeat .tbytes false)
    | _, .tlist => some (.sequenceRepeat .list false)
    | _, .ttuple => some (.sequenceRepeat .tuple false)
    | _, _ => none
  | _ => none

inductive Candidate
  | builtin (impl : BuiltinImpl)
  | user (label : String) (fn : FuncDef) (self other : AbsVal)

def Candidate.label : Candidate → String
  | .builtin impl => impl.label
  | .user label .. => label

def Candidate.key : Candidate → String
  | .builtin impl => s!"builtin:{repr impl}"
  | .user label .. => s!"user:{label}"

def addCandidate (xs : List Candidate) (candidate : Option Candidate) :
    List Candidate :=
  match candidate with
  | none => xs
  | some candidate =>
    if xs.any (·.key == candidate.key) then xs else xs ++ [candidate]

def builtinCandidate (impl : Option BuiltinImpl) : Option Candidate :=
  impl.map Candidate.builtin

partial def userCandidate (cn method : String) (self other : AbsVal) :
    M (Option Candidate) := do
  match ← resolveMethodM cn method with
  | some (owner, fn) =>
    pure (some (.user s!"{owner}.{fn.name}" fn self other))
  | none => pure none

/-- The generic binary protocol, before + concatenation or * repetition. -/
partial def candidates (op : BinOp) (leftTag rightTag : Tag)
    (left right : AbsVal) : M (List Candidate) := do
  let c ← get
  let leftV := left.restrictTags [leftTag]
  let rightV := right.restrictTags [rightTag]
  let forward ← match leftTag with
    | .tobj cn => userCandidate cn op.dunder leftV rightV
    | t => pure (builtinCandidate (forwardImpl op t))
  let reflected ← match rightTag with
    | .tobj rn =>
      match leftTag with
      | .tobj ln =>
        if rn == ln then pure none
        else userCandidate rn op.reflectedDunder rightV leftV
      | _ => userCandidate rn op.reflectedDunder rightV leftV
    | t => pure (builtinCandidate (reflectedImpl op t))
  let reflectedFirst : Bool := match leftTag, rightTag, reflected with
    | .tobj ln, .tobj rn, some (.user owner _ _ _) =>
      !(rn == ln) && owner.startsWith s!"{rn}." &&
        (c.classes.getCls? rn).any (fun ci => ci.mro.contains ln)
    | _, _, _ => false
  if reflectedFirst then
    pure (addCandidate (addCandidate [] reflected) forward)
  else
    pure (addCandidate (addCandidate [] forward) reflected)

-- ---------------------------------------------------------- %-formatting

structure PercentInfo where
  conversions : Fset Char := []
  mapping : Bool := false
  malformed : Bool := false
deriving Repr, Inhabited

def PercentInfo.join (a b : PercentInfo) : PercentInfo where
  conversions := Fset.union a.conversions b.conversions
  mapping := a.mapping || b.mapping
  malformed := a.malformed || b.malformed

def conversionChars : Fset Char :=
  ['d', 'i', 'u', 'o', 'x', 'X', 'e', 'E', 'f', 'F', 'g', 'G',
   'c', 'r', 's', 'a']

def formatSyntaxChars : Fset Char :=
  ['#', '0', '-', ' ', '+', '.', '*', 'h', 'l', 'L',
   '1', '2', '3', '4', '5', '6', '7', '8', '9']

partial def dropMapping : List Char → Option (List Char)
  | [] => none
  | ')' :: rest => some rest
  | _ :: rest => dropMapping rest

partial def takeConversion (chars : List Char) (invalid : Bool := false) :
    Option (Char × List Char × Bool) :=
  match chars with
  | [] => none
  | c :: rest =>
    if c ∈ conversionChars then some (c, rest, invalid)
    else takeConversion rest (invalid || !(c ∈ formatSyntaxChars))

partial def percentInfoChars : List Char → PercentInfo
  | [] => {}
  | '%' :: '%' :: rest => percentInfoChars rest
  | '%' :: '(' :: rest =>
    match dropMapping rest with
    | none => { mapping := true, malformed := true }
    | some tail =>
      match takeConversion tail with
      | none => { mapping := true, malformed := true }
      | some (conv, after, invalid) =>
        (PercentInfo.mk [conv] true invalid).join
          (percentInfoChars after)
  | '%' :: rest =>
    match takeConversion rest with
    | none => { malformed := true }
    | some (conv, after, invalid) =>
      (PercentInfo.mk [conv] false invalid).join
        (percentInfoChars after)
  | _ :: rest => percentInfoChars rest

def percentInfo (format : String) : PercentInfo :=
  percentInfoChars format.toList

def isStringConversion (c : Char) : Bool :=
  c == 's' || c == 'r' || c == 'a'

def isIntegerConversion (c : Char) : Bool :=
  c == 'd' || c == 'i' || c == 'u' || c == 'o' ||
  c == 'x' || c == 'X'

def isDecimalConversion (c : Char) : Bool :=
  c == 'd' || c == 'i' || c == 'u'

def isFloatConversion (c : Char) : Bool :=
  c == 'e' || c == 'E' || c == 'f' || c == 'F' ||
  c == 'g' || c == 'G'

structure FormatSummary where
  normal : Bool := false
  raises : Fset String := []
  hooks : Fset String := []
  requiredHooks : Fset String := []
deriving Repr, Inhabited

def formatHooks (info : PercentInfo) : Fset String := Id.run do
  let mut hooks : Fset String := []
  if info.mapping then hooks := Fset.insert "__getitem__" hooks
  for conv in info.conversions do
    if conv == 's' then hooks := Fset.insert "__str__" hooks
    if conv == 'r' || conv == 'a' then
      hooks := Fset.insert "__repr__" hooks
    if isIntegerConversion conv || conv == 'c' then
      hooks := Fset.insert "__index__" (Fset.insert "__int__" hooks)
    if isFloatConversion conv then
      hooks := Fset.insert "__float__" hooks
  return hooks

def plainFormatSummary (right : Tag) : FormatSummary :=
  match right with
  | .tlist | .tdict | .trange => { normal := true }
  | .ttuple => { normal := true, raises := ["TypeError"] }
  | .tobj _ => { normal := true, raises := ["TypeError"] }
  | .tany => { normal := true, raises := ["TypeError"] }
  | _ => { raises := ["TypeError"] }

def oneConversionSummary (conv : Char) (right : Tag) : FormatSummary :=
  let hooks := formatHooks { conversions := [conv] }
  let requiredHooks := if isStringConversion conv then hooks else []
  if isStringConversion conv then
    match right with
    | .ttuple =>
      { normal := true, raises := ["TypeError"], hooks, requiredHooks }
    | .tobj _ =>
      { normal := true, raises := ["TypeError"], hooks, requiredHooks }
    | _ => { normal := true, hooks, requiredHooks }
  else if isIntegerConversion conv then
    match right with
    | .tbool | .tint => { normal := true, raises := ["OverflowError"] }
    | .tfloat =>
      if isDecimalConversion conv then
        { normal := true, raises := ["ValueError", "OverflowError"] }
      else
        { raises := ["TypeError"] }
    | .ttuple | .tobj _ =>
      { normal := true, raises := ["TypeError", "OverflowError"], hooks }
    | _ => { raises := ["TypeError"], hooks }
  else if isFloatConversion conv then
    match right with
    | .tbool | .tint | .tfloat =>
      { normal := true, raises := ["OverflowError"] }
    | .ttuple | .tobj _ =>
      { normal := true, raises := ["TypeError", "OverflowError"], hooks }
    | _ => { raises := ["TypeError"], hooks }
  else -- %c
    match right with
    | .tbool | .tint =>
      { normal := true, raises := ["OverflowError"], hooks }
    | .tstr | .ttuple | .tobj _ =>
      { normal := true, raises := ["TypeError", "OverflowError"], hooks }
    | _ => { raises := ["TypeError"], hooks }

def formatInfoSummary (info : PercentInfo) (right : Tag) : FormatSummary :=
  if info.malformed then
    { raises := ["ValueError"], hooks := formatHooks info }
  else if info.conversions.isEmpty then
    plainFormatSummary right
  else if info.mapping then
    let hooks : Fset String := ["__getitem__"]
    let requiredHooks : Fset String := ["__getitem__"]
    match right with
    | .tdict =>
      { normal := true, raises := ["KeyError", "TypeError", "OverflowError"],
        hooks, requiredHooks }
    | .tobj _ =>
      { normal := true, raises := ["KeyError", "TypeError", "OverflowError"],
        hooks, requiredHooks }
    | .tany =>
      { normal := true, raises := ["KeyError", "TypeError", "OverflowError"],
        hooks, requiredHooks }
    | _ => { raises := ["TypeError"], hooks, requiredHooks }
  else
    match info.conversions with
    | [conv] => oneConversionSummary conv right
    | _ =>
      { normal := right == .ttuple || right == .tany
        raises := ["TypeError", "OverflowError"]
        hooks := formatHooks info }

def unknownFormatSummary : FormatSummary :=
  { normal := true
    raises := ["TypeError", "ValueError", "OverflowError", "KeyError"]
    hooks := ["__str__", "__repr__", "__index__", "__int__", "__float__",
      "__getitem__"] }

def mappingValues (st : AState) (mapping : AbsVal) : AbsVal :=
  mapping.locs.foldl (fun out location =>
    match location.cls with
    | .dict | .td _ => out.join (st.heapGet location .dictValues)
    | _ => out) AbsVal.bot

-- ----------------------------------------------------------- execution

abbrev InlineFn :=
  Pos → String → FuncDef → List AbsVal → List (String × AbsVal) →
    AState → M Flow

partial def executeNeg (inline : InlineFn) (p : Pos) (value : AbsVal)
    (st : AState) : M Flow := do
  let mut out := AbsVal.bot
  let mut outSt : Option AState := none
  let mut exc : Exc := {}
  for tag in value.tags do
    let input := value.restrictTags [tag]
    match tag with
    | .tbool | .tint =>
      resCase p "unary" "unary USub" (Tag.render tag)
        "builtin int.__neg__"
      out := out.join (V [.tint])
      outSt := joinOpt outSt (some st)
    | .tfloat =>
      resCase p "unary" "unary USub" (Tag.render tag)
        "builtin float.__neg__"
      out := out.join (V [.tfloat])
      outSt := joinOpt outSt (some st)
    | .tcomplex =>
      resCase p "unary" "unary USub" (Tag.render tag)
        "builtin complex.__neg__"
      out := out.join (V [.tcomplex])
      outSt := joinOpt outSt (some st)
    | .tobj cn =>
      match ← resolveMethodM cn "__neg__" with
      | some (owner, fn) =>
        let r ← inline p s!"{owner}.{fn.name}" fn [input] [] st
        resCase p "unary" "unary USub" (Tag.render tag)
          s!"{owner}.{fn.name}"
        out := out.join r.val
        if let some (_, normalState) := r.normal then
          outSt := joinOpt outSt (some normalState)
        exc := exc.joinE r.exc
        for raised in r.exc.tags do
          resCase p "unary" "unary USub" (Tag.render tag) s!"!{raised}"
      | none =>
        resCase p "unary" "unary USub" (Tag.render tag) "!TypeError"
        exc ← mraise p exc st ["TypeError"]
    | .tany =>
      resCase p "unary" "unary USub" "any" "deferred"
      oblige p "dispatch-any" "unary - has an unknown operand"
      out := out.join anyV
      outSt := joinOpt outSt (some st)
    | _ =>
      resCase p "unary" "unary USub" (Tag.render tag) "!TypeError"
      exc ← mraise p exc st ["TypeError"]
  pure {
    normal := match outSt with
      | some state => some (out.reduce, state)
      | none => none
    raised := exc
  }

structure Step where
  val : AbsVal := AbsVal.bot
  normalSt : Option AState := none
  continueSt : Option AState := none
  exc : Exc := {}
  raised : Fset String := []
  route : Option String := none
deriving Inhabited

def Step.join (left right : Step) : Step where
  val := left.val.join right.val
  normalSt := joinOpt left.normalSt right.normalSt
  continueSt := joinOpt left.continueSt right.continueSt
  exc := left.exc.joinE right.exc
  raised := Fset.union left.raised right.raised
  route := if left.route == right.route then left.route else none

def freshSequence (p : Pos) (cls : LocCls) (elem : AbsVal)
    (st : AState) : AbsVal × AState :=
  if cls == .list then
    let (v, st') := allocate st p.id .list []
    (v, st'.heapSet ⟨p.id, .list, true⟩ .elem elem)
  else
    let (v, st') := allocate st p.id .tuple []
    (v, st'.heapSet ⟨p.id, .tuple, true⟩ .elem elem)

def materialize (p : Pos) (spec : ResultSpec) (left right : AbsVal)
    (st : AState) : AbsVal × AState :=
  match spec with
  | .scalar tags => (V tags, st)
  | .sequence cls useLeft useRight =>
    let le := if useLeft then elemOf st left else AbsVal.bot
    let re := if useRight then elemOf st right else AbsVal.bot
    freshSequence p cls (le.join re) st
  | .setValue =>
    let (v, st') := allocate st p.id .set []
    let elem0 := (elemOf st left).join (elemOf st right)
    let hasUnknownIterable := (left.tags ++ right.tags).any (fun tag =>
      tag == .tany || match tag with | .tobj _ => true | _ => false)
    let elem := if hasUnknownIterable then elem0.join anyV else elem0
    (v, st'.heapSet ⟨p.id, .set, true⟩ .elem elem)
  | .dictValue =>
    let (v, st') := allocate st p.id .dict []
    let l : Loc := ⟨p.id, .dict, true⟩
    let keys := (left.locs.foldl (fun out loc =>
      if loc.cls.tag == .tdict then out.join (st.heapGet loc .dictKeys) else out)
      AbsVal.bot).join
      (right.locs.foldl (fun out loc =>
        if loc.cls.tag == .tdict then out.join (st.heapGet loc .dictKeys) else out)
        AbsVal.bot)
    let vals := (left.locs.foldl (fun out loc =>
      if loc.cls.tag == .tdict then out.join (st.heapGet loc .dictValues) else out)
      AbsVal.bot).join
      (right.locs.foldl (fun out loc =>
        if loc.cls.tag == .tdict then out.join (st.heapGet loc .dictValues) else out)
        AbsVal.bot)
    (v, (st'.heapSet l .dictKeys keys).heapSet l .dictValues vals)
  | .typeUnion =>
    if Tag.tunion ∈ left.tags || Tag.tunion ∈ right.tags ||
        Tag.tnone ∈ left.tags || Tag.tnone ∈ right.tags then
      (V [.tunion], st)
    else
      let common := Fset.inter left.classes right.classes
      let same := if common.isEmpty then AbsVal.bot
        else V [.ttype] (classes := common)
      let definitelySame := left.classes.length == 1 &&
        right.classes.length == 1 && left.classes == right.classes
      let different := if definitelySame then AbsVal.bot else V [.tunion]
      (same.join different |>.reduce, st)
  | .formattedString => (V [.tstr], st)

partial def definitelyHashable (st : AState) (value : AbsVal)
    (fuel : Nat := 8) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    value.tags.all fun tag =>
      match tag with
      | .tnone | .tbool | .tint | .tfloat | .tcomplex | .tstr | .tbytes
      | .trange | .tgen | .ttype | .tunion | .tfunc | .tnotimpl => true
      | .ttuple =>
        let locations := value.locs.filter (·.cls == LocCls.tuple)
        !locations.isEmpty && locations.all (fun location =>
          definitelyHashable st (st.heapGet location .elem) fuel)
      | .tobj _ | .tany => false
      | .tlist | .tdict | .tdictkeys | .tdictitems | .tdictvalues
      | .tset | .tunbound | .tuninit | .tmissing => false

def iterableElementsHashable (st : AState) (value : AbsVal) : Bool :=
  value.tags.all fun tag =>
    match tag with
    | .tstr | .tdict | .tdictkeys | .tset | .trange => true
    | .tlist | .ttuple | .tgen | .tdictitems | .tdictvalues =>
      definitelyHashable st (elemOf st (value.restrictTags [tag]))
    | _ => false

partial def executeHooks (inline : InlineFn) (p : Pos)
    (hooks requiredHooks : Fset String) (right : AbsVal) (st : AState) :
    M (AState × Bool × AbsVal × Exc × Fset String) := do
  let mut outSt := st
  let mut normal := requiredHooks.isEmpty || right.tags.any (fun tag =>
    match tag with | .tobj _ => false | _ => true)
  let mut values := AbsVal.bot
  let mut exc : Exc := {}
  let mut raised : Fset String := []
  for tag in right.tags do
    if let .tobj cn := tag then
      let mut tagNormal := true
      for hook in hooks do
        match ← resolveMethodM cn hook with
        | some (owner, fn) =>
          let args := if hook == "__getitem__"
            then [right.restrictTags [tag], V [.tstr]]
            else [right.restrictTags [tag]]
          let r ← inline p s!"{owner}.{fn.name}" fn
            args [] st
          if let some (_, normalState) := r.normal then
            outSt := outSt.join normalState
          exc := exc.joinE r.exc
          raised := Fset.union r.exc.tags raised
          if hook == "__getitem__" then
            values := values.join r.val
          if r.val.isBot then
            tagNormal := false
        | none =>
          if hook ∈ requiredHooks && hook == "__getitem__" then
            tagNormal := false
      normal := normal || tagNormal
  pure (outSt, normal, values.reduce, exc, raised)

def conversionMethods (conversion : Char) :
    List (String × Fset Tag) :=
  if conversion == 's' then
    [("__str__", [.tstr])]
  else if conversion == 'r' || conversion == 'a' then
    [("__repr__", [.tstr])]
  else if isDecimalConversion conversion then
    [("__int__", [.tbool, .tint]), ("__index__", [.tbool, .tint])]
  else if isIntegerConversion conversion || conversion == 'c' then
    [("__index__", [.tbool, .tint])]
  else if isFloatConversion conversion then
    [("__float__", [.tfloat]), ("__index__", [.tbool, .tint])]
  else
    []

def conversionHasDefault (conversion : Char) : Bool :=
  isStringConversion conversion

def builtinConversionNormal (conversion : Char) (tag : Tag) : Bool :=
  if isStringConversion conversion then
    tag != .tunbound && tag != .tuninit && tag != .tmissing
  else if isDecimalConversion conversion then
    tag == .tbool || tag == .tint || tag == .tfloat
  else if isIntegerConversion conversion then
    tag == .tbool || tag == .tint
  else if isFloatConversion conversion then
    tag == .tbool || tag == .tint || tag == .tfloat
  else -- %c
    tag == .tbool || tag == .tint || tag == .tstr

/-- Execute the conversion protocol on a value that occupies one format
    argument slot. Fallback methods are ordered, so an available `__int__`
    suppresses `__index__`, and an available `__float__` does likewise. -/
partial def executeConversion (inline : InlineFn) (p : Pos)
    (conversion : Char) (value : AbsVal) (st : AState) :
    M (AState × Bool × Exc × Fset String) := do
  let mut outSt : Option AState := none
  let mut normal := false
  let mut exc : Exc := {}
  let mut raised : Fset String := []
  for tag in value.tags do
    match tag with
    | .tobj cn =>
      let mut chosen :
          Option (String × String × FuncDef × Fset Tag) := none
      for (method, expected) in conversionMethods conversion do
        if chosen.isNone then
          match ← resolveMethodM cn method with
          | some (owner, fn) =>
            chosen := some (method, owner, fn, expected)
          | none => pure ()
      match chosen with
      | some (_, owner, fn, expected) =>
        let r ← inline p s!"{owner}.{fn.name}" fn
          [value.restrictTags [tag]] [] st
        let unknown := Tag.tany ∈ r.val.tags
        let good := unknown || !(r.val.restrictTags expected).isBot
        let bad := unknown || !(r.val.withoutTags expected).isBot
        let hookState := (r.normal.map (·.2)).getD st
        if good then
          normal := true
          outSt := joinOpt outSt (some hookState)
        exc := exc.joinE r.exc
        raised := Fset.union r.exc.tags raised
        if bad then
          exc ← mraise p exc hookState ["TypeError"]
          raised := Fset.insert "TypeError" raised
      | none =>
        if conversionHasDefault conversion then
          normal := true
          outSt := joinOpt outSt (some st)
        else
          exc ← mraise p exc st ["TypeError"]
          raised := Fset.insert "TypeError" raised
    | .tany =>
      oblige p "dispatch-any"
        "string-format conversion has an unknown operand"
      normal := true
      outSt := joinOpt outSt (some st)
      raised := Fset.union
        ["TypeError", "ValueError", "OverflowError"] raised
      exc ← mraise p exc st ["TypeError", "ValueError", "OverflowError"]
    | _ =>
      if builtinConversionNormal conversion tag then
        normal := true
        outSt := joinOpt outSt (some st)
      else
        exc ← mraise p exc st ["TypeError"]
        raised := Fset.insert "TypeError" raised
  pure (outSt.getD st, normal, exc, raised)

partial def executeFormatArm (inline : InlineFn) (p : Pos)
    (info : PercentInfo) (summary0 : FormatSummary) (right : AbsVal)
    (rightTag : Tag) (st : AState) : M Step := do
  let mut summary := summary0
  if let .tobj cn := rightTag then
    if info.conversions.isEmpty && !info.malformed &&
        (← resolveMethodM cn "__getitem__").isNone then
      summary := { summary with normal := false }
  let hookTarget := if info.mapping then right
    else if rightTag == .ttuple then elemOf st right
    else right
  let singleConversion := match info.conversions with
    | [conversion] => some conversion
    | _ => none
  let (hookSt, hooksReturn, fetched, hookExc, hookRaised) ←
    if info.mapping then
      executeHooks inline p summary.hooks summary.requiredHooks hookTarget st
    else
      match singleConversion with
      | some conversion => do
        let (post, normal, exc, raised) ←
          executeConversion inline p conversion hookTarget st
        pure (post, normal, AbsVal.bot, exc, raised)
      | none =>
        executeHooks inline p summary.hooks summary.requiredHooks hookTarget st
  let converted := fetched.join (mappingValues hookSt right) |>.reduce
  let conversionHooks := Fset.diff (formatHooks info) ["__getitem__"]
  let requiredConversionHooks := conversionHooks.filter (fun hook =>
    hook == "__str__" || hook == "__repr__")
  let (postSt, conversionsReturn, _, conversionExc, conversionRaised) ←
    if info.mapping && !converted.isBot then
      match singleConversion with
      | some conversion => do
        let (post, normal, exc, raised) ←
          executeConversion inline p conversion converted hookSt
        pure (post, normal, AbsVal.bot, exc, raised)
      | none =>
        executeHooks inline p conversionHooks requiredConversionHooks
          converted hookSt
    else
      pure (hookSt, true, AbsVal.bot, {}, [])
  let protocolsReturn := hooksReturn && conversionsReturn
  let machineExc ← if protocolsReturn then
      mraise p {} postSt summary.raises
    else pure {}
  let normal := summary.normal && protocolsReturn
  pure {
    val := if normal then V [.tstr] else AbsVal.bot
    normalSt := if normal then some postSt else none
    exc := (machineExc.joinE hookExc).joinE conversionExc
    raised := Fset.union summary.raises
      (Fset.union hookRaised conversionRaised)
  }

partial def executeFormat (inline : InlineFn) (p : Pos)
    (left right : AbsVal) (rightTag : Tag) (st : AState) : M Step := do
  let mut out : Step := {}
  for literal in left.strLits do
    let info := percentInfo literal
    let step ← executeFormatArm inline p info
      (formatInfoSummary info rightTag) right rightTag st
    out := out.join step
  if left.strOpen then
    let step ← executeFormatArm inline p {} unknownFormatSummary
      right rightTag st
    out := out.join step
  pure out

partial def executeRepeat (inline : InlineFn) (p : Pos) (routeLabel : String)
    (cls : LocCls) (scalar : Option Tag) (countOnRight : Bool)
    (left right : AbsVal) (leftTag rightTag : Tag) (st : AState) : M Step := do
  let count := if countOnRight then right else left
  let countTag := if countOnRight then rightTag else leftTag
  let sequence := if countOnRight then left else right
  let normalResult := fun (post : AState) =>
    -- A repeated str or bytes is a new immutable scalar, so it allocates
    -- nothing; a repeated list or tuple is a fresh heap object.
    match scalar with
    | some tag => (V [tag], post)
    | none => freshSequence p cls (elemOf post sequence) post
  match countTag with
  | .tbool =>
    let (v, post) := normalResult st
    pure { val := v, normalSt := some post }
  | .tint =>
    let (v, post) := normalResult st
    let raises : Fset String := ["OverflowError"]
    let exc ← mraise p {} st raises
    pure { val := v, normalSt := some post, exc, raised := raises }
  | .tobj cn =>
    match ← resolveMethodM cn "__index__" with
    | none =>
      let exc ← mraise p {} st ["TypeError"]
      pure { exc, raised := ["TypeError"] }
    | some (owner, fn) =>
      let r ← inline p s!"{owner}.{fn.name}" fn
        [count.restrictTags [countTag]] [] st
      let good := r.val.restrictTags [.tbool, .tint]
      let bad := r.val.withoutTags [.tbool, .tint]
      let (value, normalSt) :=
        match r.normal with
        | some (_, hookState) =>
          if good.isBot then (AbsVal.bot, none)
          else
            let (v, post) := normalResult hookState
            (v, some post)
        | none => (AbsVal.bot, none)
      let staticRaises : Fset String := if r.hasNormal then
          if bad.isBot then ["OverflowError"] else ["TypeError", "OverflowError"]
        else []
      let machineExc : Exc ← if r.hasNormal then
          mraise p {} (r.stateOr st) staticRaises
        else pure ({ } : Exc)
      pure {
        val := value
        normalSt
        exc := (r.exc.joinE machineExc)
        raised := Fset.union r.exc.tags staticRaises
        route := some s!"{routeLabel} via {owner}.{fn.name}"
      }
  | .tany =>
    oblige p "dispatch-any" "sequence repetition count has unknown __index__"
    let (v, post) := normalResult st
    let raises : Fset String := ["TypeError", "OverflowError"]
    let exc ← mraise p {} st raises
    pure { val := v, normalSt := some post, exc, raised := raises }
  | _ =>
    let exc ← mraise p {} st ["TypeError"]
    pure { exc, raised := ["TypeError"] }

partial def executeBuiltin (inline : InlineFn) (p : Pos) (impl : BuiltinImpl)
    (op : BinOp) (left right : AbsVal) (leftTag rightTag : Tag)
    (st : AState) : M Step := do
  match impl with
  | .strFormat => executeFormat inline p left right rightTag st
  | .scalarRepeat tag countOnRight =>
    executeRepeat inline p impl.label .list (some tag) countOnRight
      left right leftTag rightTag st
  | .sequenceRepeat cls countOnRight =>
    executeRepeat inline p impl.label cls none countOnRight
      left right leftTag rightTag st
  | _ =>
    let mut effect0 := builtinEffect impl op leftTag rightTag
    -- `builtinEffect` is a table over tags, so it cannot see that the divisor is
    -- a literal `2`. The values are here, so the raise is filtered here: this is
    -- the rule/transfer split, not an exception to it.
    --
    -- Which operand has to be nonzero depends on the operator. `x / 0` and
    -- `x % 0` are about the right one; `0 ** -1` is about the *left*, since a
    -- nonzero base cannot raise however negative the exponent is.
    if effect0.raises.contains "ZeroDivisionError" then
      let guard := match op with
        | .pow => left.restrictTags [leftTag]
        | _ => right.restrictTags [rightTag]
      if guard.definitelyNonzero then
        effect0 := { effect0 with
          raises := effect0.raises.filter (· != "ZeroDivisionError") }
    let mut protocolSt := st
    let mut protocolExc : Exc := {}
    let mut protocolRaised : Fset String := []
    let mut protocolNormal := true
    let mut route : Option String := none
    if impl == .keysNumber || impl == .itemsNumber then
      let otherTag := if leftTag == .tdictkeys || leftTag == .tdictitems
        then rightTag else leftTag
      let other := if leftTag == .tdictkeys || leftTag == .tdictitems
        then right else left
      if let .tobj cn := otherTag then
        match ← resolveMethodM cn "__iter__" with
        | some (owner, fn) =>
          let r ← inline p s!"{owner}.{fn.name}" fn
            [other.restrictTags [otherTag]] [] st
          if r.hasNormal then
            protocolSt := (r.stateOr st)
          else
            protocolNormal := false
          protocolExc := r.exc
          protocolRaised := r.exc.tags
          route := some s!"{impl.label} via {owner}.{fn.name}"
          if r.val.isBot then
            effect0 := { effect0 with results := [] }
        | none =>
          match ← resolveMethodM cn "__getitem__" with
          | some (owner, fn) =>
            let r ← inline p s!"{owner}.{fn.name}" fn
              [other.restrictTags [otherTag], V [.tint]] [] st
            let leaked := Fset.diff r.exc.tags ["IndexError"]
            let exhausted := r.exc.tags.contains "IndexError"
            let normalState := joinOpt
              (if r.hasNormal then some (r.stateOr st) else none)
              (if exhausted then r.exc.st else none)
            match normalState with
            | some post => protocolSt := post
            | none =>
              protocolNormal := false
              effect0 := { effect0 with results := [] }
            protocolExc := if leaked.isEmpty then {}
              else { r.exc with tags := leaked }
            protocolRaised := leaked
            route := some s!"{impl.label} via {owner}.{fn.name}"
          | none =>
            effect0 := { raises := ["TypeError"] }
    let effect := if "TypeError" ∈ effect0.raises &&
        effect0.results.any (fun result =>
          match result with | .setValue => true | _ => false) &&
        iterableElementsHashable protocolSt left &&
        iterableElementsHashable protocolSt right then
      { effect0 with raises := Fset.diff effect0.raises ["TypeError"] }
    else effect0
    let mut value : AbsVal := AbsVal.bot
    let mut normalSt : Option AState := none
    for result in effect.results do
      let (v, post) := materialize p result left right protocolSt
      value := value.join v
      normalSt := joinOpt normalSt (some post)
    -- Static failures happen after any __iter__/__getitem__ protocol hook.
    -- Their handlers must observe mutations performed by that hook.
    let exc ← if protocolNormal then
        mraise p {} protocolSt effect.raises
      else pure {}
    pure {
      val := value.reduce
      normalSt
      continueSt := if effect.notImplemented && protocolNormal then some st
        else none
      exc := exc.joinE protocolExc
      raised := Fset.union effect.raises protocolRaised
      route
    }

partial def executeCandidate (inline : InlineFn) (p : Pos)
    (candidate : Candidate) (op : BinOp) (left right : AbsVal)
    (leftTag rightTag : Tag) (st : AState) : M Step := do
  match candidate with
  | .builtin impl =>
    executeBuiltin inline p impl op left right leftTag rightTag st
  | .user label fn self other =>
    let r ← inline p label fn [self, other] [] st
    let value := r.val.withoutTags [.tnotimpl]
    pure {
      val := value
      normalSt := if value.isBot then none else some (r.stateOr st)
      continueSt := if Tag.tnotimpl ∈ r.val.tags then some (r.stateOr st) else none
      exc := r.exc
      raised := r.exc.tags
    }

end Binary
end Pylate
