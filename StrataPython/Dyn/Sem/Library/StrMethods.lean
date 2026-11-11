/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Collections
public import StrataPython.Dyn.Sem.Library.ParseTuple
public import StrataPython.Dyn.Sem.Library.Signatures
public import StrataPython.Dyn.Sem.Library.Str

set_option autoImplicit false

/-!
# The methods of `str` that convert their arguments, and `str.join`

Generic over the record, CPython 3.12's case methods, class tests, searches, splits, strips,
padding, `join` and `encode` of `str` (`Objects/unicodeobject.c`, with Argument Clinic's converters), over
the functions of `Str` and `Unicode`. Each binds its arguments with its generated signature
(`Signatures`), converts them in CPython's order, and returns a plain `str`, `list`, `tuple`,
`int` or `bool`; an instance of a `str` subclass gives the same result as its built-in part.
An integer argument goes through `__index__`, which may run user code. `join` gathers the items
of an iterable that is not an exact list or tuple into a list first, as `PySequence_Fast` does,
and that walk is a step machine (`Machines`).
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The text of `self`, which the descriptor check has made a `str`. -/
def selfText [PyReads m V] (self : V) : m String := do
  let some s ← strText? self | PyPure.modelInvariant "a method of str on a value that is not a str"
  return s

/-- A plain `str` of the code points `a`. -/
def charsValue [PyPure m V] (a : Str.Chars) : V := strValue (m := m) (Str.str a)

/-- A plain `list` of `str`s. -/
def strList [PyPure m V] (xs : Array Str.Chars) : m V :=
  PyPure.allocList (xs.map (charsValue (m := m)))

/-- The argument `v` as a C `int`, as Argument Clinic's converter takes it. -/
def cIntArg [PyCalls m V] (v : V) : m Int := do
  let some n ← indexValue? v |
    raiseBuiltin "TypeError" s!"'{← typeName v}' object cannot be interpreted as an integer"
  if n > 2 ^ 31 - 1 || n < -(2 ^ 31) then
    raiseBuiltin "OverflowError" "Python int too large to convert to C int"
  return n

/-- The text of the argument `v`, which must be a `str` (a subclass too); else the `TypeError`
`msg` followed by the name of `v`'s type. -/
def strArg [PyReads m V] (msg : String) (v : V) : m String := do
  if let some s ← strText? v then return s
  raiseBuiltin "TypeError" s!"{msg}{← typeName v}"

/-- The parameters of a call of the method `sig` of the built-in type `t` on `self`, bound by
`sig`. The message of a wrong call of a `METH_O` or `METH_NOARGS` method, and of a keyword to a
positional-only one, names the class: the defining type in an immediate call (`S('a').upper(1)`),
but `type(self)` through a stored bound method (`f = S('a').upper; f(1)`). So such a wrong call on
an instance of a subclass stops with a gap. -/
def bound [PyReads m V] (t : Builtin) (self : V) (sig : BuiltinSig) (args kwargs : V) :
    m (Array (Option V)) := do
  let formFree := sig.style == .keywords || sig.style == .wrapper ||
    (sig.style == .posOnly && (← PyReads.dictLen kwargs) == 0)
  if formFree || (← classIs self t) then return (← bindBuiltinArgs sig args kwargs).params
  tryCatch (return (← bindBuiltinArgs sig args kwargs).params) fun e => do
    if ← isTypeErrorExc e then
      PyPure.gap s!"the message of a wrong call of {t.info.name}.{sig.name} depends on how it is called"
    throw e

/-- The given argument `i` of a binding. -/
def arg [PyPure m V] (ps : Array (Option V)) (i : Nat) : Option V := (ps[i]?).join

/-- The required argument `i` of a binding, which the binder has checked. -/
def req [PyPure m V] (name : String) (ps : Array (Option V)) (i : Nat) : m V := do
  let some v := arg (m := m) ps i | PyPure.modelInvariant s!"{name}: a required argument is missing"
  return v

/-! ## Case and class tests -/

/-- A method with no arguments that maps the text to a new text. -/
def textMethod [PyWrites m V] (sig : BuiltinSig) (f : String → String) (self args kwargs : V) :
    m V := do
  discard <| bound .str self sig args kwargs
  return strValue (m := m) (f (← selfText self))

/-- A method with no arguments that tests the text. -/
def testMethod [PyWrites m V] (sig : BuiltinSig) (p : String → Bool) (self args kwargs : V) :
    m V := do
  discard <| bound .str self sig args kwargs
  return PyPure.imm (m := m) (.bool (p (← selfText self)))

/-! ## Searching -/

/-- The slice bounds of a search, the arguments after the first: `None` or an index each, in
order (`_PyEval_SliceIndex`). -/
def searchBounds [PyCalls m V] (xs : Array V) : m (Option Int × Option Int) := do
  let start ← match xs[1]? with | some v => sliceBound v | none => pure none
  let stop ← match xs[2]? with | some v => sliceBound v | none => pure none
  return (start, stop)

/-- **`find`, `rfind`, `index`, `rindex` and `count`**: the bounds, then the substring, which must
be a `str`. -/
def searchMethod [PyWrites m V] (sig : ParseTupleSig) (self args kwargs : V) : m V := do
  let xs ← parseTupleArgs sig args kwargs
  let (start, stop) ← searchBounds xs
  let some subV := xs[0]? | PyPure.modelInvariant s!"{sig.name}: no substring"
  let sub := Str.chars (← strArg "must be str, not " subV)
  let s := Str.chars (← selfText self)
  let found (i : Int) : m V := do
    if i < 0 && (sig.name == "index" || sig.name == "rindex") then
      raiseBuiltin "ValueError" "substring not found"
    return intValue (m := m) i
  match sig.name with
  | "find" | "index" => found (Str.find s sub start stop)
  | "rfind" | "rindex" => found (Str.rfind s sub start stop)
  | _ => return intValue (m := m) (Str.count s sub start stop)

/-- **`startswith` and `endswith`**: the bounds, then a `str` or a tuple of `str`s, tried in order
until one matches. -/
def tailMethod [PyWrites m V] (sig : ParseTupleSig) (self args kwargs : V) : m V := do
  let xs ← parseTupleArgs sig args kwargs
  let (start, stop) ← searchBounds xs
  let some x := xs[0]? | PyPure.modelInvariant s!"{sig.name}: no prefix"
  let s := Str.chars (← selfText self)
  let test (p : String) : Bool :=
    if sig.name == "startswith" then Str.startsWith s (Str.chars p) start stop
    else Str.endsWith s (Str.chars p) start stop
  let tuple? ← match ← PyPure.immView x with
    | some (.tuple ps) => pure (some ps)
    | some _ => pure none
    | none => PyReads.tupleView x
  if let some ps := tuple? then
    for p in ps do
      let some t ← strText? p |
        raiseBuiltin "TypeError"
          s!"tuple for {sig.name} must only contain str, not {← typeName p}"
      if test t then return PyPure.imm (m := m) (.bool true)
    return PyPure.imm (m := m) (.bool false)
  let some t ← strText? x |
    raiseBuiltin "TypeError"
      s!"{sig.name} first arg must be str or a tuple of str, not {← typeName x}"
  return PyPure.imm (m := m) (.bool (test t))

/-- The length of `Str.replace s old new count`, from the number of the replaced occurrences,
without building it. -/
def replaceSize (s old new : Str.Chars) (count : Int) : Nat :=
  let limit : Nat := if count < 0 then s.size + 1 else count.toNat
  if h : old.isEmpty then s.size + min limit (s.size + 1) * new.size
  else
    let k := (Str.occurrences s old (Str.size_pos_of_not_isEmpty h) 0 s.size limit).size
    s.size + k * new.size - k * old.size

/-- **`replace(old, new, count=-1)`**: a result above the model's limit on a repetition stops
with a gap. -/
def replaceMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .str self Signatures.str_replace args kwargs
  let old ← clinicStrArg "replace() argument 1 must be str, not " (← req "replace" ps 0)
  let new ← clinicStrArg "replace() argument 2 must be str, not " (← req "replace" ps 1)
  let count ← match arg (m := m) ps 2 with | some v => ssizeArg v | none => pure (-1)
  let (s, o, n) := (Str.chars (← selfText self), Str.chars old, Str.chars new)
  if replaceSize s o n count > maxRepeat then
    PyPure.gap "a replace result too large to model, where CPython may raise MemoryError"
  return charsValue (m := m) (Str.replace s o n count)

/-! ## Splitting -/

/-- The width in bytes of CPython's storage of the code points `cs` (PEP 393): 1 if all are below
256, 2 if all are below 65,536, and 4 otherwise. -/
def storageKind (cs : Array Char) : Nat :=
  cs.foldl (fun k c => max k (if c.val < 256 then 1 else if c.val < 65536 then 2 else 4)) 1

/-- **`split(sep=None, maxsplit=-1)`** (`rev` for `rsplit`): `maxsplit` converted first. A
separator that is longer than the string, or stored wider, gives a list of `self` itself, a
subclass instance too. -/
def splitMethod [PyWrites m V] (rev : Bool) (self args kwargs : V) : m V := do
  let sig := if rev then Signatures.str_rsplit else Signatures.str_split
  let ps ← bound .str self sig args kwargs
  let maxsplit ← match arg (m := m) ps 1 with | some v => ssizeArg v | none => pure (-1)
  let s := Str.chars (← selfText self)
  match arg (m := m) ps 0 with
  | none => strList (if rev then Str.rsplitWhitespace s maxsplit else Str.splitWhitespace s maxsplit)
  | some sepV =>
    if (← PyPure.immView sepV) matches some .none then
      return ← strList
        (if rev then Str.rsplitWhitespace s maxsplit else Str.splitWhitespace s maxsplit)
    let sep := Str.chars (← strArg "must be str or None, not " sepV)
    if sep.size > s.size || storageKind sep > storageKind s then
      return ← PyPure.allocList #[self]
    if h : sep.isEmpty then raiseBuiltin "ValueError" "empty separator"
    else
      let hp := Str.size_pos_of_not_isEmpty h
      strList (if rev then Str.rsplit s sep hp maxsplit else Str.split s sep hp maxsplit)

/-- **`splitlines(keepends=False)`**: `keepends` by its truth. -/
def splitlinesMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .str self Signatures.str_splitlines args kwargs
  let keep ← match arg (m := m) ps 0 with | some v => truthy v | none => pure false
  strList (Str.splitlines (Str.chars (← selfText self)) keep)

/-- **`partition(sep)`** (`rev` for `rpartition`): with a match, the separator argument itself
is the middle part; without one, `self` itself is the part that holds the whole string, a
subclass instance too in both cases. -/
def partitionMethod [PyWrites m V] (rev : Bool) (self args kwargs : V) : m V := do
  let sig := if rev then Signatures.str_rpartition else Signatures.str_partition
  let ps ← bound .str self sig args kwargs
  let sepV ← req sig.name ps 0
  let sep := Str.chars (← strArg "must be str, not " sepV)
  if h : sep.isEmpty then raiseBuiltin "ValueError" "empty separator"
  else
  let s := Str.chars (← selfText self)
  let (a, b, c) := if rev then Str.rpartition s sep
    else Str.partition s sep (Str.size_pos_of_not_isEmpty h)
  let part (cs : Array Char) (whole : Bool) : V :=
    if whole && b.isEmpty then self else charsValue (m := m) cs
  let mid := if b.isEmpty then charsValue (m := m) b else sepV
  return PyPure.imm (m := m) (.tuple #[part a !rev, mid, part c rev])

/-! ## Stripping, prefixes and padding -/

/-- **`strip(chars=None)`**, `lstrip` and `rstrip`. -/
def stripMethod [PyWrites m V] (sig : BuiltinSig) (left right : Bool) (self args kwargs : V) :
    m V := do
  let ps ← bound .str self sig args kwargs
  let cs ← match arg (m := m) ps 0 with
    | none => pure none
    | some v =>
      if (← PyPure.immView v) matches some .none then pure none
      else match ← strText? v with
        | some t => pure (some (Str.chars t))
        | none => raiseBuiltin "TypeError" s!"{sig.name} arg must be None or str"
  return charsValue (m := m) (Str.strip (Str.chars (← selfText self)) cs left right)

/-- **`removeprefix(prefix)`** (`suffix` for `removesuffix`). -/
def removeMethod [PyWrites m V] (suffix : Bool) (self args kwargs : V) : m V := do
  let sig := if suffix then Signatures.str_removesuffix else Signatures.str_removeprefix
  let ps ← bound .str self sig args kwargs
  let p := Str.chars (← clinicStrArg s!"{sig.name}() argument must be str, not " (← req sig.name ps 0))
  let s := Str.chars (← selfText self)
  return charsValue (m := m) (if suffix then Str.removeSuffix s p else Str.removePrefix s p)

/-- The fill character of `ljust`, `rjust` and `center` (Argument Clinic's `Py_UCS4`). -/
def fillChar [PyReads m V] (v : Option V) : m Char := do
  let some v := v | return ' '
  let some t ← strText? v |
    raiseBuiltin "TypeError" s!"The fill character must be a unicode character, not {← typeName v}"
  let [c] := t.toList |
    raiseBuiltin "TypeError" "The fill character must be exactly one character long"
  return c

/-- A result of `width` characters stops with a gap above the model's limit on a repetition,
where CPython may raise `MemoryError` or `OverflowError`. -/
def padLimit [PyReads m V] (width : Int) : m Unit := do
  if width > (maxRepeat : Int) then
    PyPure.gap "a padding too large to model, where CPython may raise MemoryError"

/-- **`ljust(width, fillchar=' ')`**, `rjust` and `center`: the width first. -/
def padMethod [PyWrites m V] (sig : BuiltinSig) (f : Str.Chars → Int → Char → Str.Chars)
    (self args kwargs : V) : m V := do
  let ps ← bound .str self sig args kwargs
  let width ← ssizeArg (← req sig.name ps 0)
  let c ← fillChar (arg (m := m) ps 1)
  padLimit width
  return charsValue (m := m) (f (Str.chars (← selfText self)) width c)

/-- **`zfill(width)`**. -/
def zfillMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .str self Signatures.str_zfill args kwargs
  let width ← ssizeArg (← req "zfill" ps 0)
  padLimit width
  return charsValue (m := m) (Str.zfill (Str.chars (← selfText self)) width)

/-- **`expandtabs(tabsize=8)`**: a C `int`. -/
def expandtabsMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .str self Signatures.str_expandtabs args kwargs
  let n ← match arg (m := m) ps 0 with | some v => cIntArg v | none => pure 8
  let s := Str.chars (← selfText self)
  -- Each tab adds at most `n` characters.
  padLimit (s.size + (s.filter (· == '\t')).size * n.toNat)
  return charsValue (m := m) (Str.expandtabs s n)

/-! ## `join` -/

/-- The text of `sep.join(items)` (`_PyUnicode_JoinArray`): each item must be a `str`; one exact
`str` is the result itself. -/
def joinItems [PyWrites m V] (sep : String) (items : Array V) : m V := do
  if let #[x] := items then
    if (← PyPure.immView x) matches some (.str _) then return x
  let mut parts : Array String := #[]
  for h : i in [0:items.size] do
    pauseStep
    let x := items[i]
    let some t ← strText? x |
      raiseBuiltin "TypeError" s!"sequence item {i}: expected str instance, {← typeName x} found"
    parts := parts.push t
  return strValue (m := m) (sep.intercalate parts.toList)

/-- The first step of `sep.join(iterable)`: the result for an exact list or tuple, whose items it
reads at once; otherwise the list that gathers the items of the iterator and that iterator, as
`PySequence_List(iter(iterable))` starts. -/
def joinFirst [PyWrites m V] (self args kwargs : V) : m (Sum V (V × V)) := do
  let ps ← bound .str self Signatures.str_join args kwargs
  let x ← req "join" ps 0
  let sep ← selfText self
  if (← classIs x .list) || (← classIs x .tuple) then
    let items ← match ← listOf? x with
      | some ys => pure ys
      | none => tupleItems x
    return .inl (← joinItems sep items)
  let it ← tryCatch (getIter x) fun e => do
    if ← isTypeErrorExc e then raiseBuiltin "TypeError" "can only join an iterable"
    throw e
  let acc ← PyPure.allocList #[]
  match ← listInitFirst acc it with
  | none => return .inl (← joinItems sep ((← listOf? acc).getD #[]))
  | some it2 => return .inr (acc, it2)

/-- One activation of `join`'s walk: the items go into `acc`, and the result once the iterator
ends. -/
def joinStep [PyWrites m V] (sep acc it : V) : m (LoopStep V V) := do
  match ← listStep acc it with
  | .more it => return .more it
  | .done _ =>
    let some items ← listOf? acc | PyPure.modelInvariant "join's list stopped being a list"
    return .done (← joinItems (← selfText sep) items)

/-- **`sep.join(iterable)` inside another operation's step**: one walk, which must end. -/
def joinBody [PyWrites m V] (self args kwargs : V) : m V := do
  match ← joinFirst self args kwargs with
  | .inl v => return v
  | .inr (acc, it) =>
    match ← joinStep self acc it with
    | .done v => return v
    | .more _ => midStepGap

/-! ## `encode` -/

/-- **`encode(encoding='utf-8', errors='strict')`**: the codecs of `Codecs`, and their errors. -/
def encodeMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .str self Signatures.str_encode args kwargs
  let enc ← codecName "encode" "encoding" (arg (m := m) ps 0)
  let err ← codecName "encode" "errors" (arg (m := m) ps 1)
  match Codecs.encodeWith enc err (← selfText self) with
  | .ok o => return bytesValue (m := m) o
  | .error e => raiseCodecError e self

/-- This file's bodies of the methods of `str`. -/
def strMethodsMethod : Builtin → String → Option BuiltinImpl
  | .str, n => match n with
    | "upper" => some fun {_} {_} [_] [_] => textMethod Signatures.str_upper Unicode.upper
    | "lower" => some fun {_} {_} [_] [_] => textMethod Signatures.str_lower Unicode.lower
    | "casefold" => some fun {_} {_} [_] [_] => textMethod Signatures.str_casefold Unicode.casefold
    | "swapcase" => some fun {_} {_} [_] [_] => textMethod Signatures.str_swapcase Unicode.swapcase
    | "capitalize" =>
      some fun {_} {_} [_] [_] => textMethod Signatures.str_capitalize Unicode.capitalize
    | "title" => some fun {_} {_} [_] [_] => textMethod Signatures.str_title Unicode.title
    | "isalpha" =>
      some fun {_} {_} [_] [_] => testMethod Signatures.str_isalpha (Unicode.allNonEmpty Unicode.isAlpha)
    | "isdecimal" =>
      some fun {_} {_} [_] [_] =>
        testMethod Signatures.str_isdecimal (Unicode.allNonEmpty Unicode.isDecimal)
    | "isdigit" =>
      some fun {_} {_} [_] [_] => testMethod Signatures.str_isdigit (Unicode.allNonEmpty Unicode.isDigit)
    | "isnumeric" =>
      some fun {_} {_} [_] [_] =>
        testMethod Signatures.str_isnumeric (Unicode.allNonEmpty Unicode.isNumeric)
    | "isalnum" =>
      some fun {_} {_} [_] [_] => testMethod Signatures.str_isalnum (Unicode.allNonEmpty Unicode.isAlnum)
    | "isspace" =>
      some fun {_} {_} [_] [_] => testMethod Signatures.str_isspace (Unicode.allNonEmpty Unicode.isSpace)
    | "isupper" => some fun {_} {_} [_] [_] => testMethod Signatures.str_isupper Unicode.isUpperStr
    | "islower" => some fun {_} {_} [_] [_] => testMethod Signatures.str_islower Unicode.isLowerStr
    | "istitle" => some fun {_} {_} [_] [_] => testMethod Signatures.str_istitle Unicode.isTitleStr
    | "isidentifier" =>
      some fun {_} {_} [_] [_] => testMethod Signatures.str_isidentifier Unicode.isIdentifierStr
    | "isprintable" =>
      some fun {_} {_} [_] [_] => testMethod Signatures.str_isprintable Unicode.isPrintableStr
    | "isascii" => some fun {_} {_} [_] [_] => testMethod Signatures.str_isascii Unicode.isAsciiStr
    | "find" => some fun {_} {_} [_] [_] => searchMethod Signatures.str_find
    | "rfind" => some fun {_} {_} [_] [_] => searchMethod Signatures.str_rfind
    | "index" => some fun {_} {_} [_] [_] => searchMethod Signatures.str_index
    | "rindex" => some fun {_} {_} [_] [_] => searchMethod Signatures.str_rindex
    | "count" => some fun {_} {_} [_] [_] => searchMethod Signatures.str_count
    | "startswith" => some fun {_} {_} [_] [_] => tailMethod Signatures.str_startswith
    | "endswith" => some fun {_} {_} [_] [_] => tailMethod Signatures.str_endswith
    | "replace" => some fun {_} {_} [_] [_] => replaceMethod
    | "split" => some fun {_} {_} [_] [_] => splitMethod false
    | "rsplit" => some fun {_} {_} [_] [_] => splitMethod true
    | "splitlines" => some fun {_} {_} [_] [_] => splitlinesMethod
    | "partition" => some fun {_} {_} [_] [_] => partitionMethod false
    | "rpartition" => some fun {_} {_} [_] [_] => partitionMethod true
    | "strip" => some fun {_} {_} [_] [_] => stripMethod Signatures.str_strip true true
    | "lstrip" => some fun {_} {_} [_] [_] => stripMethod Signatures.str_lstrip true false
    | "rstrip" => some fun {_} {_} [_] [_] => stripMethod Signatures.str_rstrip false true
    | "removeprefix" => some fun {_} {_} [_] [_] => removeMethod false
    | "removesuffix" => some fun {_} {_} [_] [_] => removeMethod true
    | "ljust" => some fun {_} {_} [_] [_] => padMethod Signatures.str_ljust Str.ljust
    | "rjust" => some fun {_} {_} [_] [_] => padMethod Signatures.str_rjust Str.rjust
    | "center" => some fun {_} {_} [_] [_] => padMethod Signatures.str_center Str.center
    | "zfill" => some fun {_} {_} [_] [_] => zfillMethod
    | "expandtabs" => some fun {_} {_} [_] [_] => expandtabsMethod
    | "join" => some fun {_} {_} [_] [_] => joinBody
    | "encode" => some fun {_} {_} [_] [_] => encodeMethod
    | _ => none
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
