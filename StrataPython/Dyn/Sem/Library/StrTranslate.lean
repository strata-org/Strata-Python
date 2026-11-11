/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.StrMethods

set_option autoImplicit false

/-!
# `str.translate` and `str.maketrans`

Generic over the record, CPython 3.12's `_PyUnicode_TranslateCharmap` with the error handler
`ignore`, as `str.translate` calls it, and `unicode_maketrans_impl` (`Objects/unicodeobject.c`).
The table is any object with `__getitem__`, which may run user code, so the number of lookups is
CPython's:
* An ASCII string first takes `unicode_fast_translate`, which keeps a 128-entry cache, so each
  distinct character is looked up once. A lookup whose result isn't deletion or one ASCII
  character ends the fast path, and the rest of the string takes the slow path, which looks that
  character up again.
* The slow path looks every character up. After a character that maps to `None`, it looks the
  next characters up once more while they map to `None` too, as CPython collects the
  untranslatable run, and then goes on from the first one that doesn't, which it looks up again.

A `LookupError` keeps the character. A lone surrogate has no Lean `Char`, so a mapping to one
stops with a gap.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

/-- What the table gives for a character (`charmaptranslate_lookup`). -/
inductive Mapped where
  /-- No entry (a `LookupError`): the character stays. -/
  | keep
  /-- `None`: the character goes. -/
  | delete
  /-- An `int`: the character with that code point. -/
  | code (c : Char)
  /-- A `str`. -/
  | text (s : String)

section
variable {m : Type → Type 1} {V : Type}

/-- Whether the exception `x` is a `LookupError`. -/
def isLookupError [PyReads m V] (x : V) : m Bool := do
  let some mro ← mroOf (← PyReads.classOf x) | return false
  inMro (PyPure.imm (m := m) (.builtin .LookupError)) mro

/-- **`charmaptranslate_lookup(c, table)`**: `table[c]`, checked. -/
def lookupMapped [PyCalls m V] (table : V) (c : Char) : m Mapped := do
  let r? ← tryCatch (some <$> getItem table (intValue (m := m) c.toNat)) fun e => do
    if ← isLookupError e then pure none else throw e
  let some r := r? | return .keep
  if (← PyPure.immView r) matches some .none then return .delete
  if let some n ← intPart? r then
    -- CPython reads the int with `PyLong_AS_LONG`, unchecked, so a huge one is out of range too.
    if n < 0 || n > 0x10FFFF then
      raiseBuiltin "ValueError" "character mapping must be in range(0x110000)"
    if 0xD800 ≤ n && n ≤ 0xDFFF then PyPure.gap "a lone surrogate is not modelled"
    return .code (Char.ofNat n.toNat)
  if let some s ← strText? r then return .text s
  raiseBuiltin "TypeError" "character mapping must return integer, None or str"

/-- The fast path's entry for the character `c`, from a lookup: `some out` with the character's
output (none for a deletion), or `none` when the result ends the fast path. -/
def fastEntry [PyCalls m V] (table : V) (c : Char) : m (Option (Option Char)) := do
  match ← lookupMapped table c with
  | .keep => pure (some (some c))
  | .delete => pure (some none)
  | .code d => pure (if d.toNat < 128 then some (some d) else none)
  | .text t =>
    match t.toList with
    | [d] => pure (if d.toNat < 128 then some (some d) else none)
    | _ => pure none

/-- **`self.translate(table)`**. -/
def translateMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .str self Signatures.str_translate args kwargs
  let table ← req "translate" ps 0
  let s := Str.chars (← selfText self)
  let mut out : String := ""
  let mut i := 0
  -- `unicode_fast_translate`, for an ASCII string.
  if s.all (·.toNat < 128) then
    let mut cache : Array (Option (Option Char)) := Array.replicate 128 none
    let mut ended := false
    for c in s do
      pauseStep
      let e ← match cache[c.toNat]? with
        | some (some e) => pure (some e)
        | _ => fastEntry table c
      match e with
      | some o =>
        cache := cache.set! c.toNat (some o)
        if let some d := o then out := out.push d
        i := i + 1
      | none =>
        ended := true
        break
    if !ended then return strValue (m := m) out
  -- The slow path, from position `i`. After a character that maps to `None`, CPython looks the
  -- next characters up while they map to `None` too (`inRun`), and then looks the first one that
  -- doesn't up again. So each character is looked up at most twice.
  let mut j := i
  let mut inRun := false
  for _ in [0:2 * s.size + 1] do
    if j ≥ s.size then break
    pauseStep
    let c := s.getD j ' '
    let r ← lookupMapped table c
    if inRun then
      if r matches .delete then j := j + 1 else inRun := false
    else
      match r with
      | .keep => out := out.push c; j := j + 1
      | .code d => out := out.push d; j := j + 1
      | .text t => out := out ++ t; j := j + 1
      | .delete => inRun := true; j := j + 1
  return strValue (m := m) out

/-- **`str.maketrans(x, y=…, z=…)`**: with `y`, the code points of `x` mapped to those of `y`,
and those of `z` to `None`; with `x` alone, an exact dict whose `str` keys of one character
become their code points. -/
def maketransFn [PyWrites m V] (_self args kwargs : V) : m V := do
  -- A static method: its messages name no class.
  let ps := (← bindBuiltinArgs Signatures.str_maketrans args kwargs).params
  let x ← req "maketrans" ps 0
  let y? ← match arg (m := m) ps 1 with
    | some v => some <$> clinicStrArg "maketrans() argument 2 must be str, not " v
    | none => pure none
  let z? ← match arg (m := m) ps 2 with
    | some v => some <$> clinicStrArg "maketrans() argument 3 must be str, not " v
    | none => pure none
  let new ← PyPure.allocDict
  match y? with
  | some y =>
    let some xs ← strText? x |
      raiseBuiltin "TypeError"
        "first maketrans argument must be a string if there is a second argument"
    if xs.length != y.length then
      raiseBuiltin "ValueError" "the first two maketrans arguments must have equal length"
    for (a, b) in xs.toList.zip y.toList do
      dictPut new (intValue (m := m) a.toNat) (intValue (m := m) b.toNat)
    if let some z := z? then
      for c in z.toList do dictPut new (intValue (m := m) c.toNat) (PyPure.imm (m := m) .none)
  | none =>
    unless ← classIs x .dict do
      raiseBuiltin "TypeError" "if you give only one argument to maketrans it must be a dict"
    for (k, v, _) in ← PyReads.dictEntries x do
      if let some t ← strText? k then
        let [c] := t.toList |
          raiseBuiltin "ValueError" "string keys in translate table must be of length 1"
        dictPut new (intValue (m := m) c.toNat) v
      else if (← intPart? k).isSome then
        if ← isUserObject k then
          PyPure.gap "a key of maketrans that is an instance of a subclass of int is not modelled yet"
        dictPut new k v
      else
        raiseBuiltin "TypeError" "keys in translate table must be strings or integers"
  return new

/-- This file's bodies of the methods of `str`. -/
def strTranslateMethod : Builtin → String → Option BuiltinImpl
  | .str, "translate" => some fun {_} {_} [_] [_] => translateMethod
  | .str, "maketrans" => some fun {_} {_} [_] [_] => maketransFn
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
