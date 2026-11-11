/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.StrMethods
public import StrataPython.Dyn.Sem.Library.FormatString

set_option autoImplicit false

/-!
# `str.format` and `str.format_map`

Generic over the record, CPython 3.12's `build_string` (`Objects/stringlib/unicode_format.h`)
over the pieces that `FormatString` reads: for each replacement field, in order, the lookups of
its name (an argument by position or by name, then each `.attr` and `[key]`), its conversion
(`!r`, `!s`, `!a`), its spec, itself formatted first when it holds fields, and the call of
`format(value, spec)`. A nested spec counts one level of recursion; CPython allows two, so a
field inside a field inside a spec raises `ValueError: Max string recursion exceeded`. Every
lookup and call may run user code, and an error stops the formatting where CPython stops it.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins FormatString

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- Where the fields' names are looked up: the positional arguments (none for `format_map`) and
the mapping of the names (the keywords of `format`, or the argument of `format_map`). -/
structure FormatArgs (V : Type) where
  args : Option (Array V)
  names : V

/-- The value of the replacement field whose name is `name` (`get_field_object`), with the
numbering state after it. -/
def fieldValue [PyCalls m V] (fa : FormatArgs V) (name : String) (st : AutoState) :
    m (V × AutoState) := do
  let (first, idx?, accessors) := splitName name
  let idx ← match idx? with
    | .ok i => pure i
    | .error e => raiseBuiltin "ValueError" e
  let (index, st) ← match autoNumber st first idx with
    | .ok r => pure r
    | .error e => raiseBuiltin "ValueError" e
  let mut obj ← match index with
    | none => getItem fa.names (strValue (m := m) first)
    | some i =>
      match fa.args with
      | none => raiseBuiltin "ValueError" "Format string contains positional fields"
      | some xs =>
        match xs[i]? with
        | some v => pure v
        | none =>
          raiseBuiltin "IndexError" s!"Replacement index {i} out of range for positional args tuple"
  for a in accessors do
    match a with
    | .error e => raiseBuiltin "ValueError" e
    | .ok (.attr n) => obj ← getAttr obj n
    | .ok (.index i) => obj ← getItem obj (intValue (m := m) i)
    | .ok (.key k) => obj ← getItem obj (strValue (m := m) k)
  return (obj, st)

/-- `do_conversion`: `repr`, `str` or `ascii` of `v`. -/
def convertField [PyCalls m V] (v : V) : Option Char → m V
  | none => pure v
  | some 'r' => reprOf v
  | some 's' => strOf v
  | some 'a' => asciiOf v
  | some c => raiseBuiltin "ValueError" (conversionError c)

/-- What CPython's writer gives back when a format string's last piece was its only non-empty
write: that piece's object itself, not a copy. -/
inductive LastWrite (V : Type) where
  /-- Another result: a new `str` of the text. -/
  | none
  /-- The whole format string, which has no field. -/
  | template
  /-- The value that the last field's formatting gave. -/
  | value (v : V)

/-- **`build_string(s)`** with `depth` levels of recursion left: the formatted text, the
numbering state after it, and the object that the result is when the last piece was the only
non-empty write. -/
def buildString [PyCalls m V] (fa : FormatArgs V) :
    Nat → String → AutoState → m (String × AutoState × LastWrite V)
  | 0, _, _ => raiseBuiltin "ValueError" "Max string recursion exceeded"
  | depth + 1, s, st => do
    let mut out := ""
    let mut st := st
    let mut last : LastWrite V := .none
    for p in pieces s do
      match p with
      | .literal t =>
        last := if out.isEmpty && t == s && !t.isEmpty then .template else .none
        out := out ++ t
      | .error e => raiseBuiltin "ValueError" e
      | .field f =>
        let (v, st') ← fieldValue fa f.name st
        st := st'
        let v ← convertField v f.conversion
        let spec ← if f.specNeedsExpanding then
            let (sp, st', _) ← buildString fa depth f.spec st
            st := st'
            pure sp
          else pure f.spec
        let r ← formatOf v (strValue (m := m) spec)
        let some t ← strText? r |
          PyPure.modelInvariant "format() gave a value that is not a str"
        last := if out.isEmpty && !t.isEmpty then .value r else .none
        out := out ++ t
    return (out, st, last)

/-- The result of `self.format(…)` or `self.format_map(…)` for the template `self`. -/
def formatResult [PyReads m V] (self : V) (s : String) : LastWrite V → V
  | .none => strValue (m := m) s
  | .template => self
  | .value r => r

/-- **`self.format(*args, **kwargs)`**. -/
def formatMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let fa : FormatArgs V := { args := some (← tupleItems args), names := kwargs }
  let (s, _, last) ← buildString fa 2 (← selfText self) .init
  return formatResult (m := m) self s last

/-- **`self.format_map(mapping)`**: the names looked up in `mapping`; a field by position is a
`ValueError`. -/
def formatMapMethod [PyWrites m V] (self args kwargs : V) : m V := do
  let ps ← bound .str self Signatures.str_format_map args kwargs
  let fa : FormatArgs V := { args := none, names := ← req "format_map" ps 0 }
  let (s, _, last) ← buildString fa 2 (← selfText self) .init
  return formatResult (m := m) self s last

/-- This file's bodies of the methods of `str`. -/
def strFormatMethod : Builtin → String → Option BuiltinImpl
  | .str, "format" => some fun {_} {_} [_] [_] => formatMethod
  | .str, "format_map" => some fun {_} {_} [_] [_] => formatMapMethod
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
