/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
public import StrataDDM.Util.SourceRange

set_option autoImplicit false

/-!
# Attributes

A front end states facts about a function, such as a declared shape, as *attributes*: named
values the printer writes below the function's signature and the reader reads back, so that
goldens pin them.  The IR gives them no meaning, and well-formedness does not mention them.
A key is prefixed by the front end that gives it its meaning: `py.fields`.

`Info`, a source range and attributes, is the annotation that carries them.  The printer
writes the attributes of `Func.info` through `HasAttrs`, which gives none for `Unit` and
`SourceRange`, and the reader returns a module annotated with `Info`.  `Func.setInfo` replaces a
built function's own `Info`.  Its blocks and instructions keep theirs.

What reads back: keys are unique at each level, a function pointer names a function of the
module, and a ghost constant `ghost @m.g` names a ghost of the module.  Source names belong in
string values: `{name = "module"}`.
-/

namespace Strata.Dyn

public section

/-- A value an attribute holds: a literal, a list, or a record of named values. -/
inductive AttrValue where
  | const (c : Const)
  | list (vs : Array AttrValue)
  | record (fields : Array (Name × AttrValue))
deriving Inhabited, Repr

/-- An attribute: its key and its value. -/
abbrev Attr := Name × AttrValue

/-- An annotation with attributes: where the part comes from, and the facts stated about it. -/
structure Info where
  range : StrataDDM.SourceRange := .none
  attrs : Array Attr := #[]
deriving Inhabited

/-- The attributes an annotation carries. -/
-- Not specialized: the printer's private helpers are not visible at a call site.
@[nospecialize] class HasAttrs (α : Type) where
  attrs : α → Array Attr

instance : HasAttrs Info := ⟨Info.attrs⟩
instance : HasAttrs Unit := ⟨fun _ => #[]⟩
instance : HasAttrs StrataDDM.SourceRange := ⟨fun _ => #[]⟩

end

end Strata.Dyn
