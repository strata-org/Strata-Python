/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.LoopExits
public import StrataDyn.Attr
public import StrataDyn.DDM

set_option autoImplicit false

/-!
# Loop records as an attribute

A front end states its loop records (`StrataDyn/LoopExits.lean`) as an attribute of each
function, so that they are printed with the function and read back with it.  Each record is a
record value: `{head = "head.0", done = "done.0"}`, with `done` left out when the record has none.
A record with any other field does not read, so that a field that the check does not know, such
as the label of a labelled `break`, is reported rather than dropped.  A block's label is written
as the printer writes it (`ToDDM.nameText`) and read back as the reader reads it
(`ToDDM.nameOfText`), so it reads back exactly as the label that names its block does.
-/

namespace Strata.Dyn

public section

/-- A loop record as an attribute value. -/
@[expose] def LoopRecord.toAttrValue (r : LoopRecord) : AttrValue :=
  .record <| #[(.str .base "head", .const (.str (ToDDM.nameText r.head.name)))] ++
    (match r.done with
     | some d => #[(.str .base "done", .const (.str (ToDDM.nameText d.name)))]
     | none => #[])

/-- The field `k` of a record value. -/
@[expose] def attrField? (k : String) (fs : Array (Name × AttrValue)) : Option AttrValue :=
  (fs.find? (·.1 == .str .base k)).map (·.2)

/-- The label that an attribute value names: a string, read as the reader reads a label. -/
@[expose] def labelOfAttr? : AttrValue → Option Label
  | .const (.str s) => some ⟨ToDDM.nameOfText s⟩
  | _ => none

/-- The loop record that an attribute value states, if it reads as one: a record with a `head`
label, maybe a `done` label, and no other field. -/
@[expose] def LoopRecord.ofAttrValue? : AttrValue → Option LoopRecord
  | .record fs => do
    guard (fs.all fun (k, _) => k == .str .base "head" || k == .str .base "done")
    let head ← (attrField? "head" fs).bind labelOfAttr?
    let done ← match attrField? "done" fs with
      | none => pure none
      | some v => some <$> labelOfAttr? v
    pure { head, done }
  | _ => none

/-- The loop records of the attribute `key` among `attrs`.  An absent attribute gives `some []`.
An entry that does not read as a record gives `none`, so that a front end's mistake is reported,
not dropped. -/
@[expose] def LoopRecord.ofAttrs? (key : Name) (attrs : Array Attr) : Option (List LoopRecord) :=
  match attrs.find? (·.1 == key) with
  | none => some []
  | some (_, .list vs) => vs.toList.mapM LoopRecord.ofAttrValue?
  | some _ => none

/-- The attribute `key` that states `recs`, or none if there is no record. -/
@[expose] def LoopRecord.toAttrs (key : Name) (recs : List LoopRecord) : Array Attr :=
  if recs.isEmpty then #[] else #[(key, .list (recs.map LoopRecord.toAttrValue).toArray)]

end

end Strata.Dyn
