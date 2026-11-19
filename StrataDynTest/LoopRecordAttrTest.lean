/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.LoopRecordAttr
meta import StrataDyn.LoopRecordAttr

set_option autoImplicit false

/-!
# Loop records as an attribute

A label reads back from its text as the reader reads the label that names a block, and a loop
record's attribute value reads back as the record.
-/

namespace Strata.Dyn.LoopRecordAttrTest

open Strata.Dyn

private def lbl (s : String) (k : Nat) : Label := ⟨.num (.str .base s) k⟩

-- A label's text reads back as the label, as the reader reads the label that names a block.
#guard ToDDM.nameOfText (ToDDM.nameText (lbl "head" 0).name) == (lbl "head" 0).name
#guard ToDDM.nameOfText (ToDDM.nameText (lbl "done" 12).name) == (lbl "done" 12).name
#guard ToDDM.nameOfText "a.b.3" == .num (.str (.str .base "a") "b") 3
#guard ToDDM.nameOfText (ToDDM.nameText (Name.num (.str .base "a") 7)) == .num (.str .base "a") 7
-- A segment that is not all digits stays a string, so "1_0" reads back as itself.
#guard ToDDM.nameOfText (ToDDM.nameText (Name.str (.str .base "a") "1_0")) ==
  Name.str (.str .base "a") "1_0"
#guard labelOfAttr? (.const (.str "0.head")) == some ⟨.str (.num .base 0) "head"⟩

private def recs : List LoopRecord :=
  [{ head := lbl "head" 0, done := some (lbl "done" 0) },
   { head := lbl "head" 1, done := none, label := some 3 }]

-- Each record reads back as itself, and so does the attribute that states them.
#guard recs.all fun r => LoopRecord.ofAttrValue? r.toAttrValue == some r
#guard LoopRecord.ofAttrs? (.str .base "loops") (LoopRecord.toAttrs (.str .base "loops") recs) ==
  some recs
-- No record: no attribute, which reads as no record.
#guard (LoopRecord.toAttrs (.str .base "loops") []).isEmpty
#guard LoopRecord.ofAttrs? (.str .base "loops") #[] == some []
-- An entry that is not a record: the attribute does not read.
#guard LoopRecord.ofAttrs? (.str .base "loops")
  #[(.str .base "loops", .list #[.const (.int 1)])] == none
-- A label field that is not an integer.
#guard LoopRecord.ofAttrValue? (.record #[(.str .base "head", .const (.str "head.0")),
  (.str .base "label", .const (.str "x"))]) == none

end Strata.Dyn.LoopRecordAttrTest
