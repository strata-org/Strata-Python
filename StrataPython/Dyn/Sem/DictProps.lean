/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Dict
public import StrataPython.Dyn.Sem.IndexProps

set_option autoImplicit false

/-!
# Properties of dict tables

Key theorems:
* `DictTable.objPositions_eq`: the object index gives the scan;
* `DictTable.groupCount_spec`: `groupCount` counts the distinct hashes of the live entries of
  one hash kind and key class, and `DictTable.kindGroupCount_spec` those of one hash kind.
-/

namespace StrataPython.Dyn.Sem.DictTable

/-- `objPositions` is the scan. -/
public theorem objPositions_eq (t : DictTable) (id : ObjId) :
    t.objPositions id = positionsBy DictEntry.objKey t.entries id := t.byObj.wf id

/-- `groupCount k c` is the length of a list without duplicates of exactly the hashes `h` such
that some live entry has the hash `h`, the hash kind `k` and the key class `c`. -/
public theorem groupCount_spec (t : DictTable) (k : HashKind) (c : KeyClass) :
    ∃ l : List Hash, l.Nodup ∧
      (∀ h, h ∈ l ↔ 0 < countBy DictEntry.groupKey t.entries ((k, c), h)) ∧
      t.groupCount k c = l.length :=
  t.groups.count_spec (k, c)

/-- `kindGroupCount k` is the length of a list without duplicates of exactly the hashes `h` such
that some live entry has the hash `h` and the hash kind `k`, whatever its key class. -/
public theorem kindGroupCount_spec (t : DictTable) (k : HashKind) :
    ∃ l : List Hash, l.Nodup ∧
      (∀ h, h ∈ l ↔ 0 < countBy DictEntry.kindKey t.entries (k, h)) ∧
      t.kindGroupCount k = l.length :=
  t.kindGroups.count_spec k

end StrataPython.Dyn.Sem.DictTable
