/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Set
public import StrataPython.Dyn.Sem.IndexProps

set_option autoImplicit false

/-!
# Properties of set tables

Key theorems: `SetTable.groupCount_spec` and `SetTable.kindGroupCount_spec`, which say what the
two counts of distinct hashes count.
-/

namespace StrataPython.Dyn.Sem.SetTable

/-- `groupCount k c` is the length of a list without duplicates of exactly the hashes `h` such
that some entry has the hash `h`, the hash kind `k` and the key class `c`. -/
public theorem groupCount_spec (t : SetTable) (k : HashKind) (c : KeyClass) :
    ∃ l : List Hash, l.Nodup ∧
      (∀ h, h ∈ l ↔ 0 < countBy SetSlot.groupKey t.slots ((k, c), h)) ∧
      t.groupCount k c = l.length :=
  t.groups.count_spec (k, c)

/-- `kindGroupCount k` is the length of a list without duplicates of exactly the hashes `h` such
that some entry has the hash `h` and the hash kind `k`, whatever its key class. -/
public theorem kindGroupCount_spec (t : SetTable) (k : HashKind) :
    ∃ l : List Hash, l.Nodup ∧
      (∀ h, h ∈ l ↔ 0 < countBy SetSlot.kindKey t.slots (k, h)) ∧
      t.kindGroupCount k = l.length :=
  t.kindGroups.count_spec k

end StrataPython.Dyn.Sem.SetTable
