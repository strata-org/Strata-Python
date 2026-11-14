/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
public import Std.Data.HashMap

set_option autoImplicit false

/-!
# Fresh names

A generated name is a stem with a numeric suffix, `x.3`.  A pass that adds values or blocks to
a function names them this way, so that no two names of the function are alike.

* `Suffixes` gives each stem its next suffix.
* `ValueNames` is the names of the values of a function or ghost, by id, with their suffixes: a
  new value takes the next id and a name that no value has, in one step.

Each is built only from the names in use (`of`) and changed only by `fresh`, so its suffixes
are above every suffix in use.
-/

namespace Strata.Dyn

public section

/-- The stem and the suffix of a name: `x.3` is `(x, 3)`. -/
@[expose] def Name.splitNum : Name → Name × Option Nat
  | .num n i => (n, some i)
  | n => (n, none)

/-- For each stem, a suffix above every suffix of the stem in use: `0` for a stem that is not
listed. -/
structure Suffixes where
  private mk ::
  private next : Std.HashMap Name Nat

namespace Suffixes

/-- The suffixes that the names `names` leave. -/
def of (names : Array Name) : Suffixes :=
  ⟨names.foldl (init := {}) fun m nm =>
    match nm.splitNum with
    | (s, some i) => m.insert s (max (m.getD s 0) (i + 1))
    | _ => m⟩

/-- The name `stem.k` for the next suffix `k` of the stem, and the suffixes left after it. -/
def fresh : Suffixes → Name → Name × Suffixes
  | ⟨next⟩, stem =>
    let k := next.getD stem 0
    (.num stem k, ⟨next.insert stem (k + 1)⟩)

end Suffixes

/-- The names of the values of a function or ghost, with the suffixes they leave. -/
structure ValueNames where
  private mk ::
  /-- `names[i]` is the name of value `i`. -/
  names : Array Name
  private suffixes : Suffixes

namespace ValueNames

/-- The names of the values of a function or ghost, as it holds them. -/
def of (names : Array Name) : ValueNames := ⟨names, .of names⟩

/-- A new value named after `stem`: its id, the next one, and the names with its name added. -/
def fresh : ValueNames → Name → ValId × ValueNames
  | ⟨names, suffixes⟩, stem =>
    let (name, suffixes) := suffixes.fresh stem
    (⟨names.size⟩, ⟨names.push name, suffixes⟩)

end ValueNames

end

end Strata.Dyn
