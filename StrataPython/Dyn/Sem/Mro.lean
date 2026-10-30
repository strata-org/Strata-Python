/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# C3 linearization

CPython 3.12's `mro_implementation` and `pmerge` (`Objects/typeobject.c`), over any type of class
keys whose equality is identity: the MRO of a class from its bases and their stored MROs, or why
there is none.

The caller does the rest of CPython's class creation:
* a metaclass `mro()` override, which replaces C3 (and whose result CPython checks);
* `Cannot extend an incomplete type`, for a base that has no MRO yet (`mroOf` is total here);
* the stored MRO of each base: a `__mro__` attribute changes what the user sees, not C3's input;
* the bases of a class statement, never empty (`type.__new__` puts `(object,)` there);
* the classes' names, which CPython reads through the metaclass.  `Error.message` takes them, with
  `none` for a name that is not a `str`;
* the comparison of the error heads.  CPython keeps them in a dict, so a metaclass with its own
  `__eq__` or `__hash__` can change the message; the caller then reports that the semantics
  doesn't cover the case.
-/

namespace StrataPython.Dyn.Sem.C3

variable {α : Type} [DecidableEq α]

@[expose] public section

/-- `l` without its head, if its head is `c`. -/
def dropHead (c : α) : List α → List α
  | x :: xs => if x = c then xs else x :: xs
  | [] => []

/-- The heads of the non-empty lists, in order, each once: the classes that `set_mro_error`
names. -/
def heads (ls : List (List α)) : List α :=
  (ls.filterMap List.head?).foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The first head that is in no list's tail: `pmerge`'s next class. -/
def candidate? (ls : List (List α)) : Option α :=
  (ls.filterMap List.head?).find? fun c => ls.all fun l => !(l.drop 1).contains c

/-- The total length of the lists. -/
def total (ls : List (List α)) : Nat := ls.foldr (fun l n => l.length + n) 0

/-- `dropHead` never makes a list longer. -/
private theorem dropHead_le (c : α) (l : List α) : (dropHead c l).length ≤ l.length := by
  cases l with
  | nil => simp [dropHead]
  | cons x xs => by_cases h : x = c <;> simp [dropHead, h]

/-- Dropping `c` from the heads never makes the total larger. -/
private theorem total_drop_le (c : α) (ls : List (List α)) : total (ls.map (dropHead c)) ≤ total ls := by
  induction ls with
  | nil => simp [total]
  | cons l ls ih =>
    simp only [total, List.map_cons, List.foldr_cons] at *
    have hl := dropHead_le c l
    omega

/-- Dropping `c` from the heads makes the total smaller when `c` heads some list. -/
private theorem total_drop_lt (c : α) : ∀ (ls : List (List α)),
    (∃ l ∈ ls, l.head? = some c) → total (ls.map (dropHead c)) < total ls
  | [], ⟨_, hl, _⟩ => by simp at hl
  | l :: ls, ⟨l', hl', hh⟩ => by
    simp only [total, List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hl' with rfl | hrest
    · have hle := total_drop_le c ls
      simp only [total] at hle
      cases l' with
      | nil => simp at hh
      | cons x xs =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp [dropHead]
        omega
    · have hlt := total_drop_lt c ls ⟨l', hrest, hh⟩
      simp only [total] at hlt
      have hl := dropHead_le c l
      omega

/-- Mapping `dropHead c` over `ls.attach`, as `merge`'s recursion does, gives the same list as
mapping it over `ls`. -/
theorem attach_map_dropHead (c : α) (ls : List (List α)) :
    (ls.attach.map fun x => match x with | ⟨x, _⟩ => dropHead c x) = ls.map (dropHead c) := by
  simp

/-- C3's merge, as CPython's `pmerge`: the classes of `acc` in reverse order (`acc` holds the
classes merged so far, the newest first), then the merge of `ls`; or the heads that it couldn't
merge. -/
def merge (ls : List (List α)) (acc : List α) : Except (List α) (List α) :=
  if ls.all List.isEmpty then .ok acc.reverse
  else match h : candidate? ls with
    | none => .error (heads ls)
    | some c =>
      have hc : ∃ l ∈ ls, l.head? = some c := by
        unfold candidate? at h
        exact List.mem_filterMap.mp (List.mem_of_find?_eq_some h)
      merge (ls.map (dropHead c)) (c :: acc)
termination_by total ls
decreasing_by
  rw [attach_map_dropHead]
  exact total_drop_lt c ls hc

/-- Why a class has no MRO. -/
inductive Error (α : Type) where
  /-- `TypeError: duplicate base class X`. -/
  | duplicate (base : α)
  /-- `TypeError: Cannot create a consistent method resolution\norder (MRO) for bases …`, naming
  these classes. -/
  | inconsistent (heads : List α)
  deriving Repr, DecidableEq

/-- The first base that appears twice, as CPython's `check_duplicates` finds it. -/
def firstDuplicate : List α → Option α
  | [] => none
  | b :: bs => if bs.contains b then some b else firstDuplicate bs

/-- The MRO of the class `cls` with the bases `bases`, whose MROs `mroOf` gives: CPython's
`mro_implementation`.  One base needs no merge; two or more are first checked for duplicates. -/
def mro (cls : α) (bases : List α) (mroOf : α → List α) : Except (Error α) (List α) :=
  match bases with
  | [b] => .ok (cls :: mroOf b)
  | _ =>
    match firstDuplicate bases with
    | some b => .error (.duplicate b)
    | none => match merge (bases.map mroOf ++ [bases]) [cls] with
      | .ok r => .ok r
      | .error hs => .error (.inconsistent hs)

/-- The first `n` bytes of `s` as UTF-8, if they end at a character boundary. -/
def truncateUtf8 (s : String) (n : Nat) : Option String :=
  let bytes := s.toUTF8
  if bytes.size ≤ n then some s else String.fromUTF8? (bytes.extract 0 n)

/-- The message of the `TypeError` for `e`, with `name` the `__name__` of each class (`none` if it
is not a `str`).  CPython writes the MRO message into a 1000-byte buffer, so it keeps its first 999
bytes; `none` when that cuts a character, where CPython raises `UnicodeDecodeError` instead. -/
def Error.message (name : α → Option String) : Error α → Option String
  | .duplicate b => some (match name b with
    | some n => s!"duplicate base class {n}"
    | none => "duplicate base class")
  | .inconsistent hs =>
    truncateUtf8 ("Cannot create a consistent method resolution\norder (MRO) for bases " ++
      ", ".intercalate (hs.map fun h => (name h).getD "?")) 999

end

end StrataPython.Dyn.Sem.C3
