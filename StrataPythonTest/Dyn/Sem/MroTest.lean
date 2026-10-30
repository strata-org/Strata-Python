/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Mro
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Mro

set_option autoImplicit false

/-!
# C3 linearization

Each expected MRO and message is what CPython 3.12.15 gives for the same class statements.
-/

namespace StrataPython.Dyn.Sem.MroTest

open StrataPython.Dyn.Sem

/-- The classes of the examples, by name. -/
abbrev K := String

/-- The MROs of the classes below. -/
def mros : K → List K
  | "object" => ["object"]
  | "A" => ["A", "object"]
  | "B" => ["B", "A", "object"]
  | "X" => ["X", "object"]
  | "Y" => ["Y", "object"]
  | "Z" => ["Z", "X", "Y", "object"]
  | "W" => ["W", "Y", "X", "object"]
  | "O" => ["O", "object"]
  | "Fa" => ["Fa", "O", "object"]
  | "Fb" => ["Fb", "O", "object"]
  | "C" => ["C", "object"]
  | "D" => ["D", "A", "object"]
  | "P1" => ["P1", "object"]
  | "P2" => ["P2", "object"]
  | "P3" => ["P3", "object"]
  | "Q1" => ["Q1", "P1", "P2", "P3", "object"]
  | "Q2" => ["Q2", "P2", "P3", "P1", "object"]
  | "Q3" => ["Q3", "P3", "P1", "P2", "object"]
  | k => [k, "object"]

/-- The result of creating class `cls` with `bases`: the MRO, or the message of the `TypeError`. -/
def result (cls : K) (bases : List K) : List K ⊕ String :=
  match C3.mro cls bases mros with
  | .ok r => .inl r
  | .error e => .inr ((e.message some).getD "<UnicodeDecodeError>")

-- A diamond: `class Fc(Fa, Fb)`.
#guard result "Fc" ["Fa", "Fb"] == .inl ["Fc", "Fa", "Fb", "O", "object"]
-- One base needs no merge: `class B(A)`.
#guard result "B" ["A"] == .inl ["B", "A", "object"]
-- `class C(A, B)` after `class B(A)`.
#guard result "C" ["A", "B"] ==
  .inr "Cannot create a consistent method resolution\norder (MRO) for bases A, B"
-- `class V(Z, W)` with `Z(X, Y)` and `W(Y, X)`.
#guard result "V" ["Z", "W"] ==
  .inr "Cannot create a consistent method resolution\norder (MRO) for bases X, Y"
-- `class D(A, A)`.
#guard result "D" ["A", "A"] == .inr "duplicate base class A"
-- The first base with a later copy is named: `class X(A, B, C, B)`.
#guard result "X" ["A", "B", "C", "B"] == .inr "duplicate base class B"
-- `class Y(object, A)`.
#guard result "Y" ["object", "A"] ==
  .inr "Cannot create a consistent method resolution\norder (MRO) for bases object, A"
-- Three heads: `class Z(Q1, Q2, Q3)` with `Q1(P1, P2, P3)`, `Q2(P2, P3, P1)`, `Q3(P3, P1, P2)`.
#guard result "Z" ["Q1", "Q2", "Q3"] ==
  .inr "Cannot create a consistent method resolution\norder (MRO) for bases P1, P2, P3"
-- A deeper diamond: `class E(B, D)` with `B(A)` and `D(A)`.
#guard result "E" ["B", "D"] == .inl ["E", "B", "D", "A", "object"]
-- No bases: object's own MRO.
#guard result "object" [] == .inl ["object"]
-- A name that is not a `str`: no name, or `?`.
#guard (C3.Error.duplicate "A").message (fun _ => none) == some "duplicate base class"
#guard (C3.Error.inconsistent ["A", "B"]).message (fun _ => none) ==
  some "Cannot create a consistent method resolution\norder (MRO) for bases ?, ?"
-- CPython keeps the first 999 bytes of a long message, and raises `UnicodeDecodeError` when the cut
-- splits a character.
/-- The start of every MRO error message. -/
def mroPrefix : String := "Cannot create a consistent method resolution\norder (MRO) for bases "
/-- `n` copies of `c`. -/
def rep (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)
#guard (C3.Error.inconsistent ((List.range 5).map fun i => rep 300 (Char.ofNat (97 + i)))).message
  some == some (mroPrefix ++ rep 300 'a' ++ ", " ++ rep 300 'b' ++ ", " ++ rep 300 'c' ++ ", " ++
    rep 26 'd')
#guard (C3.Error.inconsistent ["a" ++ rep 600 'é']).message some == none
#guard (C3.Error.inconsistent [rep 600 'é']).message some == some (mroPrefix ++ rep 466 'é')

end StrataPython.Dyn.Sem.MroTest
