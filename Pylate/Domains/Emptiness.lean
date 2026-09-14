/-
Four-state collection emptiness domain and its reduction with the
collection element summary.

`bottom` denotes no concrete collection, while `empty` denotes a reachable
collection with no elements.  In particular, allocation starts at `empty`,
not `bottom`.
-/
import Pylate.Domains.Value

namespace Pylate

inductive Emptiness
  | bottom
  | empty
  | nonempty
  | top
deriving DecidableEq, Repr, Inhabited

namespace Emptiness

def all : List Emptiness :=
  [.bottom, .empty, .nonempty, .top]

def join : Emptiness -> Emptiness -> Emptiness
  | .bottom, other | other, .bottom => other
  | .empty, .empty => .empty
  | .nonempty, .nonempty => .nonempty
  | .top, _ | _, .top => .top
  | .empty, .nonempty | .nonempty, .empty => .top

def le : Emptiness -> Emptiness -> Bool
  | .bottom, _ => true
  | _, .top => true
  | .empty, .empty | .nonempty, .nonempty => true
  | _, _ => false

end Emptiness

/-- Collection size: a refinement of `Emptiness` that can say *how many*.

    `Emptiness` separates empty from non-empty and stops there, so `xs[0]` on a
    two-element list still owed a `bounds` obligation. This adds the count, which
    is what `tupleSlotCount` already gives tuples exactly -- and tuple subscripts
    are exact today while list subscripts are not.

    Chains are `bottom < exact n < positive < top`: **height four**, so no
    widening. The flat `exact n` layer is what makes that work, and it is worth
    seeing why a loop terminates. `xs = []` then `xs.append(i)` in a loop gives
    `exact 0` on entry and `exact 1` after the body; the join of two *different*
    exact sizes is not a wider count but `positive` or `top`, so the second
    iteration is already at the fixpoint. An interval domain is what would climb
    `[0,1]`, `[0,2]`, ... forever; a flat layer cannot. -/
inductive Size
  | bottom
  /-- Exactly this many elements. -/
  | exact (n : Nat)
  /-- At least one element; the count is unknown. -/
  | positive
  | top
deriving DecidableEq, Repr, Inhabited

namespace Size

def join : Size -> Size -> Size
  | .bottom, other | other, .bottom => other
  | .top, _ | _, .top => .top
  | .exact n, .exact m =>
    if n == m then .exact n
    else if n > 0 && m > 0 then .positive else .top
  | .exact n, .positive | .positive, .exact n =>
    if n > 0 then .positive else .top
  | .positive, .positive => .positive

def le : Size -> Size -> Bool
  | .bottom, _ => true
  | _, .top => true
  | .exact n, .exact m => n == m
  | .exact n, .positive => n > 0
  | .positive, .positive => true
  | _, _ => false

def render : Size -> String
  | .bottom => "unreachable"
  | .exact n => toString n
  | .positive => "positive"
  | .top => "unknown"

/-- The emptiness this size implies. Every existing reader goes through here, so
    the coarser domain stays available unchanged. -/
def emptiness : Size -> Emptiness
  | .bottom => .bottom
  | .exact 0 => .empty
  | .exact _ => .nonempty
  | .positive => .nonempty
  | .top => .top

/-- The coarsest size with a given emptiness. `emptinessSet` goes through here,
    so setting an emptiness forgets a count rather than contradicting one. -/
def ofEmptiness : Emptiness -> Size
  | .bottom => .bottom
  | .empty => .exact 0
  | .nonempty => .positive
  | .top => .top

/-- `emptiness` is a lattice homomorphism: refining the domain cannot change what
    any existing reader concludes, because joining sizes and then projecting is
    the same as projecting and then joining emptiness.

    This is what makes replacing the stored domain behaviour-preserving rather
    than merely intended to be. -/
theorem emptiness_join (a b : Size) :
    (a.join b).emptiness = a.emptiness.join b.emptiness := by
  cases a with
  | bottom => cases b with
    | exact m => cases m <;> rfl
    | _ => rfl
  | top => cases b with
    | exact m => cases m <;> rfl
    | _ => rfl
  | positive => cases b with
    | exact m => cases m <;> simp [join, emptiness, Emptiness.join]
    | _ => rfl
  | exact n => cases b with
    | bottom => cases n <;> rfl
    | top => cases n <;> rfl
    | positive => cases n <;> simp [join, emptiness, Emptiness.join]
    | exact m =>
      -- The only case with real content: two known counts.
      cases n with
      | zero => cases m <;> simp [join, emptiness, Emptiness.join]
      | succ k =>
        cases m with
        | zero => simp [join, emptiness, Emptiness.join]
        | succ j =>
          by_cases h : k = j
          · subst h; simp [join, emptiness, Emptiness.join]
          · simp [join, emptiness, Emptiness.join, h]

end Size

namespace Emptiness

structure Reduced where
  emptiness : Emptiness
  elements  : AbsVal
deriving Repr, Inhabited

/--
Reduce the product of collection emptiness and its complete may-element
summary.

An empty collection has no elements.  A nonempty collection with a bottom
element summary is inconsistent and therefore reduces to bottom.  A bottom
element summary refines `top` to `empty`; a non-bottom summary alone cannot
establish non-emptiness.
-/
def reduce (emptiness : Emptiness) (elements : AbsVal) : Reduced :=
  let elements := elements.reduce
  match emptiness with
  | .bottom => ⟨.bottom, AbsVal.bot⟩
  | .empty => ⟨.empty, AbsVal.bot⟩
  | .nonempty =>
    if elements.isBot then ⟨.bottom, AbsVal.bot⟩
    else ⟨.nonempty, elements⟩
  | .top =>
    if elements.isBot then ⟨.empty, AbsVal.bot⟩
    else ⟨.top, elements⟩

def mayBeEmpty : Emptiness -> Bool
  | .empty | .top => true
  | .bottom | .nonempty => false

def mayBeNonempty : Emptiness -> Bool
  | .nonempty | .top => true
  | .bottom | .empty => false

end Emptiness

end Pylate
