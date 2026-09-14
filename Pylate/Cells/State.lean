/-
The cell layer: association-list environment and heap keyed by
(location, field), collection emptiness keyed by location, reads with the
unbound/bottom defaults, strong writes versus weak joins, state join/order,
and the recency fold that demotes a recent block to its summary. An absent
variable reads as {tunbound}, uniformly (the spec's stated default).
-/
import Std.Data.HashMap
import Pylate.Domains.Emptiness
import Pylate.Cells.Selector

namespace Pylate

open Std

/-- The heap is a hash map, not an association list, because `join` is the most
    frequent operation in the interpreter and every cost in it was quadratic in
    the cell count: `heapKeys` built a set by folding a linear `Fset.insert`
    (O(H^2)), `join` did that twice, unioned the results (O(H^2) again), then per
    key did two linear `heapGet`s and, for a literal key, two more full scans.

    A corpus whose module level runs 280 `try`/`except` drivers -- each one a join
    -- against a heap that nothing prunes turned that into O(U^3): 57 minutes for
    one file. The same file with its drivers cut off took 7 seconds, which is why
    the defect stayed invisible until the corpus became admissible.

    `Repr` can no longer be derived, because a `HashMap` has none. It is written
    out below instead of dropped: downstream types derive `Repr` structurally, so
    removing it breaks them, and a state's debug rendering is worth keeping. -/
structure AState where
  env       : HashMap String AbsVal := {}
  heap      : HashMap (Loc × CellSelector) AbsVal := {}
  /-- Collection size, which subsumes emptiness: `Size.emptiness` projects it and
      `Size.emptiness_join` proves the projection is a lattice homomorphism, so
      every reader that wants only emptiness gets exactly what it got before. -/
  sizes     : HashMap Loc Size := {}
deriving Inhabited

/-- Debug rendering only. Keys are sorted so the output is deterministic: a hash
    map's iteration order is not, and an unstable `Repr` makes a failing test
    print differently on each run. -/
instance : Repr AState where
  reprPrec st _ :=
    let cells := (st.heap.toList.map (fun (k, v) =>
      s!"({k.1.render}, {k.2.render}) -> {reprStr v}")).mergeSort (· < ·)
    let empt := (st.sizes.toList.map (fun (l, e) =>
      s!"{l.render} -> {reprStr e}")).mergeSort (· < ·)
    let vars := (st.env.toList.map (fun (x, v) =>
      s!"{x} -> {reprStr v}")).mergeSort (· < ·)
    Std.Format.text
      s!"AState env:={vars} heap:={cells} sizes:={empt}"

/-- Whether a write through this value may be a *strong* update of this location.

    All four conjuncts are load-bearing. One tag and one location mean the write
    cannot be landing somewhere else; `recent` means the location is the
    most-recent block of its site rather than the summary of every block, which is
    the only case where overwriting is sound; and no witness means no other name
    reaches the cell.

    This lived in four textually identical copies -- two called
    `completeStrongTarget`, two called `isSoleRecentTarget` -- and no test
    distinguished them. It belongs here, beside `heapSet` and `heapJoin`, because
    it is the rule for choosing between them, not a per-transfer judgement. -/
def strongUpdateTarget (value : AbsVal) (l : Loc) : Bool :=
  value.tags == [l.cls.tag] &&
    value.locs == [l] &&
    l.recent &&
    !value.witness

namespace AState

def envGet (st : AState) (x : String) : AbsVal :=
  st.env.getD x unboundV

def envSet (st : AState) (x : String) (v : AbsVal) : AState :=
  { st with env := st.env.insert x v.reduce }

def envKill (st : AState) (x : String) : AState :=
  st.envSet x unboundV

def heapGet (st : AState) (l : Loc) (f : CellSelector) : AbsVal :=
  st.heap.getD (l, f) AbsVal.bot

/-- Whether a cell exists at all, which is not the same question as whether its
    value is non-bottom: a cell can exist holding bottom. Key presence is cell
    existence, the same distinction the join records. -/
def heapHas (st : AState) (l : Loc) (f : CellSelector) : Bool :=
  st.heap.contains (l, f)

def heapSet (st : AState) (l : Loc) (f : CellSelector) (v : AbsVal) : AState :=
  { st with heap := st.heap.insert (l, f) v.reduce }

def heapJoin (st : AState) (l : Loc) (f : CellSelector) (v : AbsVal) : AState :=
  st.heapSet l f ((st.heapGet l f).join v)

/-- The heap write a store performs: strong when the target is unambiguous and
    most-recent, weak otherwise. Stating it once removes the chance of a transfer
    picking the wrong one, which is what four copies of the predicate invited. -/
def heapStore (st : AState) (value : AbsVal) (l : Loc) (f : CellSelector)
    (v : AbsVal) : AState :=
  if strongUpdateTarget value l then st.heapSet l f v else st.heapJoin l f v

/-- How many tuple slots a location carries.

    Written out three times -- `Machine`, `RuleContracts`, `RuleIteration` -- as a
    filter over the heap followed by `.length`, which the port to a hash map
    surfaced by breaking all three identically. -/
def tupleSlotCount (st : AState) (l : Loc) : Nat :=
  st.heap.fold (init := 0) fun count key _ =>
    if key.1 == l then
      match key.2 with
      | .tupleSlot _ => count + 1
      | _ => count
    else count

def heapDel (st : AState) (l : Loc) (f : CellSelector) : AState :=
  { st with heap := st.heap.erase (l, f) }

/-- An untracked location is unknown, not unreachable: `bottom` would let a
    caller prove emptiness it never established. Allocation records `empty`
    explicitly, so every genuinely fresh collection is still precise. -/
def sizeGet (st : AState) (l : Loc) : Size :=
  st.sizes.getD l .top

/-- Strong update of one location's size. -/
def sizeSet (st : AState) (l : Loc) (value : Size) : AState :=
  if value == .bottom then { st with sizes := st.sizes.erase l }
  else { st with sizes := st.sizes.insert l value }

/-- Weak update of one location's size. -/
def sizeJoin (st : AState) (l : Loc) (value : Size) : AState :=
  st.sizeSet l ((st.sizeGet l).join value)

/-- The exact element count, when it is known. -/
def sizeExact? (st : AState) (l : Loc) : Option Nat :=
  match st.sizeGet l with
  | .exact n => some n
  | _ => none

/-- Are all the index's possible values within the receiver's bounds?

    Answering this needs a length *and* an index, which is why it was owed to the
    solver: `Emptiness` gave non-emptiness only, so `xs[0]` on a two-element list
    still carried a `bounds` obligation while `t[1]` on a tuple did not.

    Two length sources. A container contributes `Size.exact`, and only from a
    single location -- a may-alias over two lists of different lengths proves
    nothing. A `str` has no location at all, so its length comes from the literal
    set, and with several literals the shortest one governs.

    Deliberately conservative in three ways: the index must be closed `int`
    literals, a `bool` index bails rather than being read as 0/1, and negative
    indices are accepted only within `-n ≤ i`, which is exactly Python's rule. -/
def indexDefinitelyInRange (st : AState) (receiver index : AbsVal) : Bool :=
  let closedInt :=
    !index.intOpen && !index.intLits.isEmpty &&
      index.tags.all (fun t => t == Tag.tint)
  if !closedInt then false
  else
    let within := fun (n : Nat) =>
      index.intLits.all (fun i => -(Int.ofNat n) ≤ i && i < Int.ofNat n)
    match receiver.locs with
    | [location] =>
      match st.sizeExact? location with
      | some n => within n
      | none => false
    | [] =>
      if receiver.tags == [Tag.tstr] && !receiver.strOpen &&
          !receiver.strLits.isEmpty then
        within (receiver.strLits.foldl
          (fun best s => min best s.length) receiver.strLits.length)
      else false
    | _ => false

def emptinessGet (st : AState) (l : Loc) : Emptiness :=
  (st.sizeGet l).emptiness

/-- Whether the component records this location at all. -/
def emptinessTracked (st : AState) (l : Loc) : Bool :=
  st.sizes.contains l

/-- Strong update of one abstract collection location.

    Setting an emptiness *forgets* any count rather than contradicting one:
    `ofEmptiness` is the coarsest size with that emptiness. A caller that knows
    the count should use `sizeSet`. -/
def emptinessSet (st : AState) (l : Loc) (value : Emptiness) : AState :=
  st.sizeSet l (Size.ofEmptiness value)

/-- Weak update of one abstract collection location. -/
def emptinessJoin (st : AState) (l : Loc) (value : Emptiness) : AState :=
  st.sizeJoin l (Size.ofEmptiness value)

/-- Straight from the map. This was a fold of `Fset.insert`, so O(E^2), and
    `join` unioned two of them -- the same shape the heap had. -/
def envKeys (st : AState) : List String :=
  st.env.keys

/-- The keys, straight from the map. This was a fold of `Fset.insert` over the
    association list, so building it was O(H^2) in the cell count -- and `join`
    called it twice before unioning the results. -/
def heapKeys (st : AState) : List (Loc × CellSelector) :=
  st.heap.keys

def emptinessKeys (st : AState) : List Loc :=
  st.sizes.keys

/-- The emptiness a state contributes to a join. An untracked location that
    the state never mentions denotes no collection there, so it contributes
    `bottom`; one the state does mention is merely unknown, so `top`. -/
def sizeContribution (st : AState) (l : Loc) : Size :=
  match st.sizes[l]? with
  | some value => value
  | none =>
    if st.heap.any (fun key _ => key.1 == l) then .top else .bottom

def emptinessContribution (st : AState) (l : Loc) : Emptiness :=
  (st.sizeContribution l).emptiness

def join (a b : AState) : AState :=
  let env := a.env.fold (init := ({} : HashMap String AbsVal))
    (fun acc x v => acc.insert x (v.join (b.env.getD x unboundV)).reduce)
  let env := b.env.fold (init := env)
    (fun acc x v =>
      if acc.contains x then acc
      else acc.insert x (v.join (a.env.getD x unboundV)).reduce)
  -- One pass over each side instead of building and unioning key sets. A key in
  -- both sides is joined once, on the second visit.
  --
  -- A per-key cell present on one path and absent on the other is a key that
  -- may not be there. `heapGet` reads an absent cell as bottom, and joining a
  -- value with bottom yields the value, which would read back as proof of
  -- presence -- so `d = {}` then `if flag: d["k"] = v` would discharge the
  -- KeyError on `d["k"]`. The may-absence is recorded explicitly instead.
  -- Only `literalKey` needs this: an absent field or element summary already
  -- means uninitialised, which the `.tuninit` marker carries.
  --
  -- Presence is cell *existence*, not a non-bottom value. A cell can exist
  -- holding bottom -- a store whose value satisfies no declared annotation
  -- leaves exactly that -- and reading bottom as absence turns a type error
  -- into a spurious KeyError.
  let mergeCell := fun (heap : HashMap (Loc × CellSelector) AbsVal)
      (other : AState) (key : Loc × CellSelector) (value : AbsVal) =>
    let joined := value.join (other.heap.getD key AbsVal.bot)
    let joined := match key.2 with
      | .literalKey _ =>
        if other.heap.contains key then joined
        else joined.join (V [.tmissing])
      | _ => joined
    heap.insert key joined.reduce
  let heap := a.heap.fold (init := ({} : HashMap (Loc × CellSelector) AbsVal))
    (fun acc key value => mergeCell acc b key value)
  let heap := b.heap.fold (init := heap)
    (fun acc key value =>
      if acc.contains key then acc else mergeCell acc a key value)
  let ekeys := Fset.union (a.emptinessKeys.foldr Fset.insert [])
    (b.emptinessKeys.foldr Fset.insert [])
  let sizes := ekeys.foldl (init := ({} : HashMap Loc Size))
    (fun out location =>
      let value := (a.sizeContribution location).join
        (b.sizeContribution location)
      if value == .bottom then out else out.insert location value)
  { env, heap, sizes }

def le (a b : AState) : Bool :=
  (Fset.union a.envKeys b.envKeys).all
    (fun x => (a.envGet x).le (b.envGet x)) &&
  a.heapKeys.all (fun (l, f) => (a.heapGet l f).le (b.heapGet l f)) &&
  a.emptinessKeys.all
    (fun location => (a.emptinessGet location).le
      (b.emptinessGet location))

/-- Rename the recent block of (site, cls) to its summary everywhere:
    environment values, heap values, heap keys, and emptiness keys.
    Colliding heap and emptiness rows join. The recency fold of
    LEAN_SPEC.md 6.1. -/
def foldRecent (st : AState) (site : NodeId) (cls : LocCls) : AState :=
  let old : Loc := ⟨site, cls, true⟩
  let new : Loc := ⟨site, cls, false⟩
  let env := st.env.fold (init := ({} : HashMap String AbsVal))
    (fun acc x v => acc.insert x (v.renameLoc old new))
  let heap := st.heap.fold
    (init := ({} : HashMap (Loc × CellSelector) AbsVal))
    (fun acc key v =>
      let l' := if key.1 = old then new else key.1
      let v' := v.renameLoc old new
      -- Renaming can collide the recent block with its own summary, and the two
      -- rows join rather than one winning.
      let joined := match acc[(l', key.2)]? with
        | some prev => (prev.join v').reduce
        | none => v'
      acc.insert (l', key.2) joined)
  let sizes := st.sizes.fold
    (init := ({} : HashMap Loc Size))
    (fun acc location value =>
      let location' := if location = old then new else location
      let previous := acc.getD location' .bottom
      let joined := previous.join value
      if joined == .bottom then acc.erase location'
      else acc.insert location' joined)
  { env, heap, sizes }

end AState

def joinOpt : Option AState → Option AState → Option AState
  | none, b => b
  | a, none => a
  | some a, some b => some (a.join b)

def leOpt : Option AState → Option AState → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => a.le b

-- ------------------------------------------------------- statement modes

end Pylate
