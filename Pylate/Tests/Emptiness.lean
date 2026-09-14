import Pylate.Engine.Update

namespace Pylate.Tests.Emptiness

open Pylate

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def testLattice : IO Unit := do
  for left in Emptiness.all do
    ensure (left.join .bottom == left) "bottom is not a right join identity"
    ensure (Emptiness.bottom.join left == left)
      "bottom is not a left join identity"
    ensure (left.join left == left) "join is not idempotent"
    ensure (Emptiness.bottom.le left) "bottom is not least"
    ensure (left.le .top) "top is not greatest"
    for right in Emptiness.all do
      ensure (left.join right == right.join left) "join is not commutative"
      ensure (left.le right == (left.join right == right))
        "order and join disagree"
      ensure (left.le (left.join right)) "join is not an upper bound"
      ensure (right.le (left.join right)) "join is not an upper bound"
      if left.le right && right.le left then
        ensure (left == right) "order is not antisymmetric"
      for last in Emptiness.all do
        ensure ((left.join right).join last == left.join (right.join last))
          "join is not associative"
        if left.le right && right.le last then
          ensure (left.le last) "order is not transitive"
        if left.le last && right.le last then
          ensure ((left.join right).le last) "join is not least"
  ensure (!(Emptiness.empty.le .nonempty))
    "empty unexpectedly orders below nonempty"
  ensure (!(Emptiness.nonempty.le .empty))
    "nonempty unexpectedly orders below empty"

def testReduction : IO Unit := do
  let elements := V [.tint]
  let bottom := Emptiness.reduce .bottom elements
  ensure (bottom.emptiness == .bottom && bottom.elements.isBot)
    "bottom did not erase its element summary"
  let empty := Emptiness.reduce .empty elements
  ensure (empty.emptiness == .empty && empty.elements.isBot)
    "empty did not erase its element summary"
  let inconsistent := Emptiness.reduce .nonempty AbsVal.bot
  ensure (inconsistent.emptiness == .bottom && inconsistent.elements.isBot)
    "nonempty with no possible element did not reduce to bottom"
  let inferredEmpty := Emptiness.reduce .top AbsVal.bot
  ensure (inferredEmpty.emptiness == .empty)
    "a bottom element summary did not refine top to empty"
  let unknown := Emptiness.reduce .top elements
  ensure (unknown.emptiness == .top && !unknown.elements.isBot)
    "a may-element summary incorrectly proved nonemptiness"

def testStateJoinAndOrder : IO Unit := do
  let location : Loc := ⟨5, .list, true⟩
  let empty := ({} : AState).emptinessSet location .empty
  let nonempty := ({} : AState).emptinessSet location .nonempty
  let joined := empty.join nonempty
  ensure (joined.emptinessGet location == .top)
    "state join did not join collection emptiness"
  ensure (empty.le joined && nonempty.le joined)
    "state order does not place inputs below their join"
  ensure (!(joined.le empty) && !(joined.le nonempty))
    "state order collapsed incomparable emptiness states"
  ensure (({} : AState).le empty)
    "a state with bottom emptiness does not order below empty"

def testFreshAllocation : IO Unit := do
  let (value, state) := allocate {} 10 .list []
  let location : Loc := ⟨10, .list, true⟩
  ensure (value.locs == [location]) "allocation returned the wrong location"
  ensure (state.emptinessGet location == .empty)
    "fresh collection was not initialized empty"
  let (_, objectState) := allocate {} 11 (.obj "Box") []
  ensure (!(objectState.emptinessTracked ⟨11, .obj "Box", true⟩))
    "ordinary objects unexpectedly received collection emptiness"

def testStrongTransitions : IO Unit := do
  let (receiver, initial) := allocate {} 20 .list []
  let location : Loc := ⟨20, .list, true⟩
  let withElement := initial.heapSet location .elem (V [.tint])
  let nonempty := collectionBecomesNonempty withElement receiver .list
  ensure (nonempty.emptinessGet location == .nonempty)
    "singleton grow did not establish nonemptiness"
  let withoutElements := nonempty.heapSet location .elem AbsVal.bot
  let empty := collectionBecomesEmpty withoutElements receiver .list
  ensure (empty.emptinessGet location == .empty)
    "singleton clear did not establish emptiness"

def testWeakMayTargets : IO Unit := do
  let left : Loc := ⟨30, .list, true⟩
  let right : Loc := ⟨31, .list, true⟩
  let receiver := V [.tlist] [left, right]
  let initial := (({} : AState).emptinessSet left .empty)
    |>.emptinessSet right .nonempty
  let grown := collectionBecomesNonempty initial receiver .list
  ensure (grown.emptinessGet left == .top)
    "may-target grow marked an empty candidate definitely nonempty"
  ensure (grown.emptinessGet right == .nonempty)
    "may-target grow lost an existing nonempty fact"
  let cleared := collectionBecomesEmpty initial receiver .list
  ensure (cleared.emptinessGet left == .empty)
    "may-target clear lost an existing empty fact"
  ensure (cleared.emptinessGet right == .top)
    "may-target clear marked a nonempty candidate definitely empty"

def testAliases : IO Unit := do
  let (value, allocated) := allocate {} 40 .set []
  let aliased := (allocated.envSet "left" value).envSet "right" value
  let updated := collectionBecomesNonempty aliased
    (aliased.envGet "left") .set
  let alias := updated.envGet "right"
  ensure (alias.locs == value.locs) "alias points-to information changed"
  ensure (updated.emptinessGet alias.locs.head! == .nonempty)
    "an emptiness update was not visible through an alias"

def testRecencyFolding : IO Unit := do
  let recent : Loc := ⟨50, .list, true⟩
  let summary : Loc := ⟨50, .list, false⟩
  let (oldValue, allocated) := allocate {} 50 .list []
  let oldState := ((allocated.heapSet recent .elem (V [.tstr]))
      |>.emptinessSet summary .empty)
    |>.envSet "old" oldValue
  let oldState := collectionBecomesNonempty oldState oldValue .list
  let (_, folded) := allocate oldState 50 .list []
  ensure (folded.emptinessGet summary == .top)
    "recency folding did not join colliding emptiness summaries"
  ensure (folded.emptinessGet recent == .empty)
    "new recent collection was not initialized empty"
  ensure ((folded.envGet "old").locs == [summary])
    "recency folding did not rename an alias to the summary location"

def runAll : IO Unit := do
  testLattice
  testReduction
  testStateJoinAndOrder
  testFreshAllocation
  testStrongTransitions
  testWeakMayTargets
  testAliases
  testRecencyFolding
  IO.println "Emptiness tests passed"

end Pylate.Tests.Emptiness
