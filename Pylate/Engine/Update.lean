/-
Pure rules over cells: element reads across container tags, the
allocation rule (recency fold, fresh recent block, uninitialized
layout), heap reachability, and merging an exceptional flow into a
statement outcome.
-/
import Pylate.Cells.Multi
import Pylate.Engine.Exc

namespace Pylate

abbrev dictViewSourceCell : CellSelector := .dictViewSource

structure DictItemCase where
  key   : AbsVal
  value : AbsVal
deriving Repr, Inhabited

private def exactDictCells (st : AState) (source : Loc) :
    List (String × AbsVal) :=
  st.heap.fold (init := []) fun out key stored =>
    let (location, cell) := key
    match cell with
    | .literalKey key =>
      if location == source then
        let present := stored.withoutTags [.tmissing]
        if present.isBot then out else (key, present) :: out
      else out
    | _ => out

private def exactDictKeys (entries : List (String × AbsVal)) : AbsVal :=
  entries.foldl
    (fun out entry => out.join (strLitV entry.1))
    AbsVal.bot

private def exactDictValues (entries : List (String × AbsVal)) : AbsVal :=
  entries.foldl
    (fun out entry => out.join entry.2)
    AbsVal.bot

/--
Read the current key summary of one dictionary location. TypedDict exact
field cells are authoritative when present, so a definitely absent optional
field does not leak back in through the declaration-wide `key` summary.
Generic dictionaries retain their smashed summary alongside exact literal
cells.
-/
def dictKeysAt (st : AState) (source : Loc) : AbsVal :=
  let entries := exactDictCells st source
  let exact := exactDictKeys entries
  match source.cls with
  | .td _ =>
    if entries.isEmpty then st.heapGet source .dictKeys else exact
  | .dict => exact.join (st.heapGet source .dictKeys)
  | _ => AbsVal.bot

/-- Current value summary, with TypedDict missing sentinels removed. -/
def dictValuesAt (st : AState) (source : Loc) : AbsVal :=
  let entries := exactDictCells st source
  let exact := exactDictValues entries
  match source.cls with
  | .td _ =>
    if entries.isEmpty then
      (st.heapGet source .dictValues).withoutTags [.tmissing]
    else exact
  | .dict => exact.join (st.heapGet source .dictValues)
  | _ => AbsVal.bot

def dictKeysOfSources (st : AState) (sources : AbsVal) : AbsVal := Id.run do
  let mut out : AbsVal := AbsVal.bot
  for source in sources.locs do
    if source.cls.tag == .tdict then
      out := out.join (dictKeysAt st source)
  if Tag.tany ∈ sources.tags then
    out := out.join anyV
  return out.reduce

def dictValuesOfSources (st : AState) (sources : AbsVal) : AbsVal := Id.run do
  let mut out : AbsVal := AbsVal.bot
  for source in sources.locs do
    if source.cls.tag == .tdict then
      out := out.join (dictValuesAt st source)
  if Tag.tany ∈ sources.tags then
    out := out.join anyV
  return out.reduce

/--
The relational part of an items view. Exact literal-key cells and TypedDict
field cells remain paired here; callers that cannot consume alternatives use
the sound smashed key/value summaries instead.
-/
def dictItemCasesOfSources (st : AState) (sources : AbsVal) :
    List DictItemCase := Id.run do
  let mut out : List DictItemCase := []
  for source in sources.locs do
    if source.cls.tag == .tdict then
      for (key, value) in exactDictCells st source do
        out := out ++ [{ key := strLitV key, value }]
  return out

def dictViewItemCases (st : AState) (view : AbsVal) :
    List DictItemCase := Id.run do
  let mut out : List DictItemCase := []
  for location in view.locs do
    if location.cls == .dictitems then
      let sources := st.heapGet location dictViewSourceCell
      out := out ++ dictItemCasesOfSources st sources
  return out

/--
Read a slot from an items-view tuple proxy. This is deliberately source
linked: a mutation after `items()` but before tuple consumption is visible.
-/
def dictItemSlot (st : AState) (pair : AbsVal) (index : Nat) :
    AbsVal := Id.run do
  let mut out : AbsVal := AbsVal.bot
  for location in pair.locs do
    if location.cls == .tuple then
      let sources := st.heapGet location dictViewSourceCell
      if sources.isBot then
        out := out.join (st.heapGet location (.tupleSlot index))
      else if index == 0 then
        out := out.join (dictKeysOfSources st sources)
      else if index == 1 then
        out := out.join (dictValuesOfSources st sources)
  return out.reduce

private def dictViewElements (st : AState) (location : Loc) : AbsVal :=
  let sources := st.heapGet location dictViewSourceCell
  if sources.isBot then
    st.heapGet location .elem
  else
    match location.cls with
    | .dictkeys => dictKeysOfSources st sources
    | .dictvalues => dictValuesOfSources st sources
    | .dictitems =>
      let keys := dictKeysOfSources st sources
      let values := dictValuesOfSources st sources
      if keys.isBot || values.isBot then AbsVal.bot
      else st.heapGet location .elem
    | _ => AbsVal.bot

/--
Element value of an iterable (the may-join over its locations).

Dictionary views and their item tuple proxies dereference the source
dictionary on every query. Thus mutation between view creation and iteration
is visible. Active iterators currently have only `elem` and `nonempty` cells;
detecting CPython's mutation-during-iteration `RuntimeError` additionally
requires a source reference plus a captured structural epoch on `.gen`, with
the dictionary epoch advanced only when its key set changes.
-/
def elemOf (st : AState) (v : AbsVal) : AbsVal := Id.run do
  let mut out : AbsVal := AbsVal.bot
  for t in v.tags do
    match t with
    | .tlist | .tset | .tgen =>
      for l in v.locs do
        if l.cls.tag == t then
          out := out.join (st.heapGet l .elem)
    | .ttuple =>
      for l in v.locs do
        if l.cls == .tuple then
          let sources := st.heapGet l dictViewSourceCell
          if sources.isBot then
            out := out.join (st.heapGet l .elem)
          else
            out := out.join (dictKeysOfSources st sources)
              |>.join (dictValuesOfSources st sources)
    | .tdictkeys | .tdictitems | .tdictvalues =>
      for l in v.locs do
        if l.cls.tag == t then
          out := out.join (dictViewElements st l)
    | .trange => out := out.join (V [.tint])
    | .tstr => out := out.join (V [.tstr])
    | .tdict =>
      for l in v.locs do
        if l.cls.tag == .tdict then
          out := out.join (st.heapGet l .dictKeys)
    | .tany => out := out.join anyV
    | _ => pure ()
  return out.reduce

def LocCls.tracksEmptiness : LocCls -> Bool
  | .list | .dict | .dictkeys | .dictitems | .dictvalues
  | .set | .tuple | .range | .gen | .td _ => true
  | .obj _ => false

/-- The singleton criterion for a sound strong collection update. -/
def isStrongCollectionTarget (receiver : AbsVal) (location : Loc) : Bool :=
  receiver.tags == [location.cls.tag] &&
  receiver.locs == [location] &&
  location.recent &&
  !receiver.witness

/-- Strong emptiness update for a location known to denote one object. -/
def strongEmptinessUpdate (st : AState) (location : Loc)
    (value : Emptiness) : AState :=
  st.emptinessSet location value

/-- Weak emptiness update for a summary or may-target location. -/
def weakEmptinessUpdate (st : AState) (location : Loc)
    (value : Emptiness) : AState :=
  st.emptinessJoin location value

/-- Strong size update. Unlike `strongEmptinessUpdate` this keeps the count, so a
    literal can record how many elements it has. -/
def strongSizeUpdate (st : AState) (location : Loc) (value : Size) : AState :=
  st.sizeSet location value

def weakSizeUpdate (st : AState) (location : Loc) (value : Size) : AState :=
  st.sizeJoin location value

/--
Apply one collection operation's emptiness postcondition.  A complete recent
singleton is updated strongly.  Every location in a may-target receiver is
updated weakly, preserving the possibility that another location was chosen.
-/
def updateCollectionEmptiness (st : AState) (receiver : AbsVal)
    (cls : LocCls) (value : Emptiness) : AState := Id.run do
  let mut out := st
  for location in receiver.locs do
    if location.cls == cls then
      if isStrongCollectionTarget receiver location then
        out := strongEmptinessUpdate out location value
      else
        out := weakEmptinessUpdate out location value
  return out

/-- Set a collection's size, strongly where the write is a strong update. A
    may-target gets a weak update, so joining two lists of different lengths
    lands on `positive` rather than a count neither of them has. -/
def updateCollectionSize (st : AState) (receiver : AbsVal)
    (cls : LocCls) (value : Size) : AState := Id.run do
  let mut out := st
  for location in receiver.locs do
    if location.cls == cls then
      if isStrongCollectionTarget receiver location then
        out := strongSizeUpdate out location value
      else
        out := weakSizeUpdate out location value
  return out

def collectionBecomesEmpty (st : AState) (receiver : AbsVal)
    (cls : LocCls) : AState :=
  updateCollectionEmptiness st receiver cls .empty

def collectionBecomesNonempty (st : AState) (receiver : AbsVal)
    (cls : LocCls) : AState :=
  updateCollectionEmptiness st receiver cls .nonempty

def collectionBecomesMaybeEmpty (st : AState) (receiver : AbsVal)
    (cls : LocCls) : AState :=
  updateCollectionEmptiness st receiver cls .top


def allocate (st : AState) (site : NodeId) (cls : LocCls)
    (layout : Fset String) : AbsVal × AState := Id.run do
  let st := st.foldRecent site cls
  let l : Loc := ⟨site, cls, true⟩
  -- reset the fresh block's edges
  let mut st := { st with
    heap := st.heap.filter (fun key _ => key.1 != l)
    sizes := st.sizes.filter (fun location _ => location != l) }
  for f in layout do
    st := st.heapSet l (.field f) (V [.tuninit])
  if cls.tracksEmptiness then
    st := st.emptinessSet l .empty
  return (V [cls.tag] (locs := [l]), st)


/-- Locations reachable from a set of root values through the heap.

    The points-to edges are built once, in a single pass, and the fixpoint walks
    them. Before, each round scanned the whole heap once per root, so the cost was
    O(rounds x roots x cells). -/
partial def reachableLocs (st : AState) (roots : Fset Loc) : Fset Loc :=
  let edges : Std.HashMap Loc (Fset Loc) :=
    st.heap.fold (init := {}) fun acc key value =>
      acc.insert key.1 (Fset.union value.locs (acc.getD key.1 []))
  let rec walk (frontier : List Loc) (seen : Fset Loc) : Fset Loc :=
    match frontier with
    | [] => seen
    | l :: rest =>
      let next := (edges.getD l []).filter (fun target => !(target ∈ seen))
      walk (next ++ rest) (Fset.union next seen)
  walk roots roots


def withExc (m : AMulti) (e : Exc) : AMulti :=
  if e.isEmpty then m
  else { m with
    excSt := joinOpt m.excSt e.st
    excs := Fset.union e.tags m.excs }

end Pylate
