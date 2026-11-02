/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.World
public import StrataDyn.Exec.Effects
public import StrataPython.Dyn.Sem.Store
public import StrataPython.Dyn.Sem.Hash
public import Std.Data.TreeMap

set_option autoImplicit false

/-!
# Python's world

The world at the run token `σ` has six parts, each of its own type, so that a rule names the parts
it uses:

* `ObjStore σ`, the objects;
* `Modules σ`, each module's object and its global cells by name;
* `Handled`, the exception being handled;
* `Depth`, the depth of Python calls and CPython's C recursion count;
* `ReprGuard`, the objects whose `repr` is being computed;
* `Output`, what the program wrote to standard output.

`Depth` and `ReprGuard` are bookkeeping: a rule may change them while it runs, and leaves them as
it found them.  The primitives that change `Depth` (a call, the call bracket, and the two depth
counts) write back what they changed before they go on: a call and the bracket the whole depth,
a depth count its own counter (`Prim.callClosureT_restores`,
`Prim.bracketed_restores`, `Prim.withDepth_restores`, `Prim.withPyDepth_restores`).

The effects of a rule (`Effects.Within`) are stated relative to its operation's `Start`, through
`spec`: `same` allows new objects, new entries of the module table and changes of the
bookkeeping parts, and `immEq` says which worlds a `pure` operation can't tell apart.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

@[expose] public section

/-- A module's object id, and its global cells by name.  A cell made on first use holds
`undef`. -/
structure ModuleEntry (σ : Type) [Store σ] where
  obj : ObjId
  cells : Std.TreeMap String (Ref σ Value) := {}

/-- The modules, by name. -/
structure Modules (σ : Type) [Store σ] where
  map : Std.TreeMap String (ModuleEntry σ) := {}

/-- The exception being handled, `None` if none. -/
structure Handled where
  exc : Value := .none
  deriving Repr, Inhabited

/-- The depth of Python calls (`py`), CPython's C recursion count (`c`), and how many call
brackets of built-ins that run user code are open (`bracket`).  Only a bracket's own edges (`bracketed`, `callClosureT`) change `bracket`:
at `calls`, an update whose world is inside a bracket may change anything (`WorldSpec.inCall`). -/
structure Depth where
  py : Nat := 0
  c : Nat := 0
  bracket : Nat := 0
  deriving Repr, Inhabited, DecidableEq

/-- The objects whose `repr` is being computed, as CPython's `Py_ReprEnter` list. -/
structure ReprGuard where
  active : Array ObjId := #[]
  deriving Repr, Inhabited, DecidableEq

/-- What the program wrote to standard output, in pieces. -/
structure Output where
  pieces : Array String := #[]
  deriving Repr, Inhabited, DecidableEq

/-- Python's world at the run token `σ`. -/
structure World (σ : Type) [Store σ] where
  store : ObjStore σ := {}
  modules : Modules σ := {}
  handled : Handled := {}
  depth : Depth := {}
  guard : ReprGuard := {}
  out : Output := {}

#dyn_world World

variable {σ : Type} [Store σ]

/-- What a rule's computation reads once, at the start of its activation: objects with smaller ids
existed before the activation. -/
structure Start where
  storeSize : Nat
  deriving Repr, Inhabited, DecidableEq

/-- What a `pure` operation may read of an old object: its class, and a function's closure.
The rest of an old object may change, a function's name and module included. -/
def Obj.imm (o : Obj σ) : Value × Option (FnRef σ [Value, Value] (Except Value Value)) :=
  (o.cls, match o.payload with | .func f => some f.closure | _ => none)

/-- Every entry of the module table of `w` is in that of `w'`, unchanged. -/
def Modules.Extends (m m' : Modules σ) : Prop :=
  ∀ (k : String) (e : ModuleEntry σ), m.map[k]? = some e →
    ∃ e', m'.map[k]? = some e' ∧ e'.obj = e.obj ∧
      ∀ (n : String) (r : Ref σ Value), e.cells[n]? = some r → e'.cells[n]? = some r

/-- The module table with the cell `r` of `name` in `module`, whose object is `obj` if the table
has no entry for `module` yet. -/
def Modules.withCell (m : Modules σ) (module name : String) (obj : ObjId) (r : Ref σ Value) :
    Modules σ :=
  match m.map[module]? with
  | some e => ⟨m.map.insert module { e with cells := e.cells.insertIfNew name r }⟩
  | none => ⟨m.map.insert module ⟨obj, (∅ : Std.TreeMap String (Ref σ Value)).insert name r⟩⟩

/-- The module table with a new entry for `name`, whose object is `obj` and which has no cells,
if the table has none for `name`; the table as it is otherwise. -/
def Modules.addNew (m : Modules σ) (name : String) (obj : ObjId) : Modules σ :=
  if (m.map[name]?).isSome then m else ⟨m.map.insert name ⟨obj, {}⟩⟩

/-- The global cell `name` of `module`, if the module table holds it. -/
def Modules.cell? (m : Modules σ) (module name : String) : Option (Ref σ Value) :=
  (m.map[module]?).bind fun e => e.cells[name]?

/-- The world `w'` changes none of the state of `w` that an operation must leave alone: the
objects that existed before the start `s`, the entries of the module table, the exception being
handled, and the output.  New objects, new entries and the bookkeeping parts may
change. -/
def Same (s : Start) (w w' : World σ) : Prop :=
  w.store.size ≤ w'.store.size ∧
  (∀ id o, id < s.storeSize → w.store.get? id = some o → w'.store.get? id = some o) ∧
  w.modules.Extends w'.modules ∧ w'.handled.exc = w.handled.exc ∧ w'.out = w.out

/-- Two worlds that a `pure` operation with the start `s` can't tell apart: the same objects since
`s`, the same class and closure for each older object, and the same module table: the same object
and the same cells for each module. -/
def ImmEq (s : Start) (w₁ w₂ : World σ) : Prop :=
  w₁.store.size = w₂.store.size ∧
  (∀ id, s.storeSize ≤ id → w₁.store.get? id = w₂.store.get? id) ∧
  (∀ id, id < s.storeSize → (w₁.store.get? id).map Obj.imm = (w₂.store.get? id).map Obj.imm) ∧
  (∀ k : String, (w₁.modules.map[k]?).map (ModuleEntry.obj (σ := σ)) =
    (w₂.modules.map[k]?).map (ModuleEntry.obj (σ := σ))) ∧
  ∀ (k n : String), w₁.modules.cell? k n = w₂.modules.cell? k n

/-- A world whose store grows by one object. -/
def World.allocObj (o : Obj σ) (w : World σ) : World σ := { w with store := (w.store.alloc o).1 }

/-- A world whose object `id` is changed by `f`. -/
def World.updObj (id : ObjId) (f : Obj σ → Obj σ) (w : World σ) : World σ :=
  { w with store := w.store.update id f }

/-- A world is inside a call bracket when one is open.  A call into Python lowers the marker for
the callee's run (`callClosureT`), so the marker is set only while the built-in body that opened
the bracket runs, not in the rules of the Python code that it calls. -/
instance : HasInCall (World σ) := ⟨fun w => w.depth.bracket != 0⟩

/-- The value that the name `name` of `dir(builtins)` is bound to. -/
def builtinValue (name : String) : Value :=
  match name with
  | "None" => .none
  | "True" | "__debug__" => .bool true
  | "False" => .bool false
  | "Ellipsis" => .ellipsis
  | "NotImplemented" => .notImplemented
  | _ => match Builtin.ofName? name with
    | some b => .builtin b
    | none => match Builtin.strNames.lookup name with
      | some v => .ofString v
      | none => .undef name

/-- The `builtins` module's dict: every name of `vars(builtins)`, in its order. -/
def builtinsDict : DictTable :=
  Builtin.dictNames.foldl (fun t n =>
    t.insertNew ⟨strHash (.ofString n), .ofString n, .builtin⟩ (builtinValue n)) .empty

/-- The initial world: the `builtins` module, object `1`, whose `__dict__`, object `0`, binds
every name of `vars(builtins)` to its value. -/
def w0 : World σ where
  store := ⟨#[⟨.builtin .dict, none, #[], .dict builtinsDict⟩,
    ⟨.builtin .module, some 0, #[], .module ⟨"builtins", #[], false⟩⟩]⟩
  modules := ⟨Std.TreeMap.empty.insert "builtins" ⟨1, {}⟩⟩

/-- A table starts its runs from the initial world. -/
instance : Inhabited (World σ) := ⟨w0⟩

end

end StrataPython.Dyn.Sem
