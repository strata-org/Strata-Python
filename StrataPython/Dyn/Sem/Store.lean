/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Sem
public import StrataPython.Dyn.Sem.Dict
public import StrataPython.Dyn.Sem.Set

set_option autoImplicit false

/-!
# Objects and the store

A mutable Python object (`Obj σ`) has a class, an optional `__dict__` (a dict object), the values
of its `__slots__`, and a payload that holds its built-in state.  The store (`ObjStore σ`) is an
array of objects that only grows; an object's id is its index.

Machine cells and closures live only in function objects (`FuncObj σ`), which hold their closure,
and in the module table of the world.  So the objects take the run token `σ`, and `Value` doesn't:
a value holds only object ids.

`ObjG F` is an object whose function payload is an `F`.  The store holds `Obj σ`, whose function
payload holds a closure; the primitives of the rules make and change `ObjData`, whose function
payload is empty, so that no rule makes a function object other than `mkClosure`.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

@[expose] public section

/-- What a native function is to `type()`: a Python function, or one of CPython's C kinds. -/
inductive NativeKind where
  | function
  | wrapperDescriptor
  | methodWrapper
  | builtinFunctionOrMethod
  | methodDescriptor
  deriving DecidableEq, Repr, Inhabited

/-- A function with a Lean body: the key of its body in the assembly's list of native
functions, what it captured, its attributes, and the attribute names whose read gaps. -/
structure NativeFn where
  key : String
  kind : NativeKind
  captured : Array Value := #[]
  name : String
  qualname : String
  module : String
  defaults : Option Value := none
  kwdefaults : Option Value := none
  gapped : Array String := #[]
  deriving Repr, Inhabited

/-- A class made by `__build_class__` or by a module's builder.  Its metaclass is the object's
class. -/
structure ClassObj where
  name : String
  qualname : String
  module : String
  bases : Array Value
  /-- Its method resolution order, computed once by C3; it starts with the class itself. -/
  mro : Array Value
  /-- Its namespace, in insertion order. -/
  ns : DictTable := .empty
  /-- The nearest class in its base chain whose instances have a layout of their own. -/
  solidBase : Value
  /-- Whether its instances get a `__dict__`. -/
  instanceDict : Bool := true
  /-- Its own slot names, each with a `member` descriptor in the namespace. -/
  slots : Array String := #[]
  /-- `setattr` and `delattr` on the class raise `TypeError`. -/
  immutable : Bool := false
  /-- Names whose lookup gaps. -/
  gapped : Array String := #[]
  /-- `setattr` and `delattr` on the class gap. -/
  writesGap : Bool := false
  /-- The generic attribute writes and deletions on its instances gap. -/
  instanceWritesGap : Bool := false
  /-- A C-level type name for messages. -/
  tpName : Option String := none
  /-- Whether it defines `__del__`. -/
  hasDel : Bool := false

instance : Inhabited ClassObj :=
  ⟨⟨"", "", "", #[], #[], .empty, .none, true, #[], false, #[], false,
  false, none, false⟩⟩

/-- A translated function: its closure, with its cells bound in, its `__name__`, and its
`__module__`, the value of its module's `__name__` global when it was made. -/
structure FuncObj (σ : Type) [Store σ] where
  closure : FnRef σ [Value, Value] (Except Value Value)
  name : String
  module : Value

/-- The state of an exception: its `args`, its chaining, and the fields of its class
(`StopIteration.value`, `NameError.name`, …) by name. -/
structure ExcState where
  args : Value := .tuple #[]
  context : Value := .none
  cause : Value := .none
  suppressContext : Bool := false
  traceback : Value := .none
  notes : Option Value := none
  fields : Array (String × Value) := #[]
  deriving Repr, Inhabited

/-- The state of a built-in iterator or view. -/
inductive IterState where
  /-- An iterator of the type `kind` over the sequence `target` (a list, tuple, `str` or
  `bytes`), at `index`; a reverse iterator counts down. -/
  | seq (kind : Builtin) (target : Value) (index : Nat)
  /-- A range iterator: the next value, the bound and the step. -/
  | range (kind : Builtin) (next stop step : Int)
  /-- An iterator of the type `kind` over a dict, at `index` of its entries, with the size and
  the keys' version it started with. -/
  | dict (kind : Builtin) (target : ObjId) (index size keysVersion : Nat)
  /-- A set iterator, at `index` of the table, with the size it started with. -/
  | set (target : ObjId) (index size : Nat)
  /-- A view of the type `kind` of a dict. -/
  | view (kind : Builtin) (target : ObjId)
  | zip (iters : Array Value)
  | enumerate (iter : Value) (count : Int)
  | reversed (target : Value) (index : Int)
  | callable (func sentinel : Value)
  /-- An iterator of the type `kind` that has ended. -/
  | done (kind : Builtin)
  deriving Repr, Inhabited

/-- A module object: its name, and whether reads of some names and every write gap. -/
structure ModuleObj where
  name : String
  gapped : Array String := #[]
  writesGap : Bool := false
  deriving Repr, Inhabited

/-- The built-in state of an object, whose function payload is an `F`. -/
inductive PayloadG (F : Type) where
  /-- An instance of a user class. -/
  | plain
  /-- A list: its elements, and a counter that moves at every change of its length and at each
  preallocation, where CPython may change the list's `allocated`, which `list.sort` checks. -/
  | list (elems : Array Value) (resizes : Nat)
  | dict (d : DictTable)
  | set (s : SetTable)
  /-- A frozenset, `closed` once built: only an open one takes writes, and only a closed one is read
  as a value (hashed, compared, iterated). -/
  | frozenset (s : SetTable) (closed : Bool)
  /-- The built-in part of an instance of a subclass of `tuple`, `str`, `int`, `float` or
  `bytes`. -/
  | tuple (elems : Array Value)
  | str (s : PyStr)
  | int (i : Int)
  | float (bits : UInt64)
  | bytes (b : Array UInt8)
  | cls (c : ClassObj)
  | func (f : F)
  | native (f : NativeFn)
  | exc (e : ExcState)
  | iter (it : IterState)
  | module (m : ModuleObj)
  | property (fget fset fdel doc : Value)
  | classmethod (f : Value)
  | staticmethod (f : Value)
  | super (thisType obj : Value)
  /-- An object without a dict, whose state the semantics doesn't model yet. -/
  | opaque (tag : String) (state : Array Value)
  /-- The descriptor of slot `index` of the class `owner`. -/
  | member (owner : Value) (name : String) (index : Nat)

instance {F : Type} : Inhabited (PayloadG F) := ⟨.plain⟩

/-- An object whose function payload is an `F`. -/
structure ObjG (F : Type) where
  /-- Its class: a built-in type or a class object. -/
  cls : Value
  /-- Its `__dict__`, a dict object, if it has one. -/
  dict : Option ObjId := none
  /-- The values of its `__slots__` (`undef` while unset), in layout order. -/
  slots : Array Value := #[]
  payload : PayloadG F

instance {F : Type} : Inhabited (ObjG F) := ⟨⟨.none, none, #[], .plain⟩⟩

/-- An object's contents as a rule makes them: no function payload. -/
abbrev ObjData := ObjG Empty

/-- A payload as a rule writes it: no function payload. -/
abbrev PayloadData := PayloadG Empty

/-- An object of the store. -/
abbrev Obj (σ : Type) [Store σ] := ObjG (FuncObj σ)

/-- The payload of an object of the store. -/
abbrev ObjPayload (σ : Type) [Store σ] := PayloadG (FuncObj σ)

/-- A dict payload's table changed by `f`; any other payload as it is.  The table is changed in
place when the payload is not shared. -/
def PayloadG.modDict {F : Type} (f : DictTable → DictTable) : PayloadG F → PayloadG F
  | .dict t => .dict (f t)
  | p => p

/-- A list payload's elements and resize count changed by `f`; any other payload as it is. -/
def PayloadG.modList {F : Type} (f : Array Value → Nat → Array Value × Nat) :
    PayloadG F → PayloadG F
  | .list xs n => let (xs', n') := f xs n; .list xs' n'
  | p => p

/-- A set or frozenset payload's table changed by `f`; any other payload as it is. -/
def PayloadG.modSet {F : Type} (f : SetTable → SetTable) : PayloadG F → PayloadG F
  | .set t => .set (f t)
  | .frozenset t c => .frozenset (f t) c
  | p => p

/-- A payload with an empty function payload, as one with any. -/
def PayloadG.lift {F : Type} : PayloadData → PayloadG F
  | .plain => .plain
  | .list e n => .list e n
  | .dict d => .dict d
  | .set s => .set s
  | .frozenset s c => .frozenset s c
  | .tuple e => .tuple e
  | .str s => .str s
  | .int i => .int i
  | .float b => .float b
  | .bytes b => .bytes b
  | .cls c => .cls c
  | .func f => nomatch f
  | .native f => .native f
  | .exc e => .exc e
  | .iter it => .iter it
  | .module m => .module m
  | .property a b c d => .property a b c d
  | .classmethod f => .classmethod f
  | .staticmethod f => .staticmethod f
  | .super t o => .super t o
  | .opaque t s => .opaque t s
  | .member o n i => .member o n i

/-- A payload as a rule sees it: a function payload is seen as `none`. -/
def PayloadG.data? {F : Type} : PayloadG F → Option PayloadData
  | .plain => some .plain
  | .list e n => some (.list e n)
  | .dict d => some (.dict d)
  | .set s => some (.set s)
  | .frozenset s c => some (.frozenset s c)
  | .tuple e => some (.tuple e)
  | .str s => some (.str s)
  | .int i => some (.int i)
  | .float b => some (.float b)
  | .bytes b => some (.bytes b)
  | .cls c => some (.cls c)
  | .func _ => none
  | .native f => some (.native f)
  | .exc e => some (.exc e)
  | .iter it => some (.iter it)
  | .module m => some (.module m)
  | .property a b c d => some (.property a b c d)
  | .classmethod f => some (.classmethod f)
  | .staticmethod f => some (.staticmethod f)
  | .super t o => some (.super t o)
  | .opaque t s => some (.opaque t s)
  | .member o n i => some (.member o n i)

/-- An object with an empty function payload, as one with any. -/
def ObjG.lift {F : Type} (o : ObjData) : ObjG F := { o with payload := o.payload.lift }

/-- The objects, by id. -/
structure ObjStore (σ : Type) [Store σ] where
  objs : Array (Obj σ) := #[]

instance {σ : Type} [Store σ] : Inhabited (ObjStore σ) := ⟨{}⟩

namespace ObjStore
variable {σ : Type} [Store σ]

/-- The number of objects. -/
def size (s : ObjStore σ) : Nat := s.objs.size

/-- The object `id`, if it exists. -/
def get? (s : ObjStore σ) (id : ObjId) : Option (Obj σ) := s.objs[id]?

/-- The store with a new object `o`, and its id. -/
def alloc (s : ObjStore σ) (o : Obj σ) : ObjStore σ × ObjId :=
  -- The id is read before the push, so that the push changes the array in place.
  let id := s.objs.size
  (⟨s.objs.push o⟩, id)

/-- The store with the object `id` changed by `f`; unchanged if there is no such object. -/
def update (s : ObjStore σ) (id : ObjId) (f : Obj σ → Obj σ) : ObjStore σ :=
  ⟨s.objs.modify id f⟩

end ObjStore

end

end StrataPython.Dyn.Sem
