/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Dunders
public import StrataPython.Dyn.Sem.Proto.Attrs
public import StrataPython.Dyn.Sem.Builtins.Classes
public import StrataPython.Dyn.Sem.Proto.Repr
public import StrataPython.Dyn.Sem.Modules.Names
public import StrataPython.Dyn.Sem.DictLookup

set_option autoImplicit false

/-!
# What the models of library modules share

The models of library modules port CPython's code to the record of primitives. This file holds
what they share:

* `lookupAttr?`, CPython's `_PyObject_LookupAttr`: an attribute read whose `AttributeError` means
  "none";
* the store classes that these models make, once per run (`modelClass`), with their methods as
  native functions, and the receiver of such a method (`nativeRecv`).
-/

namespace StrataPython.Dyn.Sem.Modules

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- **`_PyObject_LookupAttr(v, name)`**: the attribute, or `none` when reading it raises
`AttributeError`; any other exception propagates. -/
def lookupAttr? [PyCalls m V] (v : V) (name : String) : m (Option V) :=
  tryCatch (some <$> getAttrRaw v name) fun x => do
    if ← isAttributeError x then pure none else throw x

/-- The object `name` of the model's module `mod`, which a port reads from the module's globals;
the module exists, since an object of it exists. -/
def modelGlobal [PyReads m V] (mod name : String) : m V := do
  let some md ← PyReads.moduleGet mod | PyPure.modelInvariant s!"an object of {mod} before {mod}"
  let some (.module _ _ _ (.made attrs)) ← PyReads.objView md |
    PyPure.modelInvariant s!"{mod} is not a module that a piece made"
  let some (_, v) := attrs.find? (·.1 == name) | PyPure.modelInvariant s!"{mod} has no {name}"
  pure v

/-- The class that `type()` gives for a native function of the kind `k`. -/
def nativeClass : NativeKind → Builtin
  | .function => .function
  | .wrapperDescriptor => .wrapper_descriptor
  | .methodWrapper => .«method-wrapper»
  | .builtinFunctionOrMethod => .builtin_function_or_method
  | .methodDescriptor => .method_descriptor

/-- A new native function: its body is the assembly's native body of `key`. -/
def allocNative [PyPure m V] (nd : NativeData V) : m V :=
  PyPure.allocObj (PyPure.imm (m := m) (.builtin (nativeClass nd.kind))) (.native nd)

/-- The receiver and the arguments of a call of a native method `fn`: a bound one
(`method-wrapper`, `builtin_function_or_method`) captured its receiver last; an unbound one takes it
as its first argument, and without one raises CPython's `TypeError`. -/
def nativeRecv [PyReads m V] (fn args : V) : m (V × V) := do
  let some (.native nf) ← PyReads.objView fn |
    PyPure.modelInvariant "a native method's body called without its native"
  match nf.kind with
  | .methodWrapper | .builtinFunctionOrMethod =>
    let some r := nf.captured.back? | PyPure.modelInvariant "a bound native without its receiver"
    pure (r, args)
  | _ =>
    let xs ← tupleItems args
    let some r := xs[0]? |
      if nf.kind == .methodDescriptor then
        raiseBuiltin "TypeError" s!"unbound method {nf.qualname}() needs an argument"
      else
        raiseBuiltin "TypeError" s!"descriptor '{nf.name}' of '{← ownerName nf}' object needs an argument"
    pure (r, PyPure.imm (m := m) (.tuple (xs.extract 1 xs.size)))
where
  ownerName (nf : NativeData V) : m String := do
    match nf.owner with
    | some o => tpNameOf o
    | none => pure nf.qualname

/-- An entry of a model's class namespace. -/
inductive Entry where
  /-- A method with the native body `key`, of the native kind `kind`. -/
  | native (name key : String) (kind : NativeKind)
  /-- A Python function of the model (a native of kind `function`) that keeps a cache: it captures
  a new empty list. -/
  | cached (name key : String)
  /-- A `staticmethod` of a Python function of the model. -/
  | staticNative (name key : String)
  | str (name text : String)
  | none (name : String)
  /-- A tuple of `str`s, such as `__slots__`. -/
  | strs (name : String) (items : Array String)
  /-- The member descriptor of the class's own slot `name`. -/
  | slot (name : String)
  /-- A built-in constant, such as the class `dict`. -/
  | builtin (name : String) (b : Builtin)
  /-- The value of the entry `other`, made before this one: one object under two names. -/
  | sameAs (name other : String)

/-- The name that an entry binds. -/
def Entry.name : Entry → String
  | .native n _ _ | .cached n _ | .staticNative n _ | .str n _ | .none n | .strs n _ | .slot n
  | .builtin n _ | .sameAs n _ => n

/-- How a model describes one of its classes: CPython's names, its flags, the native methods and
values of its namespace, the names of its own slots in the order of their members, and the names
of its `vars()` that the model doesn't hold, whose lookup stops with a gap. -/
structure ClassSpec where
  name : String
  qualname : String
  «module» : String
  tpName : Option String := none
  immutable : Bool := false
  writesGap : Bool := false
  instanceWritesGap : Bool := false
  instanceDict : Bool := false
  asBase : BaseRule := .allowed
  cType : Bool := false
  slots : Array String := #[]
  entries : Array Entry
  gapped : Array String := #[]

/-- Every name of the class's `vars()`: those its namespace holds, and those whose lookup stops
with a gap. -/
def ClassSpec.names (spec : ClassSpec) : List String :=
  spec.entries.toList.map (·.name) ++ spec.gapped.toList

/-- `body` one Python frame deeper: the frame of a Python function of the ported module that the
port runs without a native of its own.  These frames, and the `withPyDepth`s of the ports, are
CPython's frames below the program code that a native calls back into (a default's `__repr__`, a
`default_factory`, a `__post_init__`, an iterator's `__next__`, an operand's own method), which so
runs at CPython's depth with no margin: each such path has a test in `sem_modules/gap_depth_*.py` at
the depth where CPython raises with 100 frames below the program, and removing one of
these frames makes that test fail (`replace`'s frame is one more than CPython's). -/
def pyFrame [PyReads m V] {α : Type} (body : m α) : m α := PyReads.withPyDepth 1 body

/-- The body of a native that stands for a Python function: CPython's call into Python from C
costs two C levels (`_PyEval_EvalFrame` and the call's vectorcall). P1's call of a native of kind
`function` counts one more level, so a call through P1's `callN` counts three, and a deep run
stops before CPython's `RecursionError`, never after it. -/
def pyFunctionCall [PyReads m V] {α : Type} (body : m α) : m α := PyReads.withDepth 2 body

/-- The Python frames above its caller that a call of a native of these modules must have room for
below the 900-frame limit, checked at the native's entry: at least the deepest that CPython 3.12
pushes inside one call of one of them on arguments that aren't nested (14, for `dataclass` on a
class with a `typing` annotation), with room for the natives that weren't measured.  The frames
that grow with nested arguments (the hashes and reprs of nested aliases) are charged by the ports
where they run them.  It's a check only: it returns before the body runs. -/
def nativePeakFrames : Nat := 32

/-- The methods that recurse through their operands' own methods: a dataclass's generated `__eq__`,
`__hash__`, `__repr__` and order methods, the `__eq__`, `__hash__` and `__repr__` of the generic and
union aliases, and a named tuple's `__repr__`.  Inside one call, CPython pushes only the frames that
their call already charges (1, or 2 for a `__repr__` that `dataclasses._recursive_repr` wraps)
before the operands' methods run, so they skip the entry check, which would stop a call of them
within `nativePeakFrames` frames of the limit where CPython runs it (`dataclass_eq_near_limit`). -/
def perLevelMethods : List String :=
  [generatedEqKey, generatedHashKey, "dataclasses.__repr__", "dataclasses.__lt__", "dataclasses.__le__",
    "dataclasses.__gt__", "dataclasses.__ge__",
    "typing._GenericAlias.__eq__", "typing._GenericAlias.__hash__", "typing._GenericAlias.__repr__",
    "typing._UnionGenericAlias.__eq__", "typing._UnionGenericAlias.__hash__",
    "typing._UnionGenericAlias.__repr__", "collections.namedtuple.__repr__"]

/-- **The body of the native `key`**, after a check, unless `key` is one of `perLevelMethods`,
that `nativePeakFrames` more Python frames fit below the limit, since CPython runs the native as
Python code with frames of its own.  The program code that the body calls back into is at least at
CPython's depth already: the frames that the body charges on its way there (its call's own frame,
and the `pyFrame`s and `withPyDepth`s of its helpers) are CPython's frames below that code. -/
def nativeFrames [PyReads m V] {α : Type} (key : String) (body : m α) : m α := do
  if !perLevelMethods.contains key then PyReads.withPyDepth nativePeakFrames (pure ())
  body

/-- The value that the name `name` of `dir(builtins)` is bound to at the start of a run. -/
def builtinOriginal? (name : String) : Option (Imm V) :=
  match name with
  | "None" => some .none
  | "True" | "__debug__" => some (.bool true)
  | "False" => some (.bool false)
  | "Ellipsis" => some .ellipsis
  | "NotImplemented" => some .notImplemented
  | _ => match Builtin.ofName? name with
    | some b => some (.builtin b)
    | none => (Builtin.strNames.lookup name).map fun t => .str (.ofString t)

/-- Whether the builtin `name` is still bound to its value at the start of the run. -/
def builtinUnchanged [PyReads m V] (name : String) : m Bool := do
  let some v ← PyReads.builtinGet name | return false
  let some o := builtinOriginal? (V := V) name | return false
  match o, ← PyPure.immView v with
  | .str t, some (.str s) => return s == t
  | .builtin b, some (.builtin b') => return b == b'
  | .none, some .none | .ellipsis, some .ellipsis | .notImplemented, some .notImplemented =>
    return true
  | .bool b, some (.bool b') => return b == b'
  | _, _ => return false

/-- A gap unless the builtin `name` is unchanged: a port looks it up in its module's globals,
which fall back to the builtins, and would run the program's own binding. -/
def useBuiltin [PyReads m V] (name : String) : m Unit := do
  if !(← builtinUnchanged name) then
    PyPure.gap s!"a use of builtins.{name} by a model after the program changed it"

/-- `raise cls(msg)` of the builtin exception class `cls`, which a port looks up in its globals. -/
def raiseT [PyReads m V] {α : Type} (cls msg : String) : m α := do
  useBuiltin cls
  raiseBuiltin cls msg

/-- Whether the builtins dict holds exactly the names of `dir(builtins)`, each unchanged: the
modules that an import loads use them too. -/
def builtinsUnchanged [PyReads m V] : m Bool := do
  let some mod ← PyReads.moduleGet "builtins" | return false
  let some d ← PyReads.objDict mod | return false
  if (← PyReads.dictLen d) != Builtin.dictNames.size then return false
  Builtin.dictNames.allM builtinUnchanged

/-- `_PyStack_UnpackDict`'s check of the keywords: one that is not a `str` raises CPython's
`TypeError`, and one that is an object (a `str` subclass's instance, or another object) stops with
a gap. -/
def keywordsCheck [PyReads m V] (kwargs : V) : m Unit := do
  for (k, _, _) in ← PyReads.dictEntries kwargs do
    match ← PyPure.immView k with
    | some (.str _) => pure ()
    | some _ => raiseBuiltin "TypeError" "keywords must be strings"
    | none => PyPure.gap "a keyword that is not an exact str"

/-- The arguments of a call of the Python function `qualname` of the model, bound to its
parameters `names` (none with a default), with `*args` (`varPos`) and `**kwargs` (`varKw`) after
them, as CPython binds them, with its `TypeError`s. -/
def bindPy [PyReads m V] [PyNew m V] (qualname : String) (names : Array String) (args kwargs : V)
    (varPos varKw : Bool := false) : m (Array V) := do
  keywordsCheck kwargs
  let r ← bindArgs qualname args kwargs (PyPure.imm (m := m) (.tuple #[])) 0 names.size varPos varKw
    names
  tupleItems r

/-- **The arguments of a call of the Python function `qualname`** bound to its parameters
`names`, as CPython 3.12's `initialize_locals` binds them, with its `TypeError`s in its order:
the first `nPosOnly` names are positional-only, the first `nPos` positional, the others
keyword-only; `defaults` gives each name's default or `none`. The result holds one value per name,
then the extra positional arguments if `varPos`, then a new dict of the other keywords if `varKw`.
Keywords are `keywordsCheck`ed first. -/
def bindPyFull [PyReads m V] [PyNew m V] (qualname : String) (names : Array String)
    (defaults : Array (Option V)) (nPosOnly nPos : Nat) (args kwargs : V)
    (varPos varKw : Bool := false) : m (Array V) := do
  let fail {α : Type} (msg : String) : m α := raiseBuiltin "TypeError" s!"{qualname}() {msg}"
  keywordsCheck kwargs
  let xs ← tupleItems args
  let mut slots : Array (Option V) := Array.replicate names.size none
  let n := min xs.size nPos
  for i in [:n] do
    slots := slots.set! i xs[i]?
  let mut rest : Array (String × V) := #[]
  for (k, v, _) in ← PyReads.dictEntries kwargs do
    let some (.str ks) ← PyPure.immView k | PyPure.modelInvariant "a keyword that keywordsCheck let pass"
    let s := ks.s
    match (names.extract nPosOnly names.size).findIdx? (· == s) with
    | some j =>
      if slots[nPosOnly + j]!.isSome then fail s!"got multiple values for argument '{s}'"
      slots := slots.set! (nPosOnly + j) (some v)
    | none =>
      if !varKw then
        -- `positional_only_passed_as_keyword`: the positional-only parameters, in their order,
        -- that any keyword names.
        let mut given : Array String := #[]
        for (k', _, _) in ← PyReads.dictEntries kwargs do
          if let some (.str ks') ← PyPure.immView k' then given := given.push ks'.s
        let posOnly := (names.extract 0 nPosOnly).filter given.contains
        if !posOnly.isEmpty then
          fail s!"got some positional-only arguments passed as keyword arguments: '{", ".intercalate posOnly.toList}'"
        fail s!"got an unexpected keyword argument '{s}'"
      rest := rest.push (s, v)
  let defcount := ((defaults.extract 0 nPos).filter (·.isSome)).size
  let isKwonly (i : Nat) := nPos ≤ i
  if xs.size > nPos && !varPos then
    let kwonlyGiven := (slots.zipIdx.filter fun (x, i) => isKwonly i && x.isSome).size
    let given := xs.size
    let (sig, pl) := if defcount > 0 then (s!"from {nPos - defcount} to {nPos}", true)
      else (s!"{nPos}", nPos != 1)
    let kwSig := if kwonlyGiven > 0 then
        s!" positional argument{pluralS given} (and {kwonlyGiven} keyword-only argument{pluralS kwonlyGiven})"
      else ""
    fail s!"takes {sig} positional argument{if pl then "s" else ""} but {given}{kwSig} {if given == 1 && kwonlyGiven == 0 then "was" else "were"} given"
  let mRequired := nPos - defcount
  let missingPos := (names.zipIdx.filter fun (_, i) => i < mRequired && slots[i]!.isNone).map (·.1)
  if !missingPos.isEmpty then
    fail s!"missing {missingPos.size} required positional argument{pluralS missingPos.size}: {missingList missingPos}"
  let mut missingKw : Array String := #[]
  for (nm, i) in names.zipIdx do
    if slots[i]!.isNone then
      match defaults[i]?.join with
      | some d => slots := slots.set! i (some d)
      | none => if isKwonly i then missingKw := missingKw.push nm
  if !missingKw.isEmpty then
    fail s!"missing {missingKw.size} required keyword-only argument{pluralS missingKw.size}: {missingList missingKw}"
  let mut out : Array V := #[]
  for x in slots do
    let some v := x | PyPure.modelInvariant "a parameter without a value"
    out := out.push v
  if varPos then out := out.push (PyPure.imm (m := m) (.tuple (xs.extract nPos xs.size)))
  if varKw then
    let d ← PyPure.allocDict
    for (k, v) in rest do
      PyNew.dictSetNew d (PyPure.imm (m := m) (.str (.ofString k))) v none fun _ => pure false
    out := out.push d
  return out

/-- The arguments of a call of the Python function `qualname`, whose positional-or-keyword
parameters are `names`, the last of them with the defaults `defaults` (`bindPyFull`). -/
def bindPyDefaults [PyReads m V] [PyNew m V] (qualname : String) (names defaults : Array V)
    (args kwargs : V) : m (Array V) := do
  let mut texts : Array String := #[]
  for nm in names do
    let some t ← str? nm | PyPure.modelInvariant "a parameter name that is not a str"
    texts := texts.push t
  let dfl := Array.replicate (texts.size - defaults.size) none ++ defaults.map some
  bindPyFull qualname texts dfl 0 texts.size args kwargs

/-- **`setattr(cls, name, v)`** on a class `cls` of `type` that a port made, for the names whose
setter is one of `type`'s getsets: `__module__` and `__doc__` write the class's namespace, and
`__qualname__` sets the class's qualified name, as `type_set_module`, `type_set_doc` and
`type_set_qualname` do; any other name is the generic write. -/
def setOnClass [PyWrites m V] (cls : V) (name : String) (v : V) : m Unit := do
  let some cd ← classData? cls | PyPure.modelInvariant "a port's class that is no class"
  match name with
  | "__module__" | "__doc__" =>
    PyWrites.dictSet cd.ns (strValue (m := m) name) v none fun _ => pure false
  | "__qualname__" =>
    let some q ← str? v |
      raiseBuiltin "TypeError" s!"can only assign string to {cd.name}.__qualname__, not '{← typeName v}'"
    PyWrites.classSetName cls cd.name q
  | _ => setAttr cls name (some v)

/-- The name of the module of the module table that keeps the model's class `qualname` of the
module `mod`, one object per run. No import statement can spell it, so no program reaches the
module itself. A rule that reads the module table by a name that a program gives (a future
`sys.modules` or `__import__`) must skip the names that start with `<`. -/
def modelClassModule (mod qualname : String) : String := s!"<the model's class {mod}.{qualname}>"

/-- The model's class of `spec` in this run, if it was made already. -/
def modelClass? [PyReads m V] (spec : ClassSpec) : m (Option V) := do
  let some mod ← PyReads.moduleGet (modelClassModule spec.module spec.qualname) | return none
  match ← PyReads.objView mod with
  | some (.module _ _ _ (.made attrs)) =>
    if let some (_, c) := attrs.find? (·.1 == "class") then return some c
    PyPure.modelInvariant s!"the module of the model's class {spec.qualname} has no class"
  | _ => PyPure.modelInvariant s!"the module of the model's class {spec.qualname} is not a module"

/-- The class that `spec` describes, with the metaclass `mcls` and the bases `bases`, made at its
first use in a run, with its methods as native functions: later uses get the same object, which a
module of the module table keeps. Its MRO is C3's over `bases`. -/
def modelClassWith [PyWrites m V] [PyNew m V] (spec : ClassSpec) (mcls : V) (bases : Array V) :
    m V := do
  if let some c ← modelClass? spec then return c
  let key := modelClassModule spec.module spec.qualname
  let ns ← PyPure.allocDict
  let tail ← c3Tail bases
  let solid ← if !spec.slots.isEmpty then pure (PyPure.imm (m := m) .none)
    else match bases[0]? with
      | some b => solidBaseOf b
      | none => PyPure.modelInvariant s!"the model's class {spec.qualname} without a base"
  let c ← PyPure.allocObj mcls <| .cls
    { name := spec.name, qualname := spec.qualname, «module» := spec.module, bases,
      mroTail := tail, ns, solidBase := solid, instanceDict := spec.instanceDict,
      slots := spec.slots, immutable := spec.immutable, gapped := spec.gapped,
      writesGap := spec.writesGap, instanceWritesGap := spec.instanceWritesGap,
      tpName := spec.tpName, asBase := spec.asBase, cType := spec.cType }
  -- The namespace is filled after the class exists, so that each method knows its owner. The
  -- members of the class's own slots follow the slots of the classes after it in the MRO.
  let offset ← slotCountOf tail.toList
  let fnData (name k : String) (captured : Array V) : NativeData V :=
    { key := k, kind := .function, captured, name, qualname := spec.qualname ++ "." ++ name,
      «module» := spec.module }
  for e in spec.entries do
    let v ← match e with
      | .native name k kind =>
        let nd : NativeData V :=
          { key := k, kind := kind, name := name, qualname := spec.qualname ++ "." ++ name,
            «module» := spec.module, owner := some c }
        allocNative nd
      | .cached name k => do
        -- `functools.wraps` gives CPython's wrapper a `__dict__`; its names stop with a gap.
        let gapped := ((functionNames.lookup k).getD []).toArray
        allocNative { fnData name k #[← PyPure.allocList #[]] with gapped }
      | .staticNative name k => do
        let f ← allocNative (fnData name k #[])
        PyPure.allocObj (PyPure.imm (m := m) (.builtin .staticmethod)) (.staticmethod (some f))
      | .str _ text => pure (PyPure.imm (m := m) (.str (.ofString text)))
      | .none _ => pure (PyPure.imm (m := m) .none)
      | .strs _ items =>
        pure (PyPure.imm (m := m) (.tuple (items.map fun t => PyPure.imm (m := m) (.str (.ofString t)))))
      | .slot name =>
        match spec.slots.idxOf? name with
        | some i =>
          PyPure.allocObj (PyPure.imm (m := m) (.builtin .member_descriptor)) (.member c name (offset + i))
        | none => PyPure.modelInvariant s!"the model's class {spec.qualname} has no slot {name}"
      | .builtin _ b => pure (PyPure.imm (m := m) (.builtin b))
      | .sameAs _ other => do
        let some v ← dictFindStr ns other |
          PyPure.modelInvariant s!"the model's class {spec.qualname} has no {other} yet"
        pure v
    PyNew.dictSetNew ns (strKey (m := m) e.name) v none fun _ => pure false
  let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
    (.module key #[] true #[("class", c)])
  PyReads.moduleAdd key mod
  pure c

/-- The class that `spec` describes, a class of `type` with the base `object` (`modelClassWith`). -/
def modelClass [PyWrites m V] [PyNew m V] (spec : ClassSpec) : m V :=
  modelClassWith spec (PyPure.imm (m := m) (.builtin .type)) #[PyPure.imm (m := m) (.builtin .object)]

end

end

end StrataPython.Dyn.Sem.Modules
