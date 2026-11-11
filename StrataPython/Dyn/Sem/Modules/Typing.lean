/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Types
public import StrataPython.Dyn.Sem.Modules.Namedtuple

set_option autoImplicit false

/-!
# The model of `typing`

A port of the parts of CPython 3.12's `Lib/typing.py` that annotations use: `TYPE_CHECKING`,
`cast`, `overload`, `Any`, the special forms `Optional`, `Union`, `NotRequired`, `Required` and
`TypeGuard`, the aliases `List`, `Dict`, `Set` and `Tuple`, their subscription with its caches, and
`ForwardRef`. Every other name of the module stops with a gap.

The ports follow `typing.py` function by function, through the record's combinators, and count
a Python frame for each Python function that CPython runs (`pyFrame`), so that a nested value
stops with a gap before CPython would raise `RecursionError`. The model's depth stops are gaps and
must stay gaps: the model counts at least CPython's frames, so it may stop where CPython goes on.
A subscription first checks that its arguments are known values (`knownDepth`), whose `==`,
`hash` and attribute reads run no user code; so every object that the model makes holds only known
values, and its own `==`, `hash` and `repr` run no user code either. Before each use of a builtin,
a port checks that the program didn't change it.
-/

namespace StrataPython.Dyn.Sem.Modules

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- `self.name` of a `typing` object, read with the attribute protocol, as `typing.py` reads it. -/
def attrOf [PyCalls m V] (self : V) (name : String) : m V := getAttr self name

/-- The `str` of a value, or a model invariant. -/
def strOf! [PyReads m V] (v : V) : m String := do
  let some s ← str? v | PyPure.modelInvariant "a typing name that is not a str"
  pure s

/-! ## The classes -/

/-- `typing._Final`. -/
def finalCls [PyWrites m V] [PyNew m V] : m V := modelClass finalSpec

/-- `typing._NotIterable`. -/
def notIterableCls [PyWrites m V] [PyNew m V] : m V := modelClass notIterableSpec

/-- The metaclass `type`. -/
def typeV [PyPure m V] : V := PyPure.imm (m := m) (.builtin .type)

/-- `typing._SpecialForm`. -/
def specialFormCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith specialFormSpec (typeV (m := m)) #[← finalCls, ← notIterableCls]

/-- `typing._BaseGenericAlias`. -/
def baseGenericAliasCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith baseGenericAliasSpec (typeV (m := m)) #[← finalCls]

/-- `typing._GenericAlias`. -/
def genericAliasCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith genericAliasSpec (typeV (m := m)) #[← baseGenericAliasCls]

/-- `typing._SpecialGenericAlias`. -/
def specialGenericAliasCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith specialGenericAliasSpec (typeV (m := m)) #[← notIterableCls, ← baseGenericAliasCls]

/-- `typing._TupleType`. -/
def tupleTypeCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith tupleTypeSpec (typeV (m := m)) #[← specialGenericAliasCls]

/-- `typing._UnionGenericAlias`. -/
def unionGenericAliasCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith unionGenericAliasSpec (typeV (m := m)) #[← notIterableCls, ← genericAliasCls]

/-- `typing.ForwardRef`. -/
def forwardRefCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith forwardRefSpec (typeV (m := m)) #[← finalCls]

/-- `typing._AnyMeta`. -/
def anyMetaCls [PyWrites m V] [PyNew m V] : m V :=
  modelClassWith anyMetaSpec (typeV (m := m)) #[typeV (m := m)]

/-- `typing.Any`. -/
def anyCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith anySpec (← anyMetaCls) #[PyPure.imm (m := m) (.builtin .object)]

/-- `typing._TypedDictMeta`. -/
def typedDictMetaCls [PyWrites m V] [PyNew m V] : m V :=
  modelClassWith typedDictMetaSpec (typeV (m := m)) #[typeV (m := m)]

/-- `typing._TypedDict`, made by `type.__new__(_TypedDictMeta, 'TypedDict', (), {})`. -/
def typedDictCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith typedDictSpec (← typedDictMetaCls) #[PyPure.imm (m := m) (.builtin .object)]

/-- `typing.NamedTupleMeta`. -/
def namedTupleMetaCls [PyWrites m V] [PyNew m V] : m V :=
  modelClassWith namedTupleMetaSpec (typeV (m := m)) #[typeV (m := m)]

/-- `typing._NamedTuple`, made by `type.__new__(NamedTupleMeta, 'NamedTuple', (), {})`. -/
def namedTupleCls [PyWrites m V] [PyNew m V] : m V := do
  modelClassWith namedTupleSpec (← namedTupleMetaCls) #[PyPure.imm (m := m) (.builtin .object)]

/-- Whether `v` is an instance of the model's class of `spec` or of a subclass of it, as
`isinstance(v, cls)` is for a class whose metaclass is `type`. -/
def isInstOf [PyReads m V] (v : V) (spec : ClassSpec) : m Bool := do
  let some c ← modelClass? spec | return false
  isSubclass (← PyReads.classOf v) c

/-- **`isinstance(v, cls)`** for the model's class of `spec`, as `typing.py` calls it: the real
class first; then CPython reads `v.__class__`, and a `__class__` that is not the real class stops
with a gap. -/
def isInstOfPy [PyCalls m V] (v : V) (spec : ClassSpec) : m Bool := do
  if ← isInstOf v spec then return true
  if (← PyPure.immView v).isSome then return false
  let some icls ← lookupAttr? v "__class__" | return false
  if (← PyPure.identical icls (← PyReads.classOf v)) == .yes then return false
  PyPure.gap "an isinstance check of typing on a value whose __class__ is not its class"

/-- The name of an attribute hook's call as an exact `str`; any other value stops with a gap, since
`typing.py` hashes it or calls its methods. -/
def hookName [PyReads m V] (v : V) : m String := do
  let some (.str s) ← PyPure.immView v |
    PyPure.gap "a typing attribute hook called with a name that is not a str is not modelled yet"
  pure s.s

/-! ## The module's objects -/


/-- A Python function of the module `typing` with the native body `key`. -/
def typingFunction [PyPure m V] (name qualname key : String) : m V :=
  allocNative { key, kind := .function, name, qualname, «module» := "typing" }

/-- The special form `name`: its slots `__doc__`, `_getitem` (the function that `typing.py`
decorates) and `_name`. -/
def newSpecialForm [PyWrites m V] [PyNew m V] (name : String) : m V := do
  let getitem ← typingFunction name name s!"typing.{name}"
  PyReads.allocInstance (← specialFormCls) .plain #[]
    #[some (strValue (m := m) (genText s!"typing.{name}")), some getitem, some (strValue (m := m) name)]

/-- `_SpecialGenericAlias(origin, nparams, inst=False, name=name)` and `_TupleType`'s: the instance
dict as `__init__` fills it. -/
def newSpecialAlias [PyWrites m V] [PyNew m V] (cls : V) (name : String) (origin : Builtin)
    (nparams : Int) (doc : String) : m V :=
  PyReads.allocInstance cls .plain
    #[("_inst", PyPure.imm (m := m) (.bool false)), ("_name", strValue (m := m) name),
      ("__origin__", PyPure.imm (m := m) (.builtin origin)), ("__slots__", PyPure.imm (m := m) .none),
      ("_nparams", PyPure.imm (m := m) (.int nparams)), ("__doc__", strValue (m := m) doc)] #[]

/-- **`_GenericAlias(origin, args, inst=inst, name=name)`** of the class `cls`, for known `args`:
the instance dict as `__init__` fills it, with `...` for `_TypingEllipsis` (`ellipsis`), the
parameters `()` (no known value holds a type variable), and `__module__` from the origin when the
alias has no name. Each write runs `_BaseGenericAlias.__setattr__` in CPython, which looks up
`super`. -/
def newGenericAlias' [PyWrites m V] [PyNew m V] (cls origin : V) (args : Array V) (inst : Bool)
    (name : Option String) : m V := do
  useBuiltin "super"
  useBuiltin "isinstance"
  useBuiltin "tuple"
  useBuiltin "hasattr"
  useBuiltin "getattr"
  useBuiltin "type"
  -- `__init__`, `super().__init__`, then `__setattr__` and `super().__setattr__`.
  PyReads.withPyDepth 4 do
    let module ← match name with
      | some _ => pure none
      | none => some <$> getAttr origin "__module__"
    let nameV := match name with
      | some n => strValue (m := m) n
      | none => PyPure.imm (m := m) .none
    let base := #[("_inst", PyPure.imm (m := m) (.bool inst)), ("_name", nameV),
      ("__origin__", origin), ("__slots__", PyPure.imm (m := m) .none),
      ("__args__", PyPure.imm (m := m) (.tuple args)), ("__parameters__", PyPure.imm (m := m) (.tuple #[]))]
    let dict := match module with
      | some md => base.push ("__module__", md)
      | none => base
    PyReads.allocInstance cls .plain dict #[]

/-- Whether `x` is a dotted name of ASCII identifiers that are not keywords, which `compile`
accepts as an expression: `some false` for a string that isn't one, `none` when the model can't
tell (a non-ASCII string). -/
def dottedName? (x : String) : Option Bool :=
  if !x.toList.all (·.toNat < 128) then none else
  let parts := x.splitOn "."
  let keywords := ["False", "None", "True", "and", "as", "assert", "async", "await", "break",
    "class", "continue", "def", "del", "elif", "else", "except", "finally", "for", "from", "global",
    "if", "import", "in", "is", "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try",
    "while", "with", "yield"]
  let ident (p : String) : Bool := match p.toList with
    | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')
    | [] => false
  some (parts.all fun p => ident p && !keywords.contains p)

/-- **`ForwardRef(arg, module=module)`**, with `is_class` `False`, for a `str` that `compile`
accepts as a dotted name; any other string stops with a gap, since CPython compiles it and may
raise `SyntaxError`. The slot `__forward_code__` holds no value: CPython's code object is not
modelled. -/
def newForwardRef [PyWrites m V] [PyNew m V] (arg : V) (text : String) (module : V) : m V := do
  useBuiltin "isinstance"
  useBuiltin "compile"
  if dottedName? text != some true then
    PyPure.gap "a ForwardRef of a string that is not a dotted name is not modelled yet"
  PyReads.withPyDepth 1 do
    PyReads.allocInstance (← forwardRefCls) .plain #[]
      #[some arg, none, some (PyPure.imm (m := m) (.bool false)), some (PyPure.imm (m := m) (.bool true)),
        some (PyPure.imm (m := m) (.bool false)), some module, some (PyPure.imm (m := m) .none)]

/-! ## The helpers of `typing.py` -/

/-- **`_type_convert(arg)`**: `NoneType` for `None`, a `ForwardRef` for a `str`. -/
def typeConvert [PyWrites m V] [PyNew m V] (arg : V) (module : V) : m V := pyFrame do
  if (← PyPure.immView arg) matches some .none then
    useBuiltin "type"
    return PyPure.imm (m := m) (.builtin .NoneType)
  useBuiltin "isinstance"
  match ← str? arg with
  | some t => newForwardRef arg t module
  | none => pure arg

/-- **`_type_check(arg, msg)`** for a known `arg`, with `is_argument` true and no special forms
allowed: `Any` passes, a special form and a tuple raise CPython's `TypeError`. -/
def typeCheck [PyWrites m V] [PyNew m V] (arg : V) (msg : String)
    (module : Option V := none) : m V := pyFrame do
  let arg ← typeConvert arg (module.getD (PyPure.imm (m := m) .none))
  -- `isinstance(arg, _GenericAlias) and arg.__origin__ in (Generic, Protocol, ClassVar, Final)`:
  -- none of these is reachable, and the comparisons of known values run no user code.
  if (← PyPure.identical arg (← anyCls)) == .yes then return arg
  if ← isInstOf arg specialFormSpec then
    raiseT "TypeError" s!"Plain {← strTextOf arg} is not valid as type argument"
  useBuiltin "type"
  useBuiltin "tuple"
  if (← PyPure.immView arg) matches some (.tuple _) then
    let r ← reprTextOf arg
    raiseT "TypeError" s!"{msg} Got {String.ofList (r.toList.take 100)}."
  pure arg

/-- `tuple(_type_check(p, msg) for p in params)`, one frame deeper for the generator. -/
def typeCheckAll [PyWrites m V] [PyNew m V] (params : Array V) (msg : String) : m (Array V) :=
  pyFrame (params.mapM (typeCheck · msg))

/-- `x in xs` by `==`, for known values. -/
def containsKnown [PyCalls m V] (xs : Array V) (x : V) : m Bool :=
  xs.anyM fun y => eqBool y x

/-- **`_remove_dups_flatten(parameters)`**: the arguments of unions spliced in, then the duplicates
dropped (`dict.fromkeys`), keeping the first of each; known values have equal hashes when `==`
holds, so a scan with `==` gives the dict's result. -/
def removeDupsFlatten [PyWrites m V] [PyNew m V] (params : Array V) : m (Array V) := pyFrame do
  useBuiltin "isinstance"
  useBuiltin "tuple"
  useBuiltin "dict"
  let mut flat : Array V := #[]
  for p in params do
    if ← isInstOf p unionGenericAliasSpec then
      flat := flat ++ (← tupleItems (← aliasField p "__args__"))
    else if let some a ← unionArgs? p then flat := flat ++ (← tupleItems a)
    else flat := flat.push p
  -- `_deduplicate`, one frame deeper.
  pyFrame do
    let mut out : Array V := #[]
    for p in flat do
      if !(← containsKnown out p) then out := out.push p
    return out

/-- **`_type_repr(obj)`**: `module.qualname` of a class (`qualname` alone for a builtin), `...`,
the items of a tuple in brackets, and `repr` otherwise; `fuel` bounds the nested tuples. -/
def typeRepr [PyCalls m V] : Nat → V → m String
  | 0, _ => PyPure.gap "a typing repr of tuples nested deeper than the model follows"
  | n + 1, obj => pyFrame do
    useBuiltin "isinstance"
    useBuiltin "type"
    if ← isType obj then
      let md ← getAttr obj "__module__"
      let qn ← getAttr obj "__qualname__"
      let mdText ← strOf! md
      if mdText == "builtins" then return ← strOf! qn
      return s!"{mdText}.{← strOf! qn}"
    if (← PyPure.immView obj) matches some .ellipsis then return "..."
    if let some (.tuple xs) ← PyPure.immView obj then
      let ps ← xs.mapM (typeRepr n)
      return "[" ++ ", ".intercalate ps.toList ++ "]"
    reprTextOf obj

/-- `_type_repr(x)`, with the fuel of `compareDepth`. -/
def typeRepr1 [PyCalls m V] (x : V) : m String := typeRepr compareDepth x

/-- The `repr` of `_GenericAlias`: `typing.Name[args]` for an alias with a name, else the origin's
`_type_repr`, and `()` for no arguments. -/
def genericAliasRepr [PyCalls m V] (self : V) : m String := do
  let name ← aliasField self "_name"
  let head ← match ← str? name with
    | some n => if n.isEmpty then typeRepr1 (← aliasField self "__origin__") else pure s!"typing.{n}"
    | none => typeRepr1 (← aliasField self "__origin__")
  let args ← tupleItems (← aliasField self "__args__")
  let body ← if args.isEmpty then pure "()" else do
    let ps ← args.mapM typeRepr1
    pure (", ".intercalate ps.toList)
  return s!"{head}[{body}]"

/-! ## The subscription caches -/

/-- The most entries that `functools.lru_cache` keeps. -/
def cacheSize : Nat := 128

/-- **A fingerprint of a known value** `v`, equal for equal known values, which the cache
compares before it compares keys with `==`, as CPython's dict compares hashes first: built from
the hashes of the leaves (the record's `hash`, and one fixed number for a hash over a store object's
address), the parts of a tuple or an alias in order, and the
arguments of a union in any order, the same for `typing`'s and `types`' unions, which can be
equal. With it come the nesting of `v`, the number of tuples, aliases and unions on the longest
path to a leaf, and the leaves whose hash is over a store object's address: classes, `Any` and
the special forms, whose `==` is `is`. `fuel` bounds the nesting. -/
def fingerprint [PyCalls m V] : Nat → V → m (UInt64 × Nat × Array V)
  | 0, _ => PyPure.gap "a typing cache key nested deeper than the model follows"
  | n + 1, v => do
    let seq (tag : UInt64) (xs : Array V) : m (UInt64 × Nat × Array V) :=
      xs.foldlM (fun (acc, d, ls) x => do
        let (h, e, l) ← fingerprint n x
        return (mixHash acc h, max d (e + 1), ls ++ l)) (tag, 1, #[])
    let set (xs : Array V) : m (UInt64 × Nat × Array V) :=
      xs.foldlM (fun (acc, d, ls) x => do
        let (h, e, l) ← fingerprint n x
        return (acc + h, max d (e + 1), ls ++ l)) (3, 1, #[])
    if let some (.tuple xs) ← PyPure.immView v then return ← seq 1 xs
    if let some (o, a) ← gaParts? v then return ← seq 2 ((← tupleItems a).push o)
    if let some a ← unionArgs? v then return ← set (← tupleItems a)
    match ← typingKind? v with
    | some (.alias false) => seq 4 ((← tupleItems (← aliasField v "__args__")).push (← aliasField v "__origin__"))
    | some (.alias true) => set (← tupleItems (← aliasField v "__args__"))
    | some .forwardRef => seq 5 #[← getAttr v "__forward_arg__", ← getAttr v "__forward_module__"]
    | _ =>
      -- A hash over a store object's address gives one fixed number, so that no stored number
      -- depends on an object id; `==` then tells such keys apart.
      match ← Proto.hash v with
      | .symbolic src =>
        if src.storeAddrFree then return (Hashable.hash (Hash.symbolic src), 0, #[])
        else return (7, 0, #[v])
      | h => return (Hashable.hash h, 0, #[])

/-- Whether `xs` and `ys` may hold the same objects, as many times each, in any order (by `is`).
Two `==` known values have the same address leaves (`fingerprint`), since those compare by `is`
and a union's arguments are free of `==`-duplicates; so keys whose leaves differ are not `==`.
More than 8 leaves count as the same, so that the check stays cheap; `==` decides then. -/
def sameLeaves [PyReads m V] (xs ys : Array V) : m Bool := do
  if xs.size != ys.size then return false
  if xs.size > 8 then return true
  let count (zs : Array V) (x : V) : m Nat :=
    zs.foldlM (fun n z => do return if (← PyPure.identical z x) == .yes then n + 1 else n) 0
  xs.allM fun x => do return (← count xs x) == (← count ys x)

/-- **`_tp_cache`'s wrapper of `body`, called as `f(self, params)`**: the cache of
`Modules/_functoolsmodule.c`'s bounded `lru_cache`, kept in the list `cache` as `(key, result,
fingerprint, leaves, frames, nesting)` entries, most recently used first, after a first item that keeps
the entries' largest frames and nesting, each with the number of entries that reach it. The key `(self, params)` must be
made of known values; CPython's hash of the key costs a Python frame per nested `typing` alias.
Entries are found by the fingerprint, then the address leaves (`sameLeaves`), then `==`, which for known values finds the entry that
CPython's dict finds. A hash that collides with a stored key's makes CPython compare the two, which
the fingerprint skips, so a scan counts the Python frames and the C levels of a comparison with the
deepest stored key, as `unionCmpBody` counts its hashes. A hit moves its entry to the front; a miss
runs `body`, and puts its result in front unless the key came in meanwhile, dropping the last entry
when the cache is full. A `TypeError` from the cached call makes `_tp_cache` run `body` again,
uncached. -/
def cached [PyWrites m V] [PyNew m V] (cache self params : V) (body : m V) : m V := do
  let key := PyPure.imm (m := m) (.tuple #[self, params])
  let some depth ← knownDepth compareDepth #[self, params] |
    PyPure.gap "a typing subscription with arguments that the model doesn't know"
  let int (n : Nat) : V := PyPure.imm (m := m) (.int n)
  let nats (e : V) (n : Nat) : m (Array Nat) := do
    let some (.tuple xs) ← PyPure.immView e | PyPure.modelInvariant "a typing cache entry"
    (xs.extract (xs.size - n) xs.size).mapM fun x => do
      let some (.int i) ← PyPure.immView x | PyPure.modelInvariant "a typing cache entry without its depths"
      pure i.toNat
  -- The bound `#[frames, count, nesting, count]`, with the number of entries at each maximum, and
  -- the entries; an empty list has neither.
  let state : m (Array Nat × Array V) := do
    let some (es, _) ← PyReads.listView cache | PyPure.modelInvariant "a typing cache that is no list"
    match es[0]? with
    | none => pure (#[0, 0, 0, 0], #[])
    | some b => pure (← nats b 4, es.extract 1 es.size)
  let find (st : Array Nat × Array V) (fp : Int) (nesting : Nat) (leaves : Array V) :
      m (Option (Nat × V)) := do
    let (bound, es) := st
    -- A comparison of nested aliases is four C levels per level of nesting (`richCompare`, the
    -- slot call into the alias's `__eq__`, and the compare of its `__args__` tuple and item).
    PyReads.withPyDepth (max (bound.getD 0 0) depth)
      (PyReads.withDepth (4 * max (bound.getD 2 0) nesting) (pure ()))
    for (e, i) in es.zipIdx do
      let some (.tuple #[k, r, f, ls, _, _]) ← PyPure.immView e | PyPure.modelInvariant "a typing cache entry"
      if let some (.int g) ← PyPure.immView f then
        if g == fp then
          let some (.tuple ls) ← PyPure.immView ls | PyPure.modelInvariant "a typing cache entry's leaves"
          if ← sameLeaves leaves ls then
            if ← eqBool k key then return some (i, r)
    return none
  -- A maximum and its count after adding `x`, or after dropping `y`; `none` when the dropped value
  -- was the last at the maximum.
  let add (mx n x : Nat) : Nat × Nat := if x > mx then (x, 1) else if x == mx then (mx, n + 1) else (mx, n)
  let drop (mx n y : Nat) : Option (Nat × Nat) :=
    if y == mx then (if n ≤ 1 then none else some (mx, n - 1)) else some (mx, n)
  let lookup : m V := do
    -- `PyObject_Hash(key)`.
    let (h, nesting, leaves) ← PyReads.withPyDepth depth (fingerprint compareDepth key)
    let fp : Int := h.toNat
    if let some (i, r) ← find (← state) fp nesting leaves then
      let (_, es) ← state
      let some e := es[i]? | PyPure.modelInvariant "a typing cache entry out of range"
      PyWrites.listSplice cache (i + 1) (i + 2) #[]
      PyWrites.listSplice cache 1 1 #[e]
      return r
    let r ← pyFrame body
    let st ← state
    if (← find st fp nesting leaves).isSome then return r
    let (bound, es) := st
    let entry := PyPure.imm (m := m) (.tuple #[key, r, PyPure.imm (m := m) (.int fp),
      PyPure.imm (m := m) (.tuple leaves), int depth, int nesting])
    let full := es.size ≥ cacheSize
    let kept := if full then es.extract 0 (es.size - 1) else es
    let dropped ← if full then
        match es[es.size - 1]? with
        | some last => pure (some (← nats last 2))
        | none => pure none
      else pure none
    -- The maxima of the kept entries: counted down past the dropped entry, or computed again
    -- when it was the last at a maximum.
    let maxOf (j : Nat) : m (Nat × Nat) :=
      kept.foldlM (fun (mx, n) e => do pure (add mx n ((← nats e 2).getD j 0))) (0, 0)
    let side (j : Nat) (mx n : Nat) : m (Nat × Nat) := do
      match dropped with
      | some d => match drop mx n (d.getD j 0) with
        | some p => pure p
        | none => maxOf j
      | none => pure (mx, n)
    let (f, fn) ← side 0 (bound.getD 0 0) (bound.getD 1 0)
    let (c, cn) ← side 1 (bound.getD 2 0) (bound.getD 3 0)
    let (f, fn) := add f fn depth
    let (c, cn) := add c cn nesting
    let header := PyPure.imm (m := m) (.tuple #[int f, int fn, int c, int cn])
    let some (all, _) ← PyReads.listView cache | PyPure.modelInvariant "a typing cache that is no list"
    if full then PyWrites.listSplice cache (all.size - 1) all.size #[]
    PyWrites.listSplice cache 0 (min 1 all.size) #[header, entry]
    return r
  tryCatch lookup fun x => do
    useBuiltin "TypeError"
    if ← isTypeErrorExc x then pyFrame body else throw x

/-- The cache that the native `fn` captured. -/
def cacheOf [PyReads m V] (fn : V) : m V := do
  let some (.native nf) ← PyReads.objView fn | PyPure.modelInvariant "a typing cache without its native"
  let some c := nf.captured[0]? | PyPure.modelInvariant "a typing cache native without its cache"
  pure c

/-! ## Subscription -/

/-- `Union[params]` through the subscription of the model's `Union`. -/
def unionOf [PyWrites m V] [PyNew m V] (params : Array V) : m V := do
  getItem (← modelGlobal "typing" "Union") (PyPure.imm (m := m) (.tuple params))

/-- The parameters of a subscription as a tuple: `parameters` itself or `(parameters,)`. -/
def asParams [PyReads m V] (parameters : V) : m (Array V) := do
  useBuiltin "isinstance"
  useBuiltin "tuple"
  match ← PyPure.immView parameters with
  | some (.tuple xs) => pure xs
  | _ => pure #[parameters]

/-- **`Union(self, parameters)`**: no arguments raise; then each argument checked, the unions
flattened and the duplicates dropped; one argument comes back alone, and two with `NoneType` make
an `Optional`. -/
def unionBody [PyWrites m V] [PyNew m V] (self parameters : V) : m V := do
  if (← PyPure.immView parameters) matches some (.tuple #[]) then
    raiseT "TypeError" "Cannot take a Union of no types."
  let ps ← asParams parameters
  let ps ← typeCheckAll ps "Union[arg, ...]: each arg must be a type."
  let ps ← removeDupsFlatten ps
  useBuiltin "len"
  if let #[p] := ps then return p
  useBuiltin "type"
  let noneT := PyPure.imm (m := m) (.builtin .NoneType)
  let name := if ps.size == 2 && (← containsKnown ps noneT) then some "Optional" else Option.none
  newGenericAlias' (← unionGenericAliasCls) self ps true name

/-- **`Optional(self, parameters)`**: `Union[arg, NoneType]`. -/
def optionalBody [PyWrites m V] [PyNew m V] (self parameters : V) : m V := do
  let arg ← typeCheck parameters s!"{← strTextOf self} requires a single type."
  useBuiltin "type"
  unionOf #[arg, PyPure.imm (m := m) (.builtin .NoneType)]

/-- `Required`, `NotRequired` (`byName`, whose message names `_name`) and `TypeGuard`: an alias of
the form with one checked argument. -/
def singleBody [PyWrites m V] [PyNew m V] (byName : Bool) (self parameters : V) : m V := do
  let msg ← if byName then pure s!"{← strOf! (← attrOf self "_name")} accepts only a single type."
    else pure s!"{← strTextOf self} accepts only single type."
  let item ← typeCheck parameters msg
  newGenericAlias' (← genericAliasCls) self #[item] true none

/-- **`_SpecialGenericAlias.__getitem__(self, params)`**, uncached: each argument checked, the count
checked against `_nparams`, then `copy_with`. -/
def specialGetItem [PyWrites m V] [PyNew m V] (self params : V) : m V := do
  let ps ← asParams params
  let ps ← typeCheckAll ps "Parameters to generic types must be types."
  -- `_check_generic(self, params, self._nparams)`.
  let some (.int n) ← PyPure.immView (← aliasField self "_nparams") |
    PyPure.modelInvariant "a special alias whose _nparams is no int"
  pyFrame do
    useBuiltin "len"
    if n == 0 then raiseT "TypeError" s!"{← strTextOf self} is not a generic class"
    if (ps.size : Int) != n then
      let which := if (ps.size : Int) > n then "many" else "few"
      raiseT "TypeError"
        s!"Too {which} arguments for {← strTextOf self}; actual {ps.size}, expected {n}"
  copyWith self ps
where
  /-- `copy_with`: `_GenericAlias(origin, params, name=_name, inst=_inst)`. -/
  copyWith (self : V) (ps : Array V) : m V := pyFrame do
    let some (.bool inst) ← PyPure.immView (← aliasField self "_inst") |
      PyPure.modelInvariant "a special alias whose _inst is no bool"
    newGenericAlias' (← genericAliasCls) (← aliasField self "__origin__") ps inst
      (← str? (← aliasField self "_name"))

/-- **`_TupleType.__getitem__(self, params)`**, uncached: `Tuple[t, ...]` and `Tuple[t0, t1]`. -/
def tupleGetItem [PyWrites m V] [PyNew m V] (self params : V) : m V := do
  let ps ← asParams params
  useBuiltin "len"
  let last := ps.back?
  let ellipsis ← match last with
    | some x => pure ((← PyPure.immView x) matches some .ellipsis)
    | none => pure false
  let ps ← if ps.size ≥ 2 && ellipsis then do
      let ts ← typeCheckAll ps.pop "Tuple[t, ...]: t must be a type."
      pure (ts.push (PyPure.imm (m := m) .ellipsis))
    else typeCheckAll ps "Tuple[t0, t1, ...]: each t must be a type."
  pyFrame do
    newGenericAlias' (← genericAliasCls) (← aliasField self "__origin__") ps false
      (← str? (← aliasField self "_name"))

/-! ## The methods -/

/-- `issubclass(cls, origin)` for an `origin` that is a known class: by the MRO for a class `cls`;
any other `cls` stops with a gap. -/
def issubclassKnown [PyCalls m V] (cls origin : V) : m Bool := do
  useBuiltin "issubclass"
  if !(← isType cls) then PyPure.gap "issubclass of a value that is not a class is not modelled yet"
  isSubclass cls origin

/-- `issubclass(cls, arg)`, `PyObject_IsSubclass`: for a class `arg` whose metaclass is `type`, the
MRO; else the metaclass's `__subclasscheck__`. -/
def issubclassOf [PyCalls m V] (cls arg : V) : m Bool := do
  if ← isType arg then
    if (← PyPure.identical (← PyReads.classOf arg) (typeV (m := m))) == .yes then
      return ← issubclassKnown cls arg
  let t ← PyReads.classOf arg
  match ← lookupType t "__subclasscheck__" with
  | some f => truthy (← callFound "__subclasscheck__" f arg t #[cls] (← PyPure.allocDict))
  | none => PyPure.gap "issubclass with this second argument is not modelled yet"

/-- **`_BaseGenericAlias.__call__`**: CPython's `TypeError` for an alias that can't be
instantiated, else the origin's call, with `__orig_class__` set on the result, ignoring any
`Exception`. -/
def aliasCall [PyWrites m V] (self args kwargs : V) : m V := do
  let some (.bool inst) ← PyPure.immView (← aliasField self "_inst") |
    PyPure.modelInvariant "an alias whose _inst is no bool"
  let origin ← aliasField self "__origin__"
  if !inst then
    let name ← strOf! (← aliasField self "_name")
    let oname ← strTextOf (← getAttr origin "__name__")
    raiseT "TypeError" s!"Type {name} cannot be instantiated; use {oname}() instead"
  let r ← callN dispatchDepth origin args kwargs
  tryCatch (setAttr r "__orig_class__" (some self)) fun x => do
    useBuiltin "Exception"
    if ← isSubclass (← PyReads.classOf x) (PyPure.imm (m := m) (.builtin .Exception)) then pure ()
    else throw x
  pure r

/-- Whether `attr` is a dunder name. -/
def isDunder (attr : String) : Bool := attr.startsWith "__" && attr.endsWith "__"

/-- **`_BaseGenericAlias.__getattr__`**: the name of the alias for `__name__` and `__qualname__`,
another name that is no dunder read from the origin, else `AttributeError`. -/
def aliasGetattr [PyCalls m V] (self attrV : V) : m V := do
  useBuiltin "getattr"
  useBuiltin "AttributeError"
  let attr ← hookName attrV
  if attr == "__name__" || attr == "__qualname__" then
    let name ← aliasField self "_name"
    if ← truthy name then return name
    return ← getAttr (← aliasField self "__origin__") "__name__"
  if !isDunder attr then return ← getAttr (← aliasField self "__origin__") attr
  PyReads.raiseNew (PyPure.imm (m := m) (.builtin .AttributeError)) #[attrV] #[]

/-- **`_BaseGenericAlias.__setattr__`**: a dunder name or `_name`, `_inst` and `_nparams` go to
`object.__setattr__`, whose write to the alias stops with a gap; any other name is set on the
origin. -/
def aliasSetattr [PyWrites m V] (self attrV val : V) : m V := do
  let attr ← hookName attrV
  if isDunder attr || ["_name", "_inst", "_nparams"].contains attr then
    PyPure.gap "a write to a typing alias is not modelled yet"
  useBuiltin "setattr"
  setAttr (← aliasField self "__origin__") attr (some val)
  pure (PyPure.imm (m := m) .none)

/-- The arguments of a `_UnionGenericAlias` or a `types.UnionType`, if `v` is one. -/
def unionLikeArgs? [PyCalls m V] (v : V) : m (Option (Array V)) := do
  if ← isInstOfPy v unionGenericAliasSpec then return some (← tupleItems (← aliasField v "__args__"))
  if ← isInstOfPy v unionSpec then
    let some a ← unionArgs? v | PyPure.modelInvariant "a UnionType without its arguments"
    return some (← tupleItems a)
  return none

/-- `set(xs) == set(ys)` for known values: each holds the other's members. -/
def sameSets [PyCalls m V] (xs ys : Array V) : m Bool := do
  let xs ← distinctArgs xs
  let ys ← distinctArgs ys
  if xs.size != ys.size then return false
  xs.allM (containsKnown ys)

/-- `hash(frozenset(xs))` for known values. -/
def frozensetHashOf [PyCalls m V] (xs : Array V) : m V := do
  useBuiltin "frozenset"
  useBuiltin "hash"
  let hs ← (← distinctArgs xs).toList.mapM fun x => PyReads.withDepth 1 (Proto.hash x)
  PyPure.hashValue (frozensetHash hs)

/-! ## `TypedDict` -/

/-- **`get_origin(tp)`** for a known `tp`: the origin of an alias or a `GenericAlias`,
`types.UnionType` for a union of it, and `None` otherwise. -/
def getOrigin [PyCalls m V] (tp : V) : m V := pyFrame do
  useBuiltin "isinstance"
  if ← isInstOf tp baseGenericAliasSpec then return ← aliasField tp "__origin__"
  if let some (o, _) ← gaParts? tp then return o
  if (← unionArgs? tp).isSome then return ← PyReads.classOf tp
  return PyPure.imm (m := m) .none

/-- The `str` members of the set `s`, which a `TypedDict` class's keys are. -/
def strMembers [PyReads m V] (s : V) : m (Array String) := do
  if (← anySetLike? s).isNone then
    PyPure.gap "TypedDict keys of a base that are not a set or frozenset are not modelled yet"
  (← setMembers s).unordered.mapM fun (k, _) => do
    let some t ← str? k | PyPure.gap "a TypedDict key that is not a str is not modelled yet"
    pure t

/-- **`frozenset(keys)`** of a new `set` of the `str`s `ks`: the set's copy as a closed frozenset.
Their order depends on the hash seed, as CPython's does. -/
def strFrozenset [PyCalls m V] [PyNew m V] (ks : Array String) : m V := do
  useBuiltin "frozenset"
  let keys ← PyPure.allocSet false true
  for k in ks do
    let kv := strValue (m := m) k
    PyNew.setAddNew keys kv none (keyEq kv)
  PyReads.setCopy keys true

/-- The entry `name` of the namespace of the class `c`, as `c.__dict__.get(name)` reads it. -/
def nsEntry [PyReads m V] (c : V) (name : String) : m (Option V) := do
  let some cd ← classData? c | PyPure.modelInvariant "a TypedDict base that is no class"
  dictFindStr cd.ns name

/-- Whether `c.name` exists, as `hasattr` checks it. -/
def hasAttr [PyCalls m V] (c : V) (name : String) : m Bool := do
  useBuiltin "hasattr"
  return (← lookupAttr? c name).isSome

/-- **`_TypedDictMeta.__new__(cls, name, bases, ns, total)`**: the bases must be `TypedDict` classes;
`type.__new__(_TypedDictMeta, name, (dict,), ns)`, with `__module__ = 'typing'` in a copy of `ns`
that lacks it, as `type.__new__` takes it from typing's globals; then `__orig_bases__`, the
annotations checked and merged with the bases', the required and optional keys, and `__total__`. -/
def typedDictNew [PyWrites m V] [PyNew m V] (name bases ns total : V) : m V := do
  let mcls ← typedDictMetaCls
  let bs ← tupleItems bases
  useBuiltin "type"
  for b in bs do
    if (← PyPure.identical (← PyReads.classOf b) mcls) != .yes then
      raiseT "TypeError" "cannot inherit from both a TypedDict type and a non-TypedDict base class"
  -- `any(issubclass(b, Generic) for b in bases)`: `Generic` is not reachable, and no base is one.
  useBuiltin "any"
  useBuiltin "issubclass"
  useBuiltin "set"
  if !(← isDict ns) then PyPure.gap "a TypedDict namespace that is not a dict is not modelled yet"
  -- `type.__new__` gets a copy with `__module__` when `ns` lacks it; the port reads `ns` itself.
  let nsNew ← if (← dictFindStr ns "__module__").isSome then pure ns else do
    let c ← PyReads.dictCopy ns
    PyWrites.dictSet c (strValue (m := m) "__module__") (strValue (m := m) "typing") none fun _ => pure false
    pure c
  let dictV := PyPure.imm (m := m) (.builtin .dict)
  let tp ← typeNew (typeV (m := m))
    (PyPure.imm (m := m) (.tuple #[mcls, name, PyPure.imm (m := m) (.tuple #[dictV]), nsNew]))
    (← PyPure.allocDict)
  if !(← hasAttr tp "__orig_bases__") then setAttr tp "__orig_bases__" (some bases)
  let own ← match ← dictFindStr ns "__annotations__" with
    | some a => pure a
    | none => PyPure.allocDict
  if !(← isDict own) then PyPure.gap "TypedDict annotations that are not a dict are not modelled yet"
  -- `tp_dict.__module__`, read for each own annotation: the new class's own entry, which runs no
  -- user code when it is an exact `str`.
  let md ← do
    if (← PyReads.dictLen own) == 0 then pure (PyPure.imm (m := m) .none) else
    let some cd ← classData? tp | PyPure.modelInvariant "a TypedDict class that is no class"
    match ← dictFindStr cd.ns "__module__" with
    | some x =>
      if (← PyPure.immView x) matches some (.str _) then pure x
      else PyPure.gap "a TypedDict class whose __module__ is not a str is not modelled yet"
    | none => PyPure.gap "a TypedDict class without __module__ is not modelled yet"
  let msg := "TypedDict('Name', {f0: t0, f1: t1, ...}); each t must be a type"
  let mut ownAnns : Array (String × V) := #[]
  for (k, v, _) in ← PyReads.dictEntries own do
    let some n ← str? k | PyPure.gap "a TypedDict annotation whose name is not a str is not modelled yet"
    if !(← knownArgs compareDepth #[v]) then
      PyPure.gap "a TypedDict annotation that the model doesn't know"
    ownAnns := ownAnns.push (n, ← typeCheck v msg (some md))
  let mut annotations : Array (String × V) := #[]
  let mut required : Array String := #[]
  let mut optional : Array String := #[]
  let put (xs : Array (String × V)) (n : String) (v : V) : Array (String × V) :=
    match xs.findIdx? (·.1 == n) with
    | some i => xs.set! i (n, v)
    | none => xs.push (n, v)
  for b in bs do
    if let some a ← nsEntry b "__annotations__" then
      if !(← isDict a) then PyPure.gap "TypedDict base annotations that are not a dict"
      for (k, v, _) in ← PyReads.dictEntries a do
        let some n ← str? k | PyPure.gap "a TypedDict annotation whose name is not a str is not modelled yet"
        annotations := put annotations n v
    let breq ← match ← nsEntry b "__required_keys__" with
      | some r => strMembers r
      | none => pure #[]
    required := required ++ breq.filter (!required.contains ·)
    optional := optional.filter (!breq.contains ·)
    let bopt ← match ← nsEntry b "__optional_keys__" with
      | some o => strMembers o
      | none => pure #[]
    required := required.filter (!bopt.contains ·)
    optional := optional ++ bopt.filter (!optional.contains ·)
  for (n, v) in ownAnns do annotations := put annotations n v
  let some (.bool totalB) ← PyPure.immView total |
    PyPure.gap "a TypedDict total that is not a bool is not modelled yet"
  for (n, v) in ownAnns do
    let o ← getOrigin v
    let isRequired ←
      if (← PyPure.identical o (← modelGlobal "typing" "Required")) == .yes then pure true
      else if (← PyPure.identical o (← modelGlobal "typing" "NotRequired")) == .yes then pure false
      else pure totalB
    if isRequired then
      if !required.contains n then required := required.push n
      optional := optional.filter (· != n)
    else
      if !optional.contains n then optional := optional.push n
      required := required.filter (· != n)
  let annV ← PyPure.allocDict
  for (n, v) in annotations do
    PyNew.dictSetNew annV (strValue (m := m) n) v none fun _ => pure false
  setAttr tp "__annotations__" (some annV)
  setAttr tp "__required_keys__" (some (← strFrozenset required))
  setAttr tp "__optional_keys__" (some (← strFrozenset optional))
  if !(← hasAttr tp "__total__") then setAttr tp "__total__" (some total)
  pure tp

/-! ## `NamedTuple` -/

/-- **`target in xs`**, `PySequence_Contains`: each item by identity, then `==`. An item before the
match whose `==` could run user code (anything but an immediate or a class whose metaclass is
`type`) stops with a gap. -/
def containsByIdentity [PyCalls m V] (xs : Array V) (target : V) : m Bool := do
  for x in xs do
    if (← PyPure.identical x target) == .yes then return true
    let plain ← do
      if (← PyPure.immView x).isSome then pure true
      else if ← isType x then
        pure ((← PyPure.identical (← PyReads.classOf x) (typeV (m := m))) == .yes)
      else pure false
    if !plain then PyPure.gap "a NamedTuple base check that could run user code is not modelled yet"
  return false

/-- The names that a `NamedTuple` class body may not bind. -/
def namedTupleProhibited : List String :=
  ["__new__", "__init__", "__slots__", "__getnewargs__", "_fields", "_field_defaults", "_make",
    "_replace", "_asdict", "_source"]

/-- **`NamedTupleMeta.__new__(cls, typename, bases, ns)`**: the bases must be `_NamedTuple`; the
fields are the annotations, the ones with a value in `ns` defaults, which no field without one
may follow; `_make_nmtuple` checks each annotation and makes a `collections.namedtuple` class;
then the other names of `ns` are set on it, but no name of `namedTupleProhibited`. -/
def namedTupleNew [PyWrites m V] [PyNew m V] (typename bases ns : V) : m V := do
  let nt ← namedTupleCls
  let bs ← tupleItems bases
  if !(← containsByIdentity bs nt) then
    PyPure.gap "NamedTupleMeta.__new__ without _NamedTuple among the bases is not modelled yet"
  -- `Generic`, the other base allowed, is not reachable.
  for b in bs do
    if (← PyPure.identical b nt) != .yes then
      raiseT "TypeError" "can only inherit from a NamedTuple type and Generic"
  useBuiltin "tuple"
  if !(← isDict ns) then PyPure.gap "a NamedTuple namespace that is not a dict is not modelled yet"
  let some name ← str? typename | PyPure.gap "a NamedTuple name that is not a str is not modelled yet"
  let types ← match ← dictFindStr ns "__annotations__" with
    | some a => pure a
    | none => PyPure.allocDict
  if !(← isDict types) then PyPure.gap "NamedTuple annotations that are not a dict are not modelled yet"
  let mut fields : Array (V × V) := #[]
  let mut defaultNames : Array String := #[]
  for (k, t, _) in ← PyReads.dictEntries types do
    let some (.str fs) ← PyPure.immView k |
      PyPure.gap "a NamedTuple field name that is not a str is not modelled yet"
    if (← dictFindStr ns fs.s).isSome then defaultNames := defaultNames.push fs.s
    else if !defaultNames.isEmpty then
      raiseT "TypeError" (s!"Non-default namedtuple field {fs.s} cannot follow default field" ++
        s!"{if defaultNames.size > 1 then "s" else ""} {", ".intercalate defaultNames.toList}")
    fields := fields.push (k, t)
  let mut defaults : Array V := #[]
  for n in defaultNames do
    let some v ← dictFindStr ns n | PyPure.modelInvariant "a NamedTuple default that went away"
    defaults := defaults.push v
  let some module ← dictFindStr ns "__module__" |
    raiseBuiltin "KeyError" "__module__"
  -- `_make_nmtuple(typename, types.items(), defaults=..., module=...)`.
  let nm ← pyFrame do
    let mut checked : Array (V × V) := #[]
    for (n, t) in fields do
      if !(← knownArgs compareDepth #[t]) then
        PyPure.gap "a NamedTuple annotation that the model doesn't know"
      let some nText ← str? n | PyPure.modelInvariant "a field name that is no str"
      checked := checked.push (n, ← typeCheck t s!"field {nText} annotation must be a type")
    let nm ← namedtuple name (fields.map (·.1)) defaults module
    let anns ← PyPure.allocDict
    for (n, t) in checked do PyNew.dictSetNew anns n t none fun _ => pure false
    -- `nm_tpl.__new__.__annotations__ = types`: the model's functions have no `__annotations__` to
    -- read, so only the class gets them.
    setAttr nm "__annotations__" (some anns)
    pure nm
  -- `nm_tpl.__bases__ = bases`: `(tuple,)` already, unless `_NamedTuple` came more than once.
  if bs.size > 1 then raiseBuiltin "TypeError" "duplicate base class tuple"
  -- The field names' texts, read once, so that the walk below tests membership without a step.
  let fieldNames ← (← tupleItems (← getAttr nm "_fields")).filterMapM str?
  for (k, v, _) in ← PyReads.dictEntries ns do
    let some (.str ks) ← PyPure.immView k |
      PyPure.gap "a NamedTuple namespace name that is not a str is not modelled yet"
    if namedTupleProhibited.contains ks.s then
      raiseT "AttributeError" s!"Cannot overwrite NamedTuple attribute {ks.s}"
    if !["__module__", "__name__", "__annotations__"].contains ks.s then
      if !fieldNames.contains ks.s then
        useBuiltin "setattr"
        setOnClass nm ks.s v
  pure nm

/-- The bodies of the Python functions of the model of `typing`, by native key, over the native
`fn` and its arguments. -/
def typingBody [PyWrites m V] [PyNew m V] (key : String) (fn args kwargs : V) : m V := do
  let k (cls name : String) := typingKey cls name
  let boolV (b : Bool) : V := PyPure.imm (m := m) (.bool b)
  let notImpl := PyPure.imm (m := m) .notImplemented
  -- The arguments bound to the parameters of the method that `key` names, whose qualname is the
  -- key without its module.
  let bound (params : Array String) : m (Array V) :=
    bindPy (key.drop "typing.".length).toString params args kwargs
  let boundVar (params : Array String) : m (Array V) :=
    bindPy (key.drop "typing.".length).toString params args kwargs true true
  let bad {α : Type} : m α := PyPure.modelInvariant "a bound call"
  -- A method called on a value of another class, as an unbound call can do, reads fields that
  -- the value doesn't have, and CPython's code may run user code on it: a gap.
  let cls := ((key.drop "typing.".length).takeWhile (· != '.')).toString
  let selfSpecs : List (String × ClassSpec) :=
    [("_SpecialForm", specialFormSpec), ("_BaseGenericAlias", baseGenericAliasSpec),
      ("_GenericAlias", genericAliasSpec), ("_SpecialGenericAlias", specialGenericAliasSpec),
      ("_TupleType", tupleTypeSpec), ("_UnionGenericAlias", unionGenericAliasSpec),
      ("ForwardRef", forwardRefSpec)]
  if let some spec := selfSpecs.lookup cls then
    match (← tupleItems args)[0]? with
    | some self =>
      if !(← isInstOf self spec) then
        PyPure.gap s!"a call of typing's {cls} method on a value of another class is not modelled yet"
    | none =>
      if (← PyReads.dictLen kwargs) > 0 then
        PyPure.gap s!"a call of typing's {cls} method with its receiver as a keyword is not modelled yet"
  -- `_tp_cache`'s key for keyword arguments is not modelled.
  if key.endsWith ".__getitem__" && (← PyReads.dictLen kwargs) > 0 then
    PyPure.gap "a typing subscription method called with keyword arguments is not modelled yet"
  -- `_SpecialForm`.
  if key == k "_SpecialForm" "__getattr__" then
    let #[self, item] ← bound #["self", "item"] | bad
    useBuiltin "AttributeError"
    match ← hookName item with
    | "__name__" | "__qualname__" => return ← attrOf self "_name"
    | _ => PyReads.raiseNew (PyPure.imm (m := m) (.builtin .AttributeError)) #[item] #[]
  if key == k "_SpecialForm" "__mro_entries__" then
    let #[self, _] ← bound #["self", "bases"] | bad
    raiseT "TypeError" s!"Cannot subclass {← reprTextOf self}"
  if key == k "_SpecialForm" "__repr__" then
    let #[self] ← bound #["self"] | bad
    return strValue (m := m) s!"typing.{← strOf! (← attrOf self "_name")}"
  if key == k "_SpecialForm" "__call__" then
    let xs ← boundVar #["self"]
    let some self := xs[0]? | bad
    raiseT "TypeError" s!"Cannot instantiate {← reprTextOf self}"
  if key == k "_SpecialForm" "__or__" then
    let #[self, other] ← bound #["self", "other"] | bad
    return ← unionOf #[self, other]
  if key == k "_SpecialForm" "__ror__" then
    let #[self, other] ← bound #["self", "other"] | bad
    return ← unionOf #[other, self]
  if key == k "_SpecialForm" "__instancecheck__" then
    let #[self, _] ← bound #["self", "obj"] | bad
    raiseT "TypeError" s!"{← strTextOf self} cannot be used with isinstance()"
  if key == k "_SpecialForm" "__subclasscheck__" then
    let #[self, _] ← bound #["self", "cls"] | bad
    raiseT "TypeError" s!"{← strTextOf self} cannot be used with issubclass()"
  if key == k "_SpecialForm" "__getitem__" then
    -- `_tp_cache`'s `inner(*args, **kwds)` passes the arguments on to `__getitem__(self,
    -- parameters)`.
    let #[self, parameters] ← bound #["self", "parameters"] | bad
    return ← cached (← cacheOf fn) self parameters do
      let getitem ← attrOf self "_getitem"
      callN dispatchDepth getitem (PyPure.imm (m := m) (.tuple #[self, parameters])) (← PyPure.allocDict)
  -- The functions that the special forms decorate.
  for form in specialForms do
    if key == s!"typing.{form}" then
      let #[self, parameters] ← bindPy form #["self", "parameters"] args kwargs | bad
      -- A direct call of the form's function skips the cache and its check of the arguments.
      if !(← isInstOf self specialFormSpec) || !(← knownArgs compareDepth #[parameters]) then
        PyPure.gap s!"a call of typing's {form} function on values that the model doesn't know"
      return ← match form with
        | "Union" => unionBody self parameters
        | "Optional" => optionalBody self parameters
        | "TypeGuard" => singleBody false self parameters
        | _ => singleBody true self parameters
  -- `_BaseGenericAlias`.
  if key == k "_BaseGenericAlias" "__call__" then
    let xs ← boundVar #["self"]
    let #[self, rest, kw] := xs | bad
    return ← aliasCall self rest kw
  if key == k "_BaseGenericAlias" "__getattr__" then
    let #[self, attr] ← bound #["self", "attr"] | bad
    return ← aliasGetattr self attr
  if key == k "_BaseGenericAlias" "__setattr__" then
    let #[self, attr, val] ← bound #["self", "attr", "val"] | bad
    return ← aliasSetattr self attr val
  if key == k "_BaseGenericAlias" "__instancecheck__" then
    let #[self, obj] ← bound #["self", "obj"] | bad
    useBuiltin "type"
    let sc ← getAttr self "__subclasscheck__"
    return ← callN dispatchDepth sc (PyPure.imm (m := m) (.tuple #[← PyReads.classOf obj]))
      (← PyPure.allocDict)
  if key == k "_BaseGenericAlias" "__subclasscheck__" then
    let #[_, _] ← bound #["self", "cls"] | bad
    raiseT "TypeError" "Subscripted generics cannot be used with class and instance checks"
  -- `_GenericAlias`.
  if key == k "_GenericAlias" "__eq__" then
    let #[self, other] ← bound #["self", "other"] | bad
    useBuiltin "isinstance"
    if !(← isInstOfPy other genericAliasSpec) then return notImpl
    let r ← richCompareV .eq (← aliasField self "__origin__") (← aliasField other "__origin__")
    if !(← truthy r) then return r
    return ← richCompareV .eq (← aliasField self "__args__") (← aliasField other "__args__")
  if key == k "_GenericAlias" "__hash__" then
    let #[self] ← bound #["self"] | bad
    useBuiltin "hash"
    let t := PyPure.imm (m := m) (.tuple #[← aliasField self "__origin__", ← aliasField self "__args__"])
    return ← PyPure.hashValue (← Proto.hash t)
  if key == k "_GenericAlias" "__or__" then
    let #[self, right] ← bound #["self", "right"] | bad
    return ← unionOf #[self, right]
  if key == k "_GenericAlias" "__ror__" then
    let #[self, left] ← bound #["self", "left"] | bad
    return ← unionOf #[left, self]
  if key == k "_GenericAlias" "__repr__" then
    let #[self] ← bound #["self"] | bad
    return strValue (m := m) (← genericAliasRepr self)
  -- `_SpecialGenericAlias` and `_TupleType`.
  if key == k "_SpecialGenericAlias" "__getitem__" || key == k "_TupleType" "__getitem__" then
    let cls := if key == k "_TupleType" "__getitem__" then "_TupleType" else "_SpecialGenericAlias"
    let #[self, params] ← bound #["self", "params"] | bad
    return ← cached (← cacheOf fn) self params do
      if cls == "_TupleType" then tupleGetItem self params else specialGetItem self params
  if key == k "_SpecialGenericAlias" "__repr__" then
    let #[self] ← bound #["self"] | bad
    return strValue (m := m) s!"typing.{← strOf! (← aliasField self "_name")}"
  if key == k "_SpecialGenericAlias" "__subclasscheck__" then
    let #[self, cls] ← bound #["self", "cls"] | bad
    useBuiltin "isinstance"
    let origin ← aliasField self "__origin__"
    if ← isInstOfPy cls specialGenericAliasSpec then
      return boolV (← issubclassKnown (← aliasField cls "__origin__") origin)
    if !(← isInstOfPy cls genericAliasSpec) then return boolV (← issubclassKnown cls origin)
    raiseT "TypeError" "Subscripted generics cannot be used with class and instance checks"
  if key == k "_SpecialGenericAlias" "__or__" then
    let #[self, right] ← bound #["self", "right"] | bad
    return ← unionOf #[self, right]
  if key == k "_SpecialGenericAlias" "__ror__" then
    let #[self, left] ← bound #["self", "left"] | bad
    return ← unionOf #[left, self]
  -- `_UnionGenericAlias`.
  if key == k "_UnionGenericAlias" "__eq__" then
    let #[self, other] ← bound #["self", "other"] | bad
    useBuiltin "isinstance"
    let some ys ← unionLikeArgs? other | return notImpl
    useBuiltin "set"
    if !(← knownArgs compareDepth ys) then
      PyPure.gap "comparing unions with arguments that the model doesn't know"
    let xs ← tupleItems (← aliasField self "__args__")
    -- `set(args)` hashes each argument first, a Python frame and `aliasHashLevels` C levels per
    -- nested alias, and returns.
    let some depth ← knownDepth compareDepth (xs ++ ys) |
      PyPure.gap "comparing unions with arguments that the model doesn't know"
    PyReads.withPyDepth depth (PyReads.withDepth (aliasHashLevels * depth) (pure ()))
    return boolV (← sameSets xs ys)
  if key == k "_UnionGenericAlias" "__hash__" then
    let #[self] ← bound #["self"] | bad
    return ← frozensetHashOf (← tupleItems (← aliasField self "__args__"))
  if key == k "_UnionGenericAlias" "__repr__" then
    let #[self] ← bound #["self"] | bad
    let xs ← tupleItems (← aliasField self "__args__")
    let noneT := PyPure.imm (m := m) (.builtin .NoneType)
    useBuiltin "type"
    useBuiltin "len"
    if let #[a, b] := xs then
      if (← PyPure.identical a noneT) == .yes then
        return strValue (m := m) s!"typing.Optional[{← typeRepr1 b}]"
      if (← PyPure.identical b noneT) == .yes then
        return strValue (m := m) s!"typing.Optional[{← typeRepr1 a}]"
    -- `super().__repr__()`.
    useBuiltin "super"
    return strValue (m := m) (← pyFrame (genericAliasRepr self))
  if key == k "_UnionGenericAlias" "__instancecheck__" then
    let #[self, obj] ← bound #["self", "obj"] | bad
    useBuiltin "isinstance"
    for a in ← tupleItems (← aliasField self "__args__") do
      if ← isinstanceN dispatchDepth obj a then return boolV true
    return boolV false
  if key == k "_UnionGenericAlias" "__subclasscheck__" then
    let #[self, cls] ← bound #["self", "cls"] | bad
    useBuiltin "issubclass"
    for a in ← tupleItems (← aliasField self "__args__") do
      if ← issubclassOf cls a then return boolV true
    return boolV false
  -- `ForwardRef`.
  if key == k "ForwardRef" "__eq__" then
    let #[self, other] ← bound #["self", "other"] | bad
    useBuiltin "isinstance"
    if !(← isInstOfPy other forwardRefSpec) then return notImpl
    -- Neither is ever evaluated: `_evaluate` stops with a gap.
    let r ← richCompareV .eq (← attrOf self "__forward_arg__") (← attrOf other "__forward_arg__")
    if !(← truthy r) then return r
    return ← richCompareV .eq (← attrOf self "__forward_module__") (← attrOf other "__forward_module__")
  if key == k "ForwardRef" "__hash__" then
    let #[self] ← bound #["self"] | bad
    useBuiltin "hash"
    let t := PyPure.imm (m := m)
      (.tuple #[← attrOf self "__forward_arg__", ← attrOf self "__forward_module__"])
    return ← PyPure.hashValue (← Proto.hash t)
  if key == k "ForwardRef" "__or__" then
    let #[self, other] ← bound #["self", "other"] | bad
    return ← unionOf #[self, other]
  if key == k "ForwardRef" "__ror__" then
    let #[self, other] ← bound #["self", "other"] | bad
    return ← unionOf #[other, self]
  if key == k "ForwardRef" "__repr__" then
    let #[self] ← bound #["self"] | bad
    let md ← attrOf self "__forward_module__"
    let mdText ← if (← PyPure.immView md) matches some .none then pure ""
      else pure s!", module={← reprTextOf md}"
    return strValue (m := m) s!"ForwardRef({← reprTextOf (← attrOf self "__forward_arg__")}{mdText})"
  -- `_AnyMeta` and `Any`.
  if key == k "_AnyMeta" "__instancecheck__" then
    let #[self, _] ← bound #["self", "obj"] | bad
    if (← PyPure.identical self (← anyCls)) == .yes then
      raiseT "TypeError" "typing.Any cannot be used with isinstance()"
    PyPure.gap "isinstance with a class of typing._AnyMeta other than Any is not modelled yet"
  if key == k "_AnyMeta" "__repr__" then
    let #[self] ← bound #["self"] | bad
    if (← PyPure.identical self (← anyCls)) == .yes then return strValue (m := m) "typing.Any"
    PyPure.gap "the repr of a class of typing._AnyMeta other than Any is not modelled yet"
  if key == k "Any" "__new__" then
    let xs ← boundVar #["cls"]
    let some cls := xs[0]? | bad
    if (← PyPure.identical cls (← anyCls)) == .yes then
      raiseT "TypeError" "Any cannot be instantiated"
    PyPure.gap "a subclass of typing.Any is not modelled yet"
  -- `NamedTuple`.
  if key == k "NamedTupleMeta" "__new__" then
    let #[_, typename, bases, ns] ← bound #["cls", "typename", "bases", "ns"] | bad
    return ← namedTupleNew typename bases ns
  if key == "typing._namedtuple_mro_entries" then
    let #[bases] ← bindPy "_namedtuple_mro_entries" #["bases"] args kwargs | bad
    -- `assert NamedTuple in bases`.
    let nt ← modelGlobal "typing" "NamedTuple"
    let bs ← match ← PyPure.immView bases with
      | some (.tuple bs) => pure bs
      | _ => PyPure.gap "_namedtuple_mro_entries of bases that are not a tuple is not modelled yet"
    if !(← containsByIdentity bs nt) then
      PyPure.gap "_namedtuple_mro_entries without NamedTuple among the bases is not modelled yet"
    return PyPure.imm (m := m) (.tuple #[← modelGlobal "typing" "_NamedTuple"])
  if key == "typing.NamedTuple" then
    -- The functional form finds its module from the calling frame.
    PyPure.gap "the functional form of NamedTuple is not modelled yet"
  -- `TypedDict`.
  if key == k "_TypedDictMeta" "__new__" then
    let xs ← tupleItems args
    let kws ← PyReads.dictEntries kwargs
    let totalKw ← kws.filterMapM fun (k, v, _) => do
      if (← str? k) == some "total" then pure (some v) else pure none
    if kws.size != totalKw.size then
      PyPure.gap "_TypedDictMeta.__new__ with keywords other than total is not modelled yet"
    match xs, totalKw with
    | #[_, name, bases, ns], #[] => return ← typedDictNew name bases ns (boolV true)
    | #[_, name, bases, ns], #[t] => return ← typedDictNew name bases ns t
    | #[_, name, bases, ns, t], #[] => return ← typedDictNew name bases ns t
    | _, _ => PyPure.gap "_TypedDictMeta.__new__ with these arguments is not modelled yet"
  if key == k "_TypedDictMeta" "__subclasscheck__" then
    let #[_, _] ← bound #["cls", "other"] | bad
    raiseT "TypeError" "TypedDict does not support instance and class checks"
  if key == "typing.TypedDict.<lambda>" then
    let #[_] ← bindPy "<lambda>" #["bases"] args kwargs | bad
    return PyPure.imm (m := m) (.tuple #[← modelGlobal "typing" "_TypedDict"])
  if key == "typing.TypedDict" then
    -- The functional form finds its module from the calling frame.
    PyPure.gap "the functional form of TypedDict is not modelled yet"
  -- The module's functions.
  if key == "typing.cast" then
    let #[_, val] ← bindPy "cast" #["typ", "val"] args kwargs | bad
    return val
  if key == "typing.overload" then
    let #[func] ← bindPy "overload" #["func"] args kwargs | bad
    useBuiltin "getattr"
    let f := (← lookupAttr? func "__func__").getD func
    -- The registry, which only `get_overloads` reads, is not kept.
    if !((← PyReads.objView f) matches some (.func ..)) then
      PyPure.gap "overload of a value that is not a function object is not modelled yet"
    -- The registry's keys: a module name that is no `str` or `None` may raise or run user code.
    let md ← getAttr f "__module__"
    if !((← PyPure.immView md) matches some (.str _) | some .none) then
      PyPure.gap "overload of a function whose __module__ is not a str is not modelled yet"
    return ← modelGlobal "typing" "_overload_dummy"
  if key == "typing._overload_dummy" then
    discard <| bindPy "_overload_dummy" #[] args kwargs true true
    useBuiltin "NotImplementedError"
    raiseT "NotImplementedError" ("You should not call an overloaded function. " ++
      "A series of @overload-decorated functions outside a stub module should always be followed " ++
      "by an implementation that is not @overload-ed.")
  PyPure.modelInvariant s!"a typing native without a body: {key}"

/-! ## The module -/

/-- The names that the model's module `typing` binds. -/
def typingAttrNames : List String :=
  ["__name__", "TYPE_CHECKING", "cast", "overload", "_overload_dummy", "Any", "_AnyMeta",
    "ForwardRef", "_Final", "_NotIterable", "_SpecialForm", "_BaseGenericAlias", "_GenericAlias",
    "_SpecialGenericAlias", "_TupleType", "_UnionGenericAlias", "List", "Dict", "Set", "Tuple",
    "TypedDict", "_TypedDict", "_TypedDictMeta", "NamedTuple", "NamedTupleMeta", "_NamedTuple",
    "_namedtuple_mro_entries"] ++
    specialForms

/-- **`import typing`**: the module, made at its first import after a check that the builtins are
unchanged, with every name of CPython's `vars(typing)` that the model doesn't bind as a gap. -/
def importTyping [PyWrites m V] [PyNew m V] (_self _args _kwargs : V) : m V := do
  if !(← builtinsUnchanged) then
    PyPure.gap "an import of typing after the program changed the builtins is not modelled yet"
  let sga ← specialGenericAliasCls
  let mut attrs : Array (String × V) := #[("__name__", strValue (m := m) "typing"),
    ("TYPE_CHECKING", PyPure.imm (m := m) (.bool false)),
    ("cast", ← typingFunction "cast" "cast" "typing.cast"),
    ("overload", ← typingFunction "overload" "overload" "typing.overload"),
    ("_overload_dummy", ← typingFunction "_overload_dummy" "_overload_dummy" "typing._overload_dummy"),
    ("Any", ← anyCls), ("_AnyMeta", ← anyMetaCls), ("ForwardRef", ← forwardRefCls),
    ("_Final", ← finalCls), ("_NotIterable", ← notIterableCls), ("_SpecialForm", ← specialFormCls),
    ("_BaseGenericAlias", ← baseGenericAliasCls), ("_GenericAlias", ← genericAliasCls),
    ("_SpecialGenericAlias", sga), ("_TupleType", ← tupleTypeCls),
    ("_UnionGenericAlias", ← unionGenericAliasCls)]
  for (n, origin, k) in specialAliases do
    attrs := attrs.push (n, ← newSpecialAlias sga n origin k s!"A generic version of {origin.info.name}.")
  attrs := attrs.push ("Tuple", ← newSpecialAlias (← tupleTypeCls) "Tuple" .tuple (-1) (genText "typing.Tuple"))
  for f in specialForms do
    attrs := attrs.push (f, ← newSpecialForm f)
  -- `TypedDict` is a function whose `__dict__` holds `__mro_entries__`.
  let td ← typingFunction "TypedDict" "TypedDict" "typing.TypedDict"
  let tdDict ← PyWrites.objEnsureDict td
  PyWrites.dictSet tdDict (strValue (m := m) "__mro_entries__")
    (← typingFunction "<lambda>" "<lambda>" "typing.TypedDict.<lambda>") none fun _ => pure false
  attrs := attrs ++ #[("TypedDict", td), ("_TypedDict", ← typedDictCls), ("_TypedDictMeta", ← typedDictMetaCls)]
  -- `NamedTuple` is a function whose `__dict__` holds `__mro_entries__`, typing's
  -- `_namedtuple_mro_entries`.
  let ntf ← typingFunction "NamedTuple" "NamedTuple" "typing.NamedTuple"
  let me ← typingFunction "_namedtuple_mro_entries" "_namedtuple_mro_entries" "typing._namedtuple_mro_entries"
  PyWrites.dictSet (← PyWrites.objEnsureDict ntf) (strValue (m := m) "__mro_entries__") me none fun _ => pure false
  attrs := attrs ++ #[("NamedTuple", ntf), ("NamedTupleMeta", ← namedTupleMetaCls),
    ("_NamedTuple", ← namedTupleCls), ("_namedtuple_mro_entries", me)]
  let gapped := ((moduleNames.lookup "typing").getD []).toArray.filter (!typingAttrNames.contains ·)
  let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module)) (.module "typing" gapped true attrs)
  PyReads.moduleAdd "typing" mod
  pure mod

end

/-- The C levels that CPython's `__hash__` and `__repr__` of a `typing` class cost on top of the
call into Python and of what the model's `hash` and `repr` of their parts count: with them, the hash
of a nested alias counts CPython's 3 C levels per level, and its `repr` CPython's 4 (measured with
the Python recursion limit raised). -/
def slotExtraLevels (key : String) : Nat :=
  if key.endsWith ".__hash__" || key.endsWith ".__repr__" then 1 else 0

/-- The native bodies of the model of `typing`, each counted as a call into Python. -/
def typingNative (key : String) : Option BuiltinImpl :=
  if key.startsWith "typing." then
    some fun {_} {_} [_] [_] fn args kwargs =>
      pyFunctionCall (PyReads.withDepth (slotExtraLevels key) (typingBody key fn args kwargs))
  else namedtupleNative key

/-- **The rules of `typing`**: its import and the bodies of its Python functions. -/
def typingImpls : Impls where
  method
    | .module, n => if n == importHook "typing" then some fun {_} {_} [_] [_] => importTyping else none
    | _, _ => none
  native := typingNative

end

end StrataPython.Dyn.Sem.Modules
