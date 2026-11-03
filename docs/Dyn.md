# Dyn

Dyn is a typed intermediate representation for programs, defined in Lean. A front end
translates a source language into Dyn, and analyses and interpreters work on Dyn
rather than on the source language. This document is a self-contained reference for Dyn
itself, and §4 shows how a language gives its programs a semantics that runs them.
[Python to Dyn](./PythonToDyn.md) describes how Python is translated into it.

## 1. Overview

Dyn separates the vocabulary a language provides from the programs written in it:

* An **environment** declares the vocabulary: types and instructions. A type is either
  primitive, such as `Int`, or a datatype with constructors, such as `Except`. An
  instruction declaration gives an operation's name and signature, such as an `add` that
  takes two values and returns a value. Apart from constants, every instruction a program
  uses is declared in its environment. Primitive types, datatypes and instructions may have
  type parameters, each ranging over types or over lists of types, such as the argument types
  of a function type `Fn [Int, Bool] Int`. A list may splice in list parameters' elements:
  `[*as, Int]`. The DSL that writes environments accepts at most one splice in a literal, at any
  position, as in `[Int, *as, Bool]`, so that inference from a result type has one answer. An
  instruction's variadic operands are any
  number of one type, or one per element of a list, and a successor's payload may likewise
  pass one value per element of a list; a constructor's fields, a region's parameters and a
  block's parameters are one value each. An application passes an argument
  of its parameter's kind for each type parameter.
* A **program** is a module of functions written against one environment. A function is a
  set of blocks. A block takes parameters, runs a sequence of instructions, and ends with a
  terminal instruction, such as a jump to another block or a return. Each value is defined
  once and has a type from the environment. An instruction's signature may declare
  *successors*, each with a payload. An application fills each with a *target*: a block and a
  prefix of its arguments, to which the instruction passes the payload after them.

Environments are built in layers. The **base environment** declares what every language
needs, and a language's environment refines the base by adding its own types and
instructions. For example, Python's environment adds a value type and the Python
operations. We have a general notion of refinement for environments that captures extending
environments with new operations as well as replacing abstract types with more precise
definitions (such as inductive types).

We write `t ≤ s`, or `t ≼ s` for the class that instance search uses, when `s` refines `t`:

* **Types:** every type of `t` is a type of `s`, with the same parameters. An abstract type of
  `t` may be a datatype in `s`.
* **Datatypes:** every datatype of `t` is the same datatype in `s`.
* **Instructions:** every instruction of `t` is an instruction of `s` with the same signature.
  An ordinary instruction of `t` may be a constructor or a case instruction in `s`.
* **Annotations:** `≤` requires each annotation of `t` to equal that of its refinement in `s`.
  `Env.LeBy R` relates them by `R` instead.

`s` may declare more than `t`. Refinement ignores positions: the same declarations in another
order refine each other.

Environments and programs come with a well-formedness check. A well-formed environment is one
whose type references all resolve to earlier declarations. A well-formed program uses only
instructions its environment declares, at their declared types, and passes each block the
arguments it expects. Lean's types guarantee that every reference to a type or instruction
resolves; a checker decides the rest. A function is checked on its own, and a module is
checked from its functions: their names are distinct, and every reference to a function names
one of them, at its code type. A function's code type is `base.Fn as r`, with `as` its
parameters' types and `r` its return type, and `base.callCode` calls through a value of that
type. A `Module.Raw` is a module as built, which may not be well formed; it still
prints, in full, for diagnostics. A `Module` is one with its proof of well-formedness, and is
the same data at run time.

**Scoping.** In an SSA function, block A *dominates* block B when every path from the entry
to B passes through A. The *immediate dominator* of B is the closest block that dominates
it, and the immediate dominators form the *dominator tree*. A value may be used only where
its definition dominates the use. Dyn refines dominance to points within a block: a
block's parameters are in scope from its start, and an instruction's result is in scope
after that instruction. A transfer to one of an instruction's successors, such as an
exception edge, leaves from just before the instruction, so a handler cannot see the result
of the instruction that raised.

The IR stores no dominance information. A well-formed function has every block reachable from
its body's entry, and for each body *some* legal tree puts every use in scope. A tree gives
each block other than the entry a parent, a point of the body: another block after some of its
instructions. It is legal when every chain of parents reaches the entry and every transfer into
a block leaves from the block's parent or a point below it in the tree. The rule names no
algorithm. The checker computes the immediate-dominator tree and checks the uses against it.
That tree is proved legal and, when every block is reachable, exact: a point's ancestors in it
are exactly its dominators. So the check accepts exactly the functions that some legal tree
scopes, and these are exactly the dominance-correct ones. The builder drops the blocks the
entry cannot reach, so a producer leaves dominance to the checker. When a function it reads is
not well formed for these reasons, the reader names each unreachable block, and each use out of
scope with a path from the entry that reaches it without passing its definition.

**Regions.** An instruction may own nested bodies, called regions, as in MLIR. A region is a
list of blocks, the first its entry, whose parameters are the region's arguments. A transfer
inside a region names a block of the same region or the region's exit, so control leaves a
region only through its exit, back to the instruction that owns it. A region's blocks have
trees of their own, rooted at its entry. Values in scope at the owning instruction
are visible inside the region, and values defined inside are local to it. An `if` whose
branches are regions:

```
%r.0 : base.Int = demo.if[base.Int](%c.0) {
  then.0():
    ret(%x.0)
} {
  else.0():
    ret(%y.0)
}
```

**Annotations.** Every part of a program carries an annotation of a type the front end chooses,
such as a source position, so that results can be reported against the original source.
Dyn does not depend on annotations for its semantics. A front end can also state facts
about a function as *attributes* (`StrataDyn/Attr.lean`): named values, such as a declared
shape, that the printer writes and the reader reads back. The IR gives them no meaning.

**Building.** A front end emits a function through the builder (`StrataDyn/Build.lean`),
which checks the function when it is finished. Each instruction has a typed emitter under its
own name, whose Lean type is the instruction's signature, so Lean checks the operands and infers
the type arguments; the instruction itself is `o.ref`. Where `Strata.Dyn.Emit` is open,
`let% x ← e` names the value or block `e` makes after the Lean binder `x`. Other values are
named after their instruction, or after an explicit `result`, and other blocks `bb`, or after an
explicit base:

```lean
let% cell ← Base.refNew zero                    -- %cell.0
let% r ← Base.refGet (← Base.refNew zero)       -- %refNew.0, then %r.0
let% x ← Base.refGet cell (result := n "read")  -- %read.0
let% ok ← Emit.freshLabel [Base.Int]            -- ^ok.0
```

Dyn is implemented in the directory `StrataDyn`. Declarations are defined in
the namespace `Strata.Dyn`.

## 2. Printed form

A module prints as text, through a Strata DDM dialect (`StrataDyn/DDM.lean`), and the
text reads back (`StrataDyn/DDMRead.lean`):

```
module m {
  func @m.f(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%x.0 : py.Value):
      %int.0 : py.Value = py.intLit(1)
      %add.0 : py.Value = py.add(%x.0, %int.0) ^propagate.0()
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%add.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
}
```

* **Values** print by name, `%x.0`, with their type where they are defined.
* **Blocks** print as their label and parameters; the entry block's parameters are also the
  function's.
* **Applications** print as the operation, its type arguments in brackets, its operands in
  parentheses, then its successors, each `^label(args)`, then its regions, each in braces.
  Empty brackets and parentheses are left out: `py.noneLit`, `unreachable`. A list of types
  prints as a literal, as a type argument or inside a type:
  `fns.callFn[[base.Int, base.Bool], base.Int](%g.0, %x.0, %y.0)`.
* **Terminators** print as applications without a result. The base's control flow drops
  `base.`: `jump ^done.0(%v.0)`, `branch(%c.0) ^some.0() ^none.0()`, `unreachable`. A jump
  to the exit is `ret(%ret.0)`.
* **Names** print dotted, as one identifier, escaped whole when needed: `@|m.<module>|`. A
  function name is marked `@`.
* **Literals** are untagged, and a literal's form fixes its type, with no widening. An
  integer `5` or `-1` is a `base.Int`. A float always has a decimal point or an exponent
  (`1.0`, `0.0025`, `1e22`), and is the shortest decimal that reads back as it, or `inf`,
  `-inf` or `nan`; it is a `base.Float64`, so `1` is never one. A boolean is `true` or
  `false`, a string `"…"`, the unit `unit`, and a function pointer `@m.f`.
* **Attributes** of a function print below its signature, one `#[key = value]` line each,
  then a blank line. A value is a literal, a list `[v, …]` or a record `{k = v, …}`, and a
  key is prefixed by the front end that gives it its meaning, such as `py.` for Python.
* **Constants** are written at their uses by default, as in `py.intLit(1)`.
  `PrintOptions.full` prints each on its own line instead: `%c.0 : base.Int = const 1`, then
  `py.intLit(%c.0)`.

`Module.format` prints a `Module`, folded by default. `Module.read env text` reads either form
against an environment and returns a `Module`, or the diagnostics. Reading and printing in
the same form gives the text back. Lines that start with `--` are comments. `pydyn read
FILE` reads a printed module against the Python environment and prints it again.

## 3. Ref-to-reg

`refToReg` (`StrataDyn/RefToReg.lean`) promotes cells to SSA values. A cell is a mutable
location, a `base.Ref a`: `base.refNew` makes one, `base.refGet` reads it and `base.refSet`
writes it. A cell made by `base.refNew` is promoted when the value that names it is used only
as the cell operand of `base.refGet` and `base.refSet`, the results of its `base.refSet`s are
unused, and its content is known at every read (as defined below). Each read is removed, and
its uses use the value that holds the content there. Each write is removed. Where edges with
different contents meet, the block takes the content as a new parameter, and each edge passes
it, an instruction's error edge included. The `refNew` stays, unused: when the module runs, a
cell is a location in a heap, numbered in the order the cells are made, and an operation given
a cell may keep its number, so removing a `refNew` could renumber the cells made after it.

```
entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):     -- before
  %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
  branch(%c.0) ^yes.0() ^join.0()
yes.0():
  %u.0 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
  jump ^join.0()
join.0():
  %r.0 : base.Int = base.refGet[base.Int](%x.0)
  ret(%r.0)

entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):     -- after
  %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
  branch(%c.0) ^yes.0() ^join.0(%a.0)
yes.0():
  jump ^join.0(%b.0)
join.0(%a.1 : base.Int):
  ret(%a.1)
```

A cell's content is known at a point unless, on some path to it, an instruction whose regions
write the cell (at any depth) comes after the cell's last write. Such an instruction makes the
cell unknown on its edges, after it, and at the start of each of its regions. So a read of such
a cell after the instruction, or in one of its regions before that region writes the cell,
keeps the cell as it is: none of its reads or writes is removed.

The pass relies on two more rules, which every environment and its front end must keep:

* A region runs only while the instruction that owns it runs. The instruction may run each of
  its regions any number of times, in any order.
* An operation reaches only the cells it is given, as operands or inside values it can read. So
  a front end passes a cell to every operation that may read or write it.

A block takes each cell's content from its parent in the dominator tree, a point that may be in
the middle of another block (§1), unless the content may change on some path from there into the
block: then the block takes a new parameter, or one value that
every edge into it passes. The check computes where contents may change from the dominator tree
and the function itself, so it doesn't rely on the plan for that.

The pass computes a plan, checks it (`Plan.check`), applies it, and checks the module's
well-formedness again. If planning or either check fails, it returns no module, and names each
function concerned with the reason.

## 4. Giving a language its semantics

A language gives each type a Lean type and each instruction a rule, an ordinary Lean function.
Dyn generates from them a table, and runs modules against it. The rule interface is
`StrataDyn.Exec` (`StrataDyn/Exec.lean`), and a module that runs programs imports
`StrataDyn.Exec.Run`. The examples below come from the While example
(`StrataDyn/Examples/While/Env.lean`) and the test environment `Ex`
(`StrataDynTest/Exec/TestEnv.lean`).

### Rules over Lean types

A rule names Lean types only. An instruction with neither regions nor successors may take a
pure rule, a function from its operands to its result:

```lean
@[dyn_sem While.add] def add (a b : Int) : Int := a + b
@[dyn_sem While.lt] def lt (a b : Int) : Bool := decide (a < b)
```

Any other rule returns `Sem ε E α`, a free monad, and is written with `do`. It is generic in
its requests `ε` and its exits `E`, and usually takes them from a `variable` line:

```lean
variable {ε : Eff} {E : Type}

@[dyn_sem While.pow] def pow (_a _b : Int) : Sem ε E Int :=
  semanticGap "while.pow: not implemented"
```

`semanticGap msg` stops the run with `Fault.gap`, for a case the semantics leaves out, and
`semanticFailure msg` with `Fault.failure`, for one the author holds impossible. `assume b msg`
continues if `b` holds and otherwise stops with `Fault.blocked`: the path is infeasible, which
stands for no behaviour rather than an error, and a run reports it as its outcome. `chooseNat` asks the run's
oracle for a number, `choose n` for one from `0` to `n`, which is the oracle's answer reduced,
and `chooseInt` for an integer, which numbers the integers `0, -1, 1, -2, …` by the oracle's
answer. A rule takes no fuel: the machine runs its requests as steps.

Rules are trusted: a rule is what its instruction means. Registration checks a rule's type
against its instruction's signature and the capabilities it takes, and that no instruction has
two rules, and each table checks every rule again at its own type rules. `implemented_by` and
`@[extern]` in a rule are flags for review, as in Lean.

### Types and rules: `@[dyn_type]` and `@[dyn_sem]`

`@[dyn_type T] d` makes the Lean type `d` the meaning of the primitive or opaque Dyn type
`T`, with one Lean parameter per Dyn parameter:

```lean
attribute [dyn_type Base.Int] Int
attribute [dyn_type Base.Sequence] Array
attribute [dyn_type Base.Except] Except
```

A datatype takes no attribute: `#dyn_types E` generates a Lean inductive for each of `E`'s
datatypes, with one constructor per Dyn constructor, and registers it. `#dyn_types While`
gives `While.IntList.Val` and `While.Flow.Val`. It comes after the rules of the primitive types
its datatypes' fields use, and before the rules that name its datatypes.

`@[dyn_sem o] r` makes `r` the rule of the instruction `o`. Keys are the Lean names of the
environment's types and instructions, `While.add` or `Base.Int`, so a misspelt key is an
elaboration error. An instruction's key is its own name, which its emitter shares, not its
reference `While.add.ref`.
The engine gives `base.Ref` and `base.Fn` their meaning, the constructors and case instructions
of a datatype are derived, and the machine implements `base.refNew`, `refGet`, `refSet` and
`callCode`: none of these takes a rule. Dyn types that share a Lean type share a tag, so a
semantics that must tell two types apart gives them distinct Lean types.

### Operands, regions, targets and `Again`

A rule's explicit arguments follow the instruction's signature, in order:

1. its operands, at their Lean types, then the variadic operands as an `Array`;
2. one `Region ε ts α` per region, whose parameters have the Lean types `ts` and whose result
   is an `α`;
3. one `Target E ts` per successor, the target the rule jumps along with the successor's
   payload, of the Lean types `ts`;
4. for a rule that loops, its state `(st : Option σ)` and then its instruction's `Again E σ`,
   for a Lean type `σ` the rule chooses.

A rule with type parameters takes one `{α : Type}` per parameter, in order. A terminal
instruction's rule returns `Sem ε E Empty`. `While.loop` takes all four kinds:

```lean
insn loop (&cond : Bool) (&body : Flow) (^err (code : Int)) : Unit
```

```lean
@[dyn_sem While.loop]
def loop (cond : Region ε [] Bool) (body : Region ε [] Flow) (err : Target E [Int])
    (_st : Option Unit) (again : Again E Unit) : Sem ε E Unit := do
  if ← runRegion cond () then
    flow (← runRegion body ()) err
    jump again ()
```

The state is the rule's own: the instruction's declaration does not mention it, so neither do
the IR, the printed form nor a front end. A loop whose variables are cells, as While's are,
has the state `Unit`.

### Jumps and regions

`jump k payload` leaves along the target `k` with its payload, a value for one type, a tuple
for several, `()` for none. A terminator's rule leaves only by `jump`:

```lean
@[dyn_sem Ex.br] def br (c : Bool) (t f : Target E []) : Sem ε E Empty :=
  if c then jump t () else jump f ()
```

`runRegion r args` runs the region `r` on its arguments and returns its result. A rule that
loops runs first with the state `none`. `jump again s` runs the instruction again, as a step
of its own, on the same operands, regions and targets, with the state `some s`. A fold's state
is its accumulator:

```lean
insn fold (init : Int) (&cond (acc : Int) : Bool) (&body (acc : Int) : Int) : Int
```

```lean
@[dyn_sem Ex.fold]
def fold (init : Int) (cond : Region ε [Int] Bool) (body : Region ε [Int] Int) (st : Option Int)
    (again : Again E Int) : Sem ε E Int := do
  let acc := st.getD init
  if ← runRegion cond acc then jump again (← runRegion body acc)
  return acc
```

A comprehension over `xs` handles one element per run, and its state is the elements left and
the results so far, starting from `(xs, #[])`. `mapStep` runs the body on the first element
and jumps to `again` with the rest:

```lean
@[dyn_sem Ex.mapList]
def mapList (xs : Array Int) (body : Region ε [Int] (Except Int Int)) (err : Target E [Int])
    (st : Option (Array Int × Array Int)) (again : Again E (Array Int × Array Int)) :
    Sem ε E (Array Int) :=
  let (rest, acc) := st.getD (xs, #[])
  mapStep rest acc body err again
```

### The world and `HasPart`

The world is the state a run threads through its rules, such as output. `#dyn_sem_table`
takes it as `(world := W)`, and it defaults to `Unit`. A rule reaches the parts it names
through `[HasPart ε.W P]`, with `getThe P`, `modifyThe P` and `modifyGetThe P`. The world's
type is abstract in a rule, so a rule reads only the parts it names. It can still put back a
world it read earlier, whole, and `HasPart` states no laws. Each of the three is one `update`
request: the machine takes the world out of its configuration and hands it to the request,
which returns the new world, so a part that `modifyThe` updates is held by nothing else:

```lean
structure World where
  out : Output := {}
  ticks : Ticks := {}
  deriving Inhabited, Repr, DecidableEq

instance : HasPart World Output := ⟨(·.out), fun w o => { w with out := o }⟩

@[dyn_sem While.print] def print (x : Int) : Sem ε E Unit :=
  modifyThe Output fun o => { o with items := o.items.push x }
```

### Refs and tags

A run's cells live on the machine's heap. `Ref σ α` is a ref to a cell holding an `α`, where
`σ` is the run token, so a rule that takes or makes a ref is generic in it,
`{σ : Type} [Store σ]`. A ref holds a proof that the token gives, so no term generic in `σ` is
a ref (`no_forge`). `newRef`, `readRef` and `writeRef` make, read and write cells through the
capability `[HasHeap σ ε]`:

```lean
@[dyn_sem Ex.cellNew] def cellNew (v : Int) : Sem ε E (Ref σ Int) := newRef v
@[dyn_sem Ex.cellGet] def cellGet (c : Ref σ Int) : Sem ε E Int := readRef c
```

`modifyRef c f` replaces a cell's contents `x` by `f x` in one request. The machine takes the
contents out of the cell before it applies `f`, so `f` updates contents that nothing else
holds:

```lean
@[dyn_sem Ex.cellPush] def cellPush (c : Ref σ (Array Int)) (x : Int) : Sem ε E Unit :=
  modifyRef c (·.push x)
```

A ref is a raw ref, `Ref.Raw σ`, a location with the token's proof, and its contents' type as a
phantom; a closure is likewise a raw closure, `FnRef.Raw σ`. The proofs name no Lean type, so a
datatype may hold a ref or a closure of itself, as the test environment's
`data Chain where | done | link (next : Ref Chain)` does.

The machine checks every access by the cell's tag: the tag of the Lean type it holds. A rule
that makes, reads or writes a cell at `α` takes `[TagOf σ α]`, and `[Decode σ]`, at which the
tag decodes to `α`. A rule generic in `α` takes `[TagOf σ α]` only if it reaches a cell at `α`.
`TagCon σ F` gives the tags of `F A` from those of `A`, and `TagCon₂ σ F` those of `F A B`, for
a rule that reaches cells through a type constructor:

```lean
@[dyn_sem Ex.newAt]
def newAt {A : Type} [TagOf σ A] (v : A) : Sem ε E (Ref σ A) := newRef v
```

The table supplies every tag, at the instruction's concrete types. A start argument holds no
ref, and an access the check rejects faults with `Fault.badCell`.

### Calls and closures

`base.Fn as r` is a closure, `FnRef σ as r`: a function of the module and the values it
captured. `callFn f args` calls one, and `bindFn f x` binds its first argument, making a new
closure, both through `[HasCall σ ε]`. A call takes the signature's tags, `[SigOf σ as r]`, and
the instances that build them from `TagOf`s are found for it:

```lean
@[dyn_sem Ex.call]
def call (f : FnRef σ [Int] (Except Int Int)) (x : Int) (err : Target E [Int]) :
    Sem ε E Int := do
  match ← callFn f x with
  | .ok v => return v
  | .error e => jump err e

@[dyn_sem Ex.bind]
def bind {A B R : Type} [TagOf σ A] [TagOf σ B] [TagOf σ R] (f : FnRef σ [A, B] R) (x : A) :
    Sem ε E (FnRef σ [B] R) :=
  bindFn f x
```

The machine checks each call against the function's signature and faults with
`Fault.badCall` on a mismatch. A language whose functions raise returns a `base.Except`, and its
call rule inspects it, as `call` does.

An instruction with a list parameter takes a rule with a `{cs : List Type}` for it. The list
may be spliced into a closure operand's arguments and be the spread, whose operands the rule
takes as one `Payload cs`; `⟦Fn [*cs, Int] Int⟧` is `FnRef σ (cs ++ [Int]) Int`. The rule takes
`[TagsOf σ cs]`, the tags of the list's elements, and `bindAll` binds a closure's leading
arguments to the payload, one `bindFn` each. This is the shape of Python's `mkClosure`:

```lean
insn mkClo [(cs : list)] (code : Fn [*cs, Int] Int) (*cells : cs) : Fn [Int] Int
```

```lean
@[dyn_sem Ex.mkClo]
def mkClo {cs : List Type} [TagsOf σ cs] (code : FnRef σ (cs ++ [Int]) Int) (cells : Payload cs) :
    Sem ε E (FnRef σ [Int] Int) :=
  bindAll cs code cells
```

A list variable may occur only there: not in the result, a region, a successor's payload or
inside an operand's datatype.

### A language's capabilities: `@[dyn_lang]`

`@[dyn_lang]` declares a language's capabilities as one class, whose fields are parts of the
world, `HasHeap`, `HasCall` and tags, or a parent language's class it extends. Each field
becomes an instance, so a rule that takes the class has every capability:

```lean
@[dyn_lang] class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  out : HasPart ε.W Output
  ticks : HasPart ε.W Ticks
  heap : HasHeap σ ε
  tagInt : TagOf σ Int

variable {σ : Type} [Store σ] [Decode σ] [Lang σ ε]
```

The token is an `outParam`, so a part of the world, which does not mention it, is found
through the class.

### The table and `#dyn_coverage`

`#dyn_coverage E` lists each type and instruction of `E` with its rule, `derived`, the
engine's or `missing`, and counts the ancestors' missing rules. `#dyn_coverage E (complete)`
is silent when every type and instruction of `E` and its ancestors has its meaning, and an error
naming the missing ones otherwise:

```lean
#dyn_coverage While (complete)
```

`#dyn_sem_table S for E (world := W)` generates the table in the namespace `S`: the tags,
one wrapper per instruction, and, for an environment that extends `Base`, `S.model`, which
modules run against. An instruction with no rule is reported and left out, and a module that
uses it faults with `Fault.missingRules` before its first step. A child environment's table
uses its ancestors' rules.

```lean
#dyn_sem_table WhileSem for While (world := WhileRules.World)
```

### Registration errors

`@[dyn_type]`, `@[dyn_sem]` and `@[dyn_lang]` check each registration against the
`environment` declaration, and name what does not match: the operand, region, target, state,
`Again` or result. Examples, from `StrataDynTest/Exec/RuleErrorTest.lean`, for
`insn inc (x : Int) : Int`, `insn split (x : Int) (^neg) (^big (q r : Int)) : Int` and
`insn drain (x : Int) (*xs : Int) (^neg) : Int`:

| Rule | Error |
|---|---|
| `def incNat (x : Nat) : Int` | operand x of err.inc: expected Int, but incNat takes Nat |
| `def inc2 (x _y : Int) : Int` | err.inc takes 1 operand, but inc2 takes 2 |
| `def incSem (_x : Int) : Sem ε E Bool` | the result of incSem is Sem ε E Bool, but err.inc needs Sem ε E Int |
| `def incFixed (x : Int) : Sem ε Nat Int` | incFixed must be generic in its requests and exits: incFixed {ε : Eff} {E : Type} … : Sem ε E … |
| `def split1 (x : Int) (_neg : Target E []) : Sem ε E Int` | err.split has 2 successors (^neg, ^big), but split1 takes 1 target |
| `… (_neg : Target E []) (_st : Option (Int × Array Int)) (_again : Again E Int)` | the Again of err.drain: expected Again (Int × Array Int), got Again Int |
| `… (_neg : Target E []) (_again : Again E (Int × Array Int))` | drainNoState takes Again (Int × Array Int) without its state: a rule that loops takes (st : Option σ) before its Again |
| `@[dyn_sem Demo.Box.box]` | demo.box is a constructor of demo.Box, derived, and takes no rule |
| `@[dyn_sem Base.refNew]` | base.refNew is implemented by the machine, and takes no rule |
| `[TagOf σ (List Int)]` | List Int is the Lean type of no Dyn type: register its type with @[dyn_type] |
| `(c : Ref Run Int)` | base.Ref needs the run token: a rule that takes or makes one must be generic in it, {σ : Type} [Store σ] |
| `{cs : Type}` for `[(cs : list)]` | type parameter cs of errCall.spread is a list, so spreadType's cs must be a List Type |
| `… : Sem ε E (FnRef σ cs Int)` | the result of errCall.spreadOut: a list type variable may occur only in the arguments of a closure operand, as a splice, and as the spread |

A module that imports two modules that both register one type or instruction gets an error
naming both, at `@[dyn_sem]`, `#dyn_coverage`, `#dyn_types` and `#dyn_sem_table`
(`StrataDynTest/Exec/DupTest.lean`). Two modules that register the same declaration give one
rule (`DupSharedTest.lean`).

`#dyn_sem_table` checks each rule, and each datatype's type rule, again at its own type rules.
A rule's module may have seen another type rule, through an import that the table's module does
not see: a rule registered where `Num ↦ Int` is an error at a table where `Num ↦ Nat`
(`RecheckTest.lean`, `RecheckDataTest.lean`).

### Running a module

`runModule M m f args fuel` links the module `m` against the model `M`, checks it, and runs its
function `f` on `args` for at most `fuel` steps. An argument is a Lean value, `M.arg x`, at the
tag of its Lean type, found as a rule's is. A run ends as an `Outcome M`: its result, a
`Snapshot` of the heap and the world, the steps and the oracle's answers. `o.read? α` reads the
result as an `α`: `some x` if its tag is `α`'s, and `none` if it has another tag or the run
faulted.

```lean
let o := runModule ExSem.model m (nm "arith")
  #[ExSem.model.arg (3 : Int), ExSem.model.arg (4 : Int)] 10000
o.read? Int   -- some 6
o.read? Bool  -- none
```

`M.read? r α` reads a `Result` the same way, and `o.result` is the result itself, a value or a
`Fault`. `runModule` runs the fused engine, `runFused`, by default; `(engine := .frames)` runs
the reference machine, `runFrames`. Given enough fuel both end with the same outcome, snapshot
and choices (`runFused_of_runFrames`, `runFrames_of_runFused`). Each counts fuel in its own
steps, so on the same fuel `runFused` may finish where `runFrames` runs out, but not the
reverse.

`startCore hw i args snap` starts function `i` from a snapshot, by default `Snapshot.initial`,
an empty heap and the initial world. A module's top level can run first, and a function of the
module then from `o.snapshot`, the heap and the world where the top level ended
(`StrataDynTest/Exec/HeapTest.lean`). One value holds both, so a run cannot start from one
run's heap and another run's world.
