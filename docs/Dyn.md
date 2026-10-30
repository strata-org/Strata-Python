# Dyn

Dyn is a typed intermediate representation for programs, defined in Lean. A front end
translates a source language into Dyn, and analyses and interpreters work on Dyn
rather than on the source language. This document is a self-contained reference for Dyn
itself. §4 shows how a language gives its programs a semantics that runs them, §5 how to
reason about those runs, and §6 how Dyn's types are translated to Core.
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
* A **program** is a module of functions written against one environment. A module may also
  have ghosts, cells that only contracts can name (**Ghost state**, below). A function is a
  set of blocks, or, if it is extern, a signature and a contract only. A block takes
  parameters, runs a sequence of instructions, and ends with a terminal instruction, such as a
  jump to another block or a return. Each value is defined once and has a type from the
  environment. An instruction's signature may declare *successors*, each with a payload. An
  application fills each with a *target*: a block and a prefix of its arguments, to which the
  instruction passes the payload after them.

Environments are built in layers. The **base environment** declares what every language
needs, and a language's environment refines the base by adding its own types and
instructions. For example, Python's environment adds a value type and the Python
operations. We have a general notion of refinement for environments, **environment
refinement**, that captures extending environments with new operations as well as replacing
abstract types with more precise definitions (such as inductive types). It is unrelated to the
trace refinement of programs (§5, "Trace refinement").

We write `t ≤ s`, or `t ≼ s` for the class that instance search uses, when `s` refines `t`:

* **Types:** every type of `t` is a type of `s`, with the same parameters. An abstract type of
  `t` may be a datatype in `s`.
* **Datatypes:** every datatype of `t` is the same datatype in `s`.
* **Instructions:** every instruction of `t` is an instruction of `s` with the same signature,
  its effect included. An ordinary instruction of `t` may be a constructor or a case
  instruction in `s`.
* **Annotations:** `≤` requires each annotation of `t` to equal that of its refinement in `s`.
  `Env.LeBy R` relates them by `R` instead.

`s` may declare more than `t`. Environment refinement ignores positions: the same declarations
in another order refine each other.

Environments and programs come with a well-formedness check. A well-formed environment is one
whose type references all resolve to earlier declarations. A well-formed program uses only
instructions its environment declares, at their declared types, and passes each block the
arguments it expects. Lean's types guarantee that every reference to a type or instruction
resolves; a checker decides the rest. A function and a ghost are each checked on their own, and
a module is checked from them: their names are distinct, every reference to a function names one
of them, at its code type, and every reference to a ghost names one of them, at the type of its
cell. A function's code type is `base.Fn as r`, with `as` its
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
scope with a path from the entry that reaches it without passing its definition. It does the same
for each contract region (**Contracts**, below), which is scoped as a body of its own.

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

**Effects.** Every instruction declaration has an effect, an upper bound on what the operation
itself may do, its regions aside. From the least to the most:

* `pure`: it reads no mutable state. It may allocate, as `py.mkTuple` does: allocating a new
  object is not a change of state. So `pure` doesn't make an unused result removable: removing a
  `base.refNew` could renumber the cells made after it (§3).
* `reads`: it may read mutable state, as `base.refGet` does.
* `calls`: it may run code that the IR does not show, such as a user-defined method (a Python
  `__eq__` or a JavaScript getter), and that code may read or change any state it can reach. The
  methods that the operation looks up on an operand, or on an object that an operand holds, count
  as such code, built-in methods included, such as the `__next__` of a Python built-in iterator.
  The operation's own fixed computation does not.
* `writes`: the operation itself may change state, as `base.refSet` does.

The DSL writes the effect before `insn`, and before `terminal`: `pure insn mkTuple …`,
`reads insn refGet …`, `pure terminal insn jump`. Without one, an instruction is `writes`, so an
operation that nobody marked is never accepted in a contract. A datatype's constructors and its
case instruction are `pure`. Environment refinement compares effects, so an ordinary instruction
that an environment refinement turns into a constructor must be declared `pure`.

**Failures.** An operation that may fail, such as a division, declares a successor for the
failure, such as an `err` successor. A *failure successor* is a successor of an instruction, as
opposed to a terminator. A region *may propagate* when its owner is an instruction that declares
a failure successor, and that declares the region's result type as a `base.Except`, before its
type arguments are put in. The checker trusts every environment to follow this rule for each
operation that is not declared `writes`, since only those may appear in a contract: the
operation reports a failure only through a failure successor, never as an `error` value that it
returns. When a region that may propagate returns `error`, its owner transfers to one of its
failure successors; it never uses the error as a value, and never passes it to another region.

**Contracts.** A function may have a contract: what a caller must establish before a call,
and what the function establishes when it returns. A `requires` or `ensures` clause is a
region that returns a `base.Bool`. A `requires` clause takes no arguments, and an `ensures`
clause takes the function's result. Such a clause sees only the function's parameters and its
own values, and the body sees none of the clause's. A `requires` clause is evaluated in the
state at the call, and an `ensures` clause in the state at return, where `base.old` reads the
state at the call (**`old` in `ensures` clauses**, below):

* A `requires` clause is a condition that the caller establishes at each call.
* An `ensures` clause is a promise that holds at every exit of a defined function.
* A `free ensures` clause is assumed after every call and never checked: it is trusted.

A clause may carry a message, which names it in diagnostics:
`requires "x is non-negative" {`. For a `free` clause, the message also says where the trust
comes from, such as "admitted postcondition of 'f'". A clause must not change state. The
checker rejects every instruction or terminator in a contract region (a clause, a frame region,
or a region nested in one at any depth) that applies an operation declared `writes`. So a clause
cannot call a function: `base.callCode` is `writes`. A `reads` or `writes` clause is a frame: a
set of locations that the function may read or change (**Frames**, below). A function without a
contract has no clauses, and its body's brace stays on the signature's line.

```
func @m.inc(%x.0 : base.Int) -> base.Int
  requires {
    pre.0():
      %ok.0 : base.Bool = demo.ge(%x.0, 0)
      ret(%ok.0)
  }
  ensures {
    post.0(%r.0 : base.Int):
      %ok.1 : base.Bool = demo.ge(%r.0, %x.0)
      ret(%ok.1)
  }
  reads()
  writes()
{
  entry.0(%x.0 : base.Int):
    %s.0 : base.Int = demo.add(%x.0, 1)
    ret(%s.0)
}
```

**Extern functions.** An extern function has a signature and a contract, and no body, such as a
library function whose code is not available. Its parameters get the first ids, 0, 1, …, in the
order they are declared. Its `requires` clauses are checked at calls, its `ensures` clauses must
all be `free`, and its frames are trusted. A defined function's `ensures` clauses are all
checked, and no `requires` clause is ever `free`. A `requires` clause is known to hold only at
the calls that the verified program makes. An extern may call a function value that it received
(a callback), and Dyn has no way to state what an extern calls, so nothing checks those
calls: a defined function whose code pointer reaches an extern may be entered without its
`requires` clauses holding. An extern's attributes are not printed, so facts belong to defined
functions. An extern prints as `extern func`, on one line when it has no contract:

```
extern func @m.f(%x.0 : base.Int) -> base.Int
  requires "x is non-negative" {
    pre.0():
      %ok.0 : base.Bool = demo.ge(%x.0, 0)
      ret(%ok.0)
  }
  free ensures "admitted postcondition of 'f'" {
    post.0(%r.0 : base.Int):
      %ok.1 : base.Bool = demo.ge(%r.0, 0)
      ret(%ok.1)
  }
```

**The trust base.** A module's trusted assumptions are its externs' signatures, `free ensures`
clauses and frames, and its ghosts' invariants and first values (**Ghost state**, below): nothing
checks that a value an extern returns has its return type, nor that a ghost's first value
satisfies its invariant. A `free ensures` clause can give the program a ghost's cell or the
object it holds; the program can then change them, and the ghost's invariant must still hold. A
consumer can list the trusted assumptions from the IR. The declarations of the module's
environment are trusted too: each operation's effect, and the rule in **Failures**, above. Like
any trusted assumption, a `free ensures` clause that is false makes every proof that relies on it
vacuous.

**What clauses mean.** A clause denotes the `base.Bool` that its region returns.

* The `requires` clauses are evaluated in order, in the state at the call. The call satisfies
  them when each returns true. A later clause is evaluated only when the earlier ones returned
  true, so it may rely on them.
* The `ensures` clauses are evaluated in order at an exit, with the result. Clause *k* is
  evaluated only when every `requires` clause returned true at the call, and `ensures` clauses 0
  to *k*−1 returned true at this exit. An `ensures` clause relies on the `requires` clauses as
  facts about the state at the call, not after it. For example, `requires len(xs) > 0` does not
  make `ensures xs[0] >= 0` well defined, since the call may empty `xs`.
* An `ensures` clause takes the function's result, of its return type. The core fixes no
  convention for exceptions. For Python, the result is a `base.Except(py.Value, py.Value)`, so a
  clause may state what holds when the function raises.
* A contract does not state whether a function terminates. An `ensures` clause holds at every
  exit, and a call may also not return.
* A region is *well defined* in a state when, run there, it reaches no `unreachable`, terminates,
  returns, on every run, the same value, up to the identity of the objects that the run
  allocates, and every `calls` operation in it changes no state. An operation's meaning may
  assume something of its operands, such as that an index is in range. Where the assumption
  fails, the result is not defined, and a region that applies the operation there is not well
  defined. A consumer, such as a verifier, relies on nothing from a region that it cannot show
  well defined: it assumes nothing from it, and a check of it fails. This holds for every kind of
  contract region, so an ill-defined region can only lose information.

**Failures in contracts.** An operation that fails transfers to its failure successor. In
a `requires` clause or a checked `ensures` clause, a failure gives `false`. In a `free ensures`
clause, a failure gives `true`. So a failure never makes a checked clause hold, and never makes a
free clause assume anything. The value applies to the whole clause, never to a part of it, so a
negation cannot turn it around. For example, `requires not (len(x) > 5)` with `x = 3` is
`false`, not `true`: `x` is an int, so `len` raises. The checker makes the IR state these values:

* In a clause's own blocks, every failure successor goes to a *failure block* of the clause: a
  block whose instructions are only constants, and that ends in `unreachable` or in `ret` of the
  constant `false`, or `true` in a `free ensures` clause.
* In a frame region's own blocks (**Frames**, below), every failure successor goes to a block
  whose instructions are only constants and that ends in `unreachable`. A frame region has no
  failure value.
* In a region nested in a clause or a frame region, at any depth, every failure successor goes to
  a block whose instructions are only constants and that ends in `unreachable`, or, if the region
  may propagate, to a *propagating block*. The only instruction of a propagating block applies
  `base.error` to the block's last parameter, the failure received, and the block ends in `ret`
  of that instruction's result. So a nested region never turns a failure into a value, and the
  failure successor of the operation that owns the region carries the failure on to the clause.
  A generic `if [a] (&then &else : a)` used at an `Except` type returns the `error` as its
  value, and an operation whose region returns a `base.Except` but that declares no failure
  successor has nowhere to pass the failure on. So their regions may not propagate.
* Every block of a contract region, at any depth, ends in control flow: `ret`, `jump`,
  `branch`, `unreachable`, or a datatype's case instruction. So no terminal operation's
  successor carries a failure.
* The blocks of every contract region, at any depth, form an acyclic graph of transfers. A
  clause then terminates unless an operation in it does not.

A failure block is an ordinary block. Here, `demo.div` fails when its divisor is zero, and
`demo.attempt` runs its region and fails with the error that the region returns:

```
func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
  requires {
    pre.0():
      %ok.0 : base.Bool = demo.attempt ^fail.0() {
        body.0():
          %q.0 : base.Int = demo.div(%x.0, %y.0) ^propagate.0()
          %b.0 : base.Bool = demo.ge(%q.0, 0)
          %v.0 : base.Except(base.Int, base.Bool) = base.ok[base.Int, base.Bool](%b.0)
          ret(%v.0)
        propagate.0(%exc.0 : base.Int):
          %err.0 : base.Except(base.Int, base.Bool) = base.error[base.Int, base.Bool](%exc.0)
          ret(%err.0)
      }
      ret(%ok.0)
    fail.0(%e.0 : base.Int):
      ret(false)
  }
{
  entry.0(%x.0 : base.Int, %y.0 : base.Int):
    ret(%x.0)
}
```

**`old` in `ensures` clauses.** An `ensures` clause reads the state at the call with the base's
`reads insn old [e a] (&body : Except e a) (^err (exc : e)) : a`. `base.old` runs its region in
the state at the call. If the region returns `ok(v)`, the operation returns `v`. If it returns
`error(x)`, the operation transfers to `err` with `x`, so a failure in the region gives the
clause's failure value. An object that it returns is the same object, and reading it afterwards
reads the state at the exit. A read, in the state at the call, of an object allocated during the
call is not well defined. An `old` nested in an `old` also runs in the state at the call. A
parameter of an enclosing region, such as a quantifier's binder, may hold a value of the state at
the exit, such as an object that the call allocated; an `old` that reads that object is then not
well defined. A value that the region uses from outside it keeps its value, so the result of
`base.old` is a value of the state at the call only when its region uses no such parameter. An
object that the region allocates is new at the exit too: it is none of the objects of the state at
the exit, and it holds there what the region gave it. The checker asks two things of `base.old`:

* It appears only in an `ensures` clause, at any depth. The body, the `requires` clauses and the
  frame regions never apply it.
* Its region sees, from outside it, only the function's parameters, constants, and the parameters
  of the regions that enclose it in the clause, such as a quantifier's binder. It never sees the
  parameter of the clause's own region, which is the result, nor any other value that the clause
  defines outside the `old` region. An `old` nested in an `old` may also use the values of the
  enclosing `old` region, which that region computes in the state at the call. So only the
  outermost `old` regions are checked.

The rules for contract regions apply to the region of `base.old`: it applies no operation declared
`writes`, and, since the region may propagate, a failure in it may go to a propagating block,
which passes it on to the `err` successor of `base.old`. Here, the result is at least the contents
of the cell `%c.0` at the call:

```
  ensures {
    post.0(%r.0 : base.Int):
      %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
        old.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %w.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%v.0)
          ret(%w.0)
      }
      %ok.0 : base.Bool = demo.ge(%r.0, %o.0)
      ret(%ok.0)
    fail.0(%e.0 : base.Int):
      ret(false)
  }
```

**Frames.** A `reads` or `writes` clause is a frame. It names a set of *locations*, the mutable
parts of the program state. The base declares `base.Loc`, the type of a set of locations, and
`pure insn cellLoc [a] (cell : Ref a) : Loc`, the contents of a cell. A language adds operations
that give its own locations, such as an object's attribute. A frame lists entries, and names the
union of their sets:

* A cell entry, such as `%c.0`, names a parameter of type `base.Ref`. It stands for the contents
  of that cell.
* A *frame region* takes no arguments and returns a `base.Loc`. Like a clause, it sees only the
  function's parameters and its own values.

Each frame region runs in the state at the call, after the `requires` clauses returned true, so
it may rely on them. Its set is fixed at the call. A frame means this:

* `writes W`: at every exit, each location that existed at the call and is outside `W` holds the
  value that it held at the call. For Python, raising is an exit too, since it returns an `error`.
  The function may write a location outside `W` and restore it. `writes()` changes nothing.
  Without a `writes` frame, the function may change any location.
* `reads R`: every read that the call makes of a location that existed at the call is a read of a
  location in `R`. A caller learns nothing from it. `reads()` reads nothing. Without a `reads`
  frame, the function may read any location.
* A frame never constrains the state that the call allocates.
* An extern's frames are trusted. A defined function's frames are claims about its body.
* A frame region is a contract region, so a consumer relies on nothing from one that it cannot
  show well defined (**What clauses mean**, above). At such a call, the frame states nothing: the
  call may read or change any location.

The checker asks these things of a frame:

* A cell entry names a parameter of type `base.Ref`, and no two cell entries name the same cell.
* A frame region takes no arguments and returns a `base.Loc`.
* A frame region sees only the function's parameters and its own values, and the body sees none
  of its values.
* The rules for contract regions apply to a frame region: it applies no operation declared
  `writes`, each failure in it goes to a block that ends in `unreachable` (**Failures in
  contracts**, above), its blocks end in control flow and form an acyclic graph, and it does not
  apply `base.old`.

A frame region prints in braces among the frame's entries. Here, `demo.nth` gives the cell at
position `%i.0` of `%cs.0`, and fails when `%i.0` is out of range. The function may change the
contents of `%c.0` and of that cell, and no other location that existed at the call. At a call
where `%i.0` is out of range, the frame region is not well defined, so that call may change any
location:

```
func @m.f(%c.0 : base.Ref(base.Int), %cs.0 : base.Sequence(base.Ref(base.Int)), %i.0 : base.Int) -> base.Int
  writes(%c.0, {
    loc.0():
      %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^fail.0()
      %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
      ret(%l.0)
    fail.0(%e.0 : base.Int):
      unreachable
  })
{
  entry.0(%c.0 : base.Ref(base.Int), %cs.0 : base.Sequence(base.Ref(base.Int)), %i.0 : base.Int):
    ret(%i.0)
}
```

**Ghost state.** A *ghost* is a cell of the module that only contracts can name. A ghost has a
name, the type of its contents, and, each if it has one, an *initializer* and an *invariant*. The
constant `ghost @m.g` is the ghost's cell, a `base.Ref` of its type, and a contract reads its
contents with `base.refGet`. A ghost means this:

* The initializers run once, before any function, in the order the ghosts are declared. An
  initializer takes no arguments and returns the ghost's first contents. A ghost without one
  starts with some value that satisfies its invariant.
* The invariant takes the ghost's contents and returns a `base.Bool`. It is trusted (**The trust
  base**, above). The invariant holds in every state. An invariant that reads state other than
  the ghost's contents, such as the entries of a mutable object that the ghost holds, is a trusted
  claim about every call that may change that state. The first value must satisfy the invariant;
  if it does not, the trust base contradicts itself.
* A ghost changes only at a call whose `writes` frame covers its cell, or that has no `writes`
  frame.
* A ghost may hold a mutable object, such as a Python dict. Its cell is then one location, and
  the object's entries are others: a frame names them separately.
* An initializer and an invariant are contract regions, so a consumer relies on nothing from one
  that it cannot show well defined (**What clauses mean**, above). The first value of a ghost
  whose initializer is not well defined is unknown, and an invariant that is not well defined in a
  state states nothing there.

The checker asks these things of ghosts:

* No two ghosts share a name, and no ghost has the name of a function of the module.
* Each `const ghost @m.g` names a ghost of the module, and the value it defines has type
  `base.Ref(T)`, with `T` that ghost's type.
* Only contract regions name ghosts: a function's body never does, at any depth. The regions of
  a ghost are contract regions.
* An initializer takes no arguments and returns the ghost's type. An invariant takes one argument
  of the ghost's type and returns a `base.Bool`. Each sees only its own values.
* An initializer names only the ghosts declared before its own. An invariant names no ghost: it
  receives the ghost's contents as its argument.
* The regions of a ghost refer to no function of the module, at any depth.
* The rules for contract regions apply to an initializer and an invariant: it applies no operation
  declared `writes`, each failure in it goes to a block that ends in `unreachable`, its blocks end
  in control flow and form an acyclic graph, and it does not apply `base.old`.

A function's attribute may name a ghost of the module, as `ghost @m.g`. Naming a ghost in an
attribute is not a use of the ghost by the function. Ghosts print first in a module, before the
functions. Here, `@m.tick` requires that the contents of `@m.count` are at least `%x.0`, and may
change only those contents:

```
module m {
  ghost @m.count : base.Int = {
    init.0():
      ret(0)
  } invariant {
    inv.0(%v.0 : base.Int):
      %ok.0 : base.Bool = demo.ge(%v.0, 0)
      ret(%ok.0)
  }
  extern func @m.tick(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %n.0 : base.Int = base.refGet[base.Int](ghost @m.count)
        %ok.0 : base.Bool = demo.ge(%n.0, %x.0)
        ret(%ok.0)
    }
    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](ghost @m.count)
        ret(%l.0)
    })
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

Blocks and transfers are typed too. `Emit.freshLabel ps` gives a block whose parameters have
the types `ps`, and a successor takes a target that still expects its payload. `Emit.func`
emits a function, giving its body the parameters and the function's exit, as a region's body is
given its region's. The builder rejects a typed exit used where it does not leave the innermost
body being emitted. For example, this function returns its argument through a block:

```lean
Emit.func (n "first") [(n "x", Base.Int)] Base.Int () fun (.cons x .nil) exit => do
  let% done ← Emit.freshLabel [Base.Int]
  Base.jump (done.goto.bind x)
  Emit.ret exit (← Emit.startBlock₁ done)
```

The untyped layer below, `Build.Raw`, takes bare labels, for a front end whose types are known
only when it runs.

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
  `false`, a string `"…"`, the unit `unit`, a function pointer `@m.f`, and a ghost's cell
  `ghost @m.g`.
* **Attributes** of a function print below its signature, one `#[key = value]` line each,
  then a blank line. A value is a literal, a list `[v, …]` or a record `{k = v, …}`, and a
  key is prefixed by the front end that gives it its meaning, such as `py.` for Python.
* **Contracts** print between the signature and the body: `requires` clauses, `ensures`
  clauses, then the frames. A frame lists its entries: cells, and regions in braces, as in
  `writes(%c.0, { … })`. The body's brace then opens a line of its own. A clause's message
  follows its keyword, and a free clause is written `free ensures`. An **extern** prints as
  `extern func`, its signature and its contract, with no body.
* **Ghosts** print before the functions: `ghost`, the ghost's name and type, then its
  initializer after `=` and its invariant after `invariant`, each a region in braces:
  `ghost @m.count : base.Int = { … } invariant { … }`.
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

The pass changes only a function's body. The function's parameters, its contract and whether it
is extern stay as they are, and a cell that a contract region makes is not promoted. So an
extern function, which has no body, stays as it is.

### What the pass keeps

`StrataDyn/RefToRegSound/` proves that a target that promotes its source's cells keeps the
source's behaviour, for a model whose rules are certified (§5, "Certificates").
`refToReg_sound_cell` takes a source module linked and validated, a well-formed linked target,
and the hypothesis `PromotionOK lm lm₁`: the linked target promotes the linked source's cells,
block by block, as the certificate in `RefToRegSound/Cert.lean` describes it. For every start of
a function on arguments that hold no ref, every observation of the world and every oracle, the
target's run improves on the source's run under the same oracle, up to a bad cell: the two runs
show the same, or the source faults with a bad cell after showing what the target also shows.
This is trace refinement under one oracle (`Exec.OracleRefines`, §5, "Trace refinement"), and
the only wrong result it excuses is a bad cell. Promotion keeps every choice, so the oracle is
shared. `refToReg_sound` is a weaker corollary, which excuses every wrong result of the source:
a failed rule or a bad call as well as a bad cell.
When no rule of the linked source stops with a bad cell itself (§5, "Heap safety"),
`refToReg_sound_eq` gives equal behaviours under every oracle, and `refToReg_sound_runs` that
every run of each behaves as some run of the other. `WhileCert.refToReg_sound_while` states
`refToReg_sound_cell` at While's table. These theorems observe the world, not how many choices a
run makes: the simulation behind them keeps that number too, but the behaviour does not record
it.

The theorems hold for any target that `PromotionOK` relates to the source, and do not mention
the pass. That the pass's output, linked, satisfies `PromotionOK` is the static half of the
proof, which relates `refToReg`'s plan, through linking, to the linked code. It is not yet
proved; proving that `refToReg` establishes `PromotionOK` is the next step. The second rule
above, "an operation reaches only the cells it is given", is not assumed: it is the model's
certificate, which linking carries to every instruction of the linked module (`link_rulesOK`).

The certificate tracks, at each point of a block, facts relating the source frame to the target
frame: a target value holds a source value, or a promoted cell's content, and a source value is
a promoted cell. A value an `eq` fact names is valid in the source heap's typing without the
promoted locations, so it holds no promoted cell. So a `refGet` or `refSet` of a cell that is not
promoted stays, with a cell operand that an `eq` fact relates to the source's, also when the
function did not allocate the cell, as for a parameter or a closure's captured cell. A rule's
certificate holds at that typing too, so the rule asks for no promoted cell, and the source and
target heaps, which agree off the promoted cells, answer it alike. An operation with regions
names the promoted cells its regions may write; its regions read the contents of the others.


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
stands for no behaviour rather than an error, and a run reports it as its outcome. The other
faults are the machine's, and a table rejects a rule that stops with one ("Running as proved",
below). `chooseNat` asks the run's oracle for a number, `choose n` for one from `0` to `n`, which is the oracle's
answer reduced, and `chooseInt` for an integer, which numbers the integers `0, -1, 1, -2, …` by
the oracle's answer. A choice is internal nondeterminism, which a translation may resolve (§5,
"Trace refinement"); input from the environment is a world request. A rule takes no fuel: the
machine runs its requests as steps.

Rules are trusted: a rule is what its instruction means. Registration checks a rule's type
against its instruction's signature and the capabilities it takes, and that no instruction has
two rules, and each table checks every rule again at its own type rules. Each table also
checks that its rules run as they are written: the code that runs is the definition that
proofs read ("Running as proved" below).

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
semantics that must tell two types apart gives them distinct Lean types. Each type rule must unfold
to an inductive or structure type with no index, a constructor and no axiom but Lean's three, or to
an opaque type of Lean's library (an opaque constant of ours fails the check of what a table runs),
in `Type`, applied to exactly its parameters, which are types; and two type rules must unfold to two
such types, neither `Ref` nor `FnRef`. The engine's `NoLoc` is the one type with no constructor
allowed. So a `def` of `Int` beside `Int`, a `def` of `Array Int`, `def K (_ : Type) := Nat`, a
`Subtype` or `Fin 3` is rejected, and a rule wraps such a type in a structure. Otherwise a rule
could read a cell made at one tag through another whose Lean type is equal by definition or by
proof, with a `cast`. The check trusts that Lean, with `propext`, `Quot.sound` and
`Classical.choice`, proves no equality between two types built from different type constructors, or
from one at different type arguments. No such proof is known; the belief rests on a model of Lean in
which each type carries its constructor, a variant of the set-theoretic model in M. Carneiro, "The
Type Theory of Lean" (2019), that has no published proof; for types with no value, such as a
structure with a field of type `False`, only that type-level form of the model keeps them apart. The
check rejects types without constructors, except `NoLoc`, only as a cheap guard: a type whose
constructors can't be filled passes, and rests on the same assumption, that distinct type
constructors are never provably equal. Nor may a type rule's values hold a `Fault`, in a field or
behind a definition in a field's type, so that a rule can't stop with a fault that only the
machine reports and that it was given.

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
world it read earlier, whole. Each of the three is one `update` request: the machine takes the world
out of its state and hands it to the request, which returns the new world, so a part that
`modifyThe` updates is held by nothing else. A part's laws are `LawfulHasPart`, which a proof about
a rule takes as hypotheses; a table doesn't require them. Reading after writing gives what was
written, writing what was read changes nothing, and the second of two writes wins. `#dyn_world W`
derives each field's part and its laws, and, for each ordered pair of parts, that writing the first
leaves the second as it is (`HasPart.Indep`):

```lean
structure World where
  out : Output := {}
  ticks : Ticks := {}
  deriving Inhabited, Repr, DecidableEq

#dyn_world World

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

### Running as proved

`#dyn_sem_table` checks the code that its rules, its wrappers, the world parts' instances and
its initial world reach, and fails at the first finding, which names the rule. Examples, from
`StrataDynTest/Exec/RuleErrorTest.lean` and `TableCheckTest.lean`:

| Rule | Error |
|---|---|
| `xs[i.toNat]'sorry` | rule sorried for err.sorried reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound |
| `pure (viaSlow x)`, with `@[implemented_by spin] def slow` | rule fast for err.fast reaches slow (fast → viaSlow → slow), which carries @[implemented_by spin]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead |
| `Helpers.hiddenLie x`, from another module that does not expose it | the table HiddenSem: rule hidden for tcHidden.f reaches Helpers.hiddenLie (HiddenSem.ops → … → hidden → Helpers.hiddenLie), whose definition its module does not expose, so the check cannot see it: mark it @[expose], or, for a derived instance, derive it in an @[expose] section or write it by hand |

`#dyn_check_rule E.o` runs the same check on the rule of `E.o` alone, in its own module's view.
That view sees the module's unexposed bodies and compiled code, which a table in another module
doesn't, so only the table's check decides. Registration itself checks a rule's shape only.

A rule's meaning is its definition, so the code that runs must be that definition; otherwise a run,
or a comparison of runs with another implementation, tests other code than proofs see. So a rule may
reach no axiom other than `propext`, `Classical.choice` and `Quot.sound`, even inside a proof: such
an axiom proves anything, so a theorem about the rule would say nothing. Nor may it reach, outside proofs, propositions and predicates, which
never run, a definition outside Lean's `Init`, `Std` and `Lean` that runs other code than its body
(`@[implemented_by]`, `@[extern]`, `@[init]`), keeps its body from proofs (`opaque`, or `partial`,
whose loop proofs see as an opaque constant, so a run that never ends would look like one that ends;
a loop that may not end goes through `again`, which the machine runs step by step), or whose
module does not expose its body to the rule's module. A `noncomputable` or `unsafe` rule has no
code, so no table can compile it (`NcSem`, `UnsSem` in `RuleErrorTest.lean`). Lean's library is
trusted. A fast version of a definition is swapped in with a `@[csimp]` lemma, which proves it
equal; the check looks at the lemma's axioms and the code it swaps in. A `local` `@[csimp]` lemma
leaves no trace once its scope ends, so every constant `@f = @g` of a definition `f` that a rule
reaches must be a theorem proved with those axioms, as must the lemmas of `g`, of their targets, and
so on along the chain (Lean applies swaps one after another), and the compiled code of each of our
definitions may call only what its own definition reaches. The table checks its initial world and
the world parts' instances the same way. Outside proofs, propositions and predicates, which never
run, a rule may also not see where a ref's cell or a closure's function is (`Ref.loc`, `FnRef.idx`,
`FnRef.captured`, the fields of `Ref.Raw` and `FnRef.Raw`, a match on them, or a request taken from
a heap or call capability that the rule built itself): a pass that removes or renumbers cells must
not change a rule's result. Nor may it build a `Ref.Raw` or `FnRef.Raw` itself: a ref's validity is
a proof, but at the machine's own token it is `True`, so a rule could point a ref at any cell, or
rebuild a closure with another closure's captures. Nor may it build or take apart a machine request
(`MReq`), which holds locations: only the handles that a table passes to it build requests, only the
machine reads them, and only the
declarations that a table emits may name `Region.slot`, `HasHeap.mreq` or `HasCall.mreq`. Every
error names the rule, or the initial world, and, except for an axiom found inside a proof, the path
to what it reaches. Equality of refs and of closures stays allowed, since it shows nothing of where
they are, and so do `MReq.Out`, which computes only a type, and `MReq.writesCell`, whose one bit
depends only on a request's constructor. A name that the check trusts this way must still run its
definition: a `@[csimp]` swap of it, or of a request's or a ref's constructor, field or eliminator,
which its code uses, is rejected. Nor may a rule build a ref or a closure from a raw one
(`Ref.mk`, `FnRef.mk`): wrapping a ref's raw cell at another type (`⟨r.raw⟩`) would give it
another type than the machine made it at; only the declarations that a table emits use them. Nor
may a rule stop with a fault that only the machine reports (`badCall`, `badCell`, `outOfFuel`,
`missingRules`, `invalid`, `noFunction`): a case that the rules don't model stops with
`semanticGap`, and `semanticFailure` is only for a case the rule's author holds impossible. Lean's library is trusted by its modules' names, so a directory
of the search path, other than Lean's own, that holds a module named `Init`, `Std` or `Lean` makes
every check fail. A recursive definition is checked through the body it runs, and a hand-written
`_unsafe_rec` is rejected. Lean's library is trusted except for its loops that may never end: a `while` loop, a
`partial_fixpoint` definition, a fixed point of `WellFounded.extrinsicFix` (which a `for` loop over
`0...n` and many `String` functions run; `for i in [0:n]` loops without it), any `partial`
definition of the library, and `ST` code (`runST`, `runEST`, `Void.mk`, `ST.Prim.mkRef`), where a
cell that holds a closure can make a loop, are rejected too. `endingPartials` lists the library
loops that a rule may reach anyway, each with its reason: a name is eligible only if its loop ends
on every argument, because it runs over finite data that it receives, such as a string, never over
an iterator, a stream or a pattern that its caller supplies. A function that the caller passes, such
as `foldl`'s, runs once on each character and is checked as part of the rule. Today the list holds
`String.Slice.foldl`, `toNat?`, `toInt?` and `isNat`; `String.any`, `contains`, `find`, `replace`
and `split` search with a searcher that the caller's pattern chooses, and are rejected. A swap of a
listed name is rejected, as for every name the check trusts. A `module` file sees most of the
library only as axioms, so a table sees such a loop only where it is visible (it finds a range loop
by its instance's type); the recheck below sees them all, prints the first loop that each listed
name reaches, which its test pins, and reports a listed name that reaches none. Lean derives some
instances as `partial` (for a nested or mutual type, and `Ord` for a recursive one), so a rule that
needs one writes it by hand.

The check reads Lean's compiler data: the `@[csimp]` entries, each definition's `_unsafe_rec`, the
compiled code and the attributes. It checks that a `@[csimp]` entry's lemma states that its two
functions are equal, and that an `_unsafe_rec` comes from a recursive definition, as Lean's
equation info records (`ForgedEntryTest.lean`). Meta code in a rule's module, or in a module it
imports, could still write any of this data directly, and no check of the environment can rule
that out, as Lean itself trusts its environment. So the check trusts that these modules run no
meta code that writes compiled code or compiler data. A review of a module with rules, and of every
module of ours that it imports, looks for such meta code: `run_cmd`, `run_elab`, `run_meta`, an
`#eval` of a `CommandElabM`, `TermElabM`, `MetaM` or `CoreM` action, and our own elaborators.

The check sees a `local` swap that another module made with a public lemma: it follows the
lemma. It may also see a swap whose code the rule's compiled code inlines: it does when that
code calls one of our definitions that the rule's definition doesn't reach. But in a `module` file, a table can't
see another module's private declarations, so a swap whose lemma is private there, or in a
module imported only privately, is not visible to it otherwise, and nor is another module's
`@[init]` attribute.

The check covers the tables that `#dyn_sem_table` makes. A `Table` or `Model` built by hand,
or any other consumer that runs registered rules, must run the same check (`notAsProved`).

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
`Fault`. `runModule` runs the fused engine, `runFused`, which counts fuel in fused steps. A
fused step performs a transition and the edges, entries and world requests it decides, so a run
takes fewer fused steps than steps of `step`. Section 5 relates the two.

`startCore hw i args snap` starts function `i` from a snapshot, by default `Snapshot.initial`,
an empty heap and the initial world. A module's top level can run first, and a function of the
module then from `o.snapshot`, the heap and the world where the top level ended
(`StrataDynTest/Exec/HeapTest.lean`). One value holds both, so a run cannot start from one
run's heap and another run's world.

A run ignores contracts and ghosts, and a module with an extern function does not run yet:
`runModule` rejects it with `Fault.invalid` (`StrataDynTest/Exec/BaseTest.lean`).

### Certifying a table: `dyn_cert`

A rule is an ordinary Lean function, generic in the run token, and Lean does not prove that it
is parametric: a rule can still build a ref at the machine's token classically. Proofs about
runs that rely on rules reaching only what they are given, such as ref-to-reg's, therefore need
the table to be *certified* (§5, "Certificates"). A language certifies its table in two steps.

First, `Accounts M` (`StrataDyn/Exec/CertModel.lean`) gives the *account* of a value of each
tag: the cells its refs name, at their contents' tags, and the captures cells of its closures.
It also gives the accounts of the world and of each rule's state. A ref's and a closure's
accounts are fixed by the engine, and the literals that link hold none: linking rejects a
ghost's cell, `ghost @m.g`, outside a contract. An account that leaves refs out
makes the certificates of the rules that reach them unprovable, so it fails safe.

Second, `dyn_cert` proves each operation's certificate. It unfolds the wrapper, the rule, the
rule's helpers and the language's class, then takes the goal apart with `Spec.Sat`'s lemmas,
splitting each `if`, `match` and `Bool`. `dyn_cert [h₁, …]` adds the accounts' definitions,
which it unfolds by reduction, so an account at a known tag is computed. When goals are left,
it fails and shows them, each a request, result, exit or world it could not show valid.

`#dyn_certs S A [h₁, …]` runs `dyn_cert [h₁, …]` on every operation of table `S`, each as its
own theorem: `cert.op : S.model.OpCertified A k S.impl.op` for the operation `op` at position
`k`. It then proves `cert.ops`, that the operations of `S.ops` are certified, from those
theorems alone, so the table's certificate does not elaborate the operations' proofs again.
Lean elaborates the operations' proofs in parallel, and a proof that fails names its operation.
An operation whose `cert.op` is declared before the command, with a proof written by hand, is
not proved again. While's certificate (`StrataDyn/Examples/While/Cert.lean`) is:

```lean
#dyn_certs WhileSem accounts [accounts, acct]

theorem certified : WhileSem.model.Certified accounts :=
  Model.certified_of_ops cert.ops
```

A table rejects a rule that gives a ref another contents' type (`Ref.mk` is banned in rules), so
no certified table has one. `CertTest` builds such an operation by hand, as a table would build it
from the rule `⟨c.raw⟩`, and shows that it is not certified (`retype_not_certified`). `dyn_cert` does not prove the certificate
of a rule that builds a closure over a list of cells, such as `ex.mkClo`, which has the shape of
Python's `mkClosure`: such a rule needs a hand-written certificate, with a lemma for `bindAll` by
induction on the list; this package has none yet.

## 5. Reasoning about runs

This section is about proofs over the runs of linked modules: what a run does when it never
ends, how the behaviours of two modules compare, and what a run of a certified table may touch.

### Runs and behaviours

A module's machine is `step`, a function of the module, an oracle and a state. What the module
does is the set of its runs. `StrataDyn/Exec/Trace.lean` defines its step relation,
`StepRel hwf`, which steps wherever some oracle does, and `RunFrom hwf s h`, the runs of that
relation from `s`. A run is a configuration at every time: running in a state, `.running ⟨s₁, h₁⟩`,
or ended, `.ended ⟨result, snapshot, drawn⟩`, which every later time keeps. A run answers each
choice freely, and its behaviour does not record how. No theorem takes fuel, so runs that never
end are covered.

* `Reach hwf s h p` holds when steps of the module lead from `s` to `p`.
* `Diverges hwf s h` holds when some run from `s` never ends.
* `always` proves a property of every configuration of every run from a property of states that
  each step, under every oracle, preserves and a property of how runs end that each final step
  establishes. A proof about a module states its fact for one step under one oracle, and
  `always` gives it for every run.

A run's behaviour, `behW hwf obs run`, is what an observer of the world sees. At each state the
observer records `obs` of the world, and drops a record equal to the one before. The behaviour
has three forms. `.term t x` is a run that ends with the result `x` after the records `t`.
`.silent t` is a run that never ends and records nothing after `t`, such as `while (true) { }`.
`.react σ` is a run that never ends and records without end, such as a loop that prints. Neither
the heap nor the choices made are part of the behaviour. A later run started from the run's
snapshot reads the heap. `behW hwf obs run` is the library's `run.beh (obsW obs) Final.result`.

`Trace.Run.beh_extends_iff` says that the finite prefixes of a behaviour are exactly the prefixes
of `run.obsUpTo (obsW obs) n` for some `n`, and `Trace.Run.beh_ended` that a run that has ended
after `n` steps behaves as `.term (run.obsUpTo (obsW obs) n) x`, where `x` is its result.

### Trace refinement

To compare two modules, a translation and its source, `Trace.Improves wrong b₁ b` holds when the
target's behaviour `b₁` is the source's `b`, or `b` ends with a wrong result after records that
`b₁` extends. For Dyn the wrong results are `Result.Wrong`: the faults `failure`, `badCall` and
`badCell`. `blocked` and `gap` are not wrong, so a target run that blocks must match a source run
that blocks after the same records, or a source run that goes wrong after records that the target
run's extend. Trace refinement, `Exec.Refines hwf hwf₁ obs wrong c c₁`, takes the source `c`
first and the target `c₁` second, and says that every run of the target improves on some run of
the source. It constrains only the target's runs: a target that blocks at once refines a source
with some run that blocks at once, though the source's other runs do not block.

**What `choose` means.** A choice is internal nondeterminism: freedom that the implementation
has, such as an unspecified order, a hash seed or a havocked value. Trace refinement picks the
source's answers to match the target's run, so a translation may resolve a choice, drop it or
move it: `x := choose; print(x)` compiled to `print(5)` refines its source. Input from the
environment must come through the world (`update`), which is observed, and a translation must
keep it. So `input()` or the time of day is a world request, not a `choose`.

Trace refinement over runs lets a source run that goes wrong early excuse every target run
whose records extend it, whatever choices the target made. A translation that keeps every choice
as it is proves more, trace refinement under one oracle (`Exec.OracleRefines`): under every
oracle the target's run improves on the source's run under the same oracle. Then the source going
wrong on some answers excuses the target only on those answers. `OracleRefines.refines` gives
`Refines` from it. `refines_iff` states `Refines` with oracles: for every oracle of the target,
some oracle of the source.

Trace refinement over a relation says nothing of a target state with no step, since such a
state has no run (`Trace.Total`). Dyn's relation is total (`stepRel_total`), and its faults are
outcomes, not stuck states. `Refines.trans` composes the trace refinements of two passes, and
`OracleRefines.trans` the trace refinements under one oracle of two passes that keep choices.

`StrataDyn/Util/Trace.lean` states runs, behaviours and trace refinement for any step relation,
and gives three ways to prove trace refinement:

* `Sim`, a forward simulation of a step function by a step function, with a measure: every
  source step is matched by target steps, or by none and the measure decreases (`Sim.refines`).
  Under one oracle, Dyn's machine is a function, so a translation that keeps choices one to one,
  such as ref-to-reg, proves a `Sim` under each oracle, and `Exec.oracleRefines_of_sim` gives
  trace refinement under one oracle.
* `BSim` and `BSimStep` (`StrataDyn/Util/Trace/Backward.lean`), backward simulations. With
  `BSimStep`, the proof takes each target step from related states and gives source steps to a
  related state, or no source step and a smaller measure. The source steps and their answers to
  choices are chosen by the proof, so a translation may drop or move a choice. `BSim` is the form
  in which each match takes one or more steps on each side, and `BSimStep.toBSim` converts.
  `StrataDynTest/Util/ChoiceTest.lean` proves that dropping an unused choice refines its source
  this way.
* `RunMatch`, a forward matching of two given runs, to which the other two reduce.

### Computing a run

The run under one oracle, `oracleRun hwf oracle s h`, is one of the runs. Its configurations,
`trace hwf oracle s h n`, compute, so a prefix can be checked with `#guard`. What its first `n`
steps show is computed in one pass by `obsTrace` (`oracleRun_obsUpTo`); evaluating `obsUpTo` of a
run directly recomputes the run at every step. `StrataDynTest/Exec/TraceTest.lean` checks
prefixes of While programs this way, and proves the three forms of behaviour for small machines.

Every run is the run under some oracle (`complete`), so a state has a run that never ends iff
some oracle's run never ends (`diverges_iff`).

`StrataDyn/Exec/Fused.lean` proves that the fused engine follows the runs. `runFused` on `n` fuel
under an oracle stops or ends at the configuration that the run under that oracle has after some
`t ≥ n` steps (`runFused_eq`), so every state at which it stops can be reached
(`reach_runFused`). When it ends, the run under that oracle ends with the same result, snapshot
and choices, and behaves as `.term` with that result (`beh_of_runFused`). A run that has ended
after `n` steps, `runFused` under its oracle ends on `n` fuel (`runFused_of_run`). Some run never
ends iff, under some oracle, `runFused` runs out of fuel on every fuel (`diverges_iff_fused`).
`runFused` runs a rule's world updates in one step, so it does not stop between them. A
debugger's hook runs `step`: one that only observes ends at the configuration of the run under
its oracle (`runHooked_observer`), and a run that it stops and `runFused` resumes ends at a
configuration of the uninterrupted run (`runHooked_resume`).

### Certificates

A rule's *certificate* says that it reaches only the cells and captures cells it is given. Every
ref and closure the rule hands the machine, in a request, a result, an exit or the world, is
valid in the typing of the heap at that point, whenever everything the machine handed it was. A
typing does not record which function a closure names or at which signature: the machine checks
that at every call.

`StrataDyn/Exec/Spec.lean` states what a tree may do once for every proof about a rule. A
`Spec G ε E` says, at a ghost state `g : G` (a value that only proofs carry, not a module's
ghost of §1), which requests a rule may make, which answers it
may get, which worlds the machine may hold and which exits the rule may take. `Spec.Sat V Q g t`
says that the tree `t` makes only allowed requests and, under allowed answers, returns a value
`Q` holds of or takes an allowed exit. The simp lemma `sat_bind` takes a goal through a `do`
block, and `RegionSpec.sat` through a region.

For certificates the ghost state is a typing of the heap, `Typing` (`StrataDyn/Exec/Cert.lean`):
a tag for some cells and tags for some captures cells, which grows by extension.
`Accounts.spec` is the machine as a rule's tree sees it, over typings and the accounts of §4.
`Model.Certified M A` says that every wrapper respects every typing under which its operands are
valid. `link_rulesOK` carries it to every instruction and terminator of a linked module,
`LModule.RulesOK`. It is an instance of `link_inv` (`StrataDyn/Exec/LinkInv.lean`), which carries
any property of linked instructions that the table's wrappers give, and that the instructions
linking makes with no wrapper have, to every function and region of a linked module.

### The frame theorem

`StrataDyn/Exec/Frame.lean` proves that a run of a module whose rules are certified leaves alone
what it cannot reach. `Reachable A heap roots` is the set of locations reached from a list of
roots, through the accounts of the cells and captures cells reached. The run invariant, `Inv`, is
a typing of the heap that misses a set of locations `P`, in which every value of the state is
valid. Every step keeps it at an extension of the typing (`step_inv`), so `frame` says that at
every configuration of every run, and at the end if there is one, the cells at `P` are as they
were. `frame_startCore` starts the run at a function's entry, with `P` unreachable from the
arguments and the world.

`StrataDyn/Exec/Call.lean` states the same for one call. A step never reads the frames waiting
below the running ones until the bottom one returns, so every run of a call is, until the callee
returns, a run of the callee from `bodyStart` with those frames below (`run_call`, which gives a
`CalleeRun`; under one oracle it is an equality of traces, `trace_call`). `frame_call` says that
every run of a call keeps the cells the callee cannot reach, along each of its callee's runs,
until it returns and when the caller resumes (`CallKeeps`). A fact proved of every run of the
callee holds of the same callee run. `frame_call_of_run` applies `frame_call` at a pending call
that a run reaches from a state where the run invariant holds, such as a function's start, and
`StrataDynTest/Exec/LinkedCallTest.lean` uses it on two While functions that go through `lower`
and `link`.

### Heap safety

A run of a module whose rules are certified uses only the cells it may
(`StrataDyn/Exec/Safety.lean`). Every ref the run holds is valid in a typing of the heap, so
every access that the machine checks finds a cell of its tag (`access_ok`). A certificate says
nothing of faults. A table rejects a rule that stops with `Fault.badCell` itself, but a module
linked by hand has no such check, so the theorem takes `LModule.Avoids`, which says that no rule
of a linked module does. With it, `never_badCell` says that no run from a state
where the run invariant holds faults with a bad cell at any configuration or ends with one.
`never_badCell_startCore` starts it from a function's entry, on arguments that hold no
ref, from the engine's start or from the snapshot where another run ended. A typing does not
record the function a closure names, so `Fault.badCall` is not covered.
`StrataDynTest/Exec/SafetyTest.lean` proves it for a module linked by hand at While's run
model, in which no rule's tree runs: its instructions are the machine's own and its terminators
are returns. Nothing yet proves
`LModule.Avoids` for a module that `link` makes from a table.

## 6. Dyn types in Core

A translator that emits Core needs Dyn's types as Core types. `StrataDyn/Core/Types.lean`
translates them, and nothing else: no values, operations or control flow.
`StrataDyn/Core/Denote.lean` proves that the translation preserves meaning.

### Policies

A policy chooses how each primitive type is represented in Core: as an uninterpreted Core type
constructor applied to the translated arguments, or as a Core type built from them, such as
`Int` as Core's `int`. A policy sees a primitive's name and parameters only, not its
annotation, so a representation cannot depend on metadata. A type whose values can fault, loop
or write the store should stay opaque: the example policy represents the function type as one
nullary Core type, `Closure`, and leaves calls to the value lowering.

Datatypes are not the policy's choice. A group whose members have a Core form becomes one Core
datatype block, with binders the translation derives from recursive references and aligns
across the group. Members may name or order their type parameters differently, but the aligned
parameter sets must be identical, including unused parameters, and each member's parameters
must remain distinct. Non-recursive members with different parameter sets belong in separate
groups. A group without a Core form has no block; the checker below reports why.

### Translation and checking

Translating a type cannot fail: every checked Dyn type expression has a Core type under a scope
that says what its variables stand for, and `compile` lists an environment's Core type
declarations in declaration order, leaving out groups without a Core form. Whether the
environment is supported is a separate question, decided by `checkEnv`: it walks the
declarations, extends a Core context with each as Core's declaration rules would (datatypes,
known types and the generated datatype functions; registering the names as program identifiers
is the embedding program's step), and either returns the final context with a proof of support
or names the first declaration that fails. It rejects a list parameter on a nominal type, since
Core's constructors have a fixed arity (a list parameter is fine where a concrete
representation consumes it); an empty datatype; a group whose members cannot share binders,
because the alignment identifies two parameters of a member or leaves different parameter
sets across members, which Core's declaration checker also forbids; a Core name already taken;
a concrete representation using a constructor the context does not know at that arity; and the shapes
Core's own datatype checker refuses, such as nested or non-uniform recursion, uninhabited types
and non-positive occurrences. Support certifies Core's declaration checks, not that the
generated functions typecheck; the tests check that as well. Emitted names are readable and
injective: `base.Except` becomes `$dyn.type.base.Except`.

### Types for signatures and instantiations

For an instruction signature without list parameters, open a generic scope over its type
parameters: it gives each a Core type variable, which every type of the signature shares, and
`scheme` closes a translated type into a Core type scheme quantified over them. A signature
with a list parameter has no generic scope, since a list cannot be a Core type variable. For an
instantiation, build a scope from the consumer's Core arguments, which are checked once for
count, kind and well-formedness in the context; translating under it substitutes them, splicing
list arguments into list literals. That every constructor a translation relies on is present in
the context the checker builds is not yet proved; until it is, consumers take the union of the
two signatures.

### What the proofs say

Dyn types have a direct meaning as Lean types, independent of Core, with the meaning of each
constructor supplied as a parameter. This is not yet the run-time semantics of §4; connecting
the two, the function type included, is a later step. Translation preserves meaning under two
assumptions: each constructor's Core representation agrees with its supplied Dyn meaning,
nominal datatypes included, and the variable assignments on both sides agree. This holds for
every type expression, type-list splices included, and also in Core's own denotation when its
custom constructors are interpreted compositionally. Each emitted datatype agrees with its Dyn
declaration for one unfolding, with recursive occurrences interpreted by arbitrary carriers;
relating the recursive types themselves is left to the implementation translator.
