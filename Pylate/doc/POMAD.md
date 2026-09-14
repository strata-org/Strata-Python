# POMAD: Python Object Model Abstract Domain (FUTURE WORK)

> POMAD is the abstract mathematical object: the abstract domain itself. **Pylate**, the
> Python lattice engine in this package implements the pomad.
>
> Pylate today implements the version of POMAD in which admission checks ensure
> the class layer is fully static, every declared class's shape and MRO are
> fixed at their declarations, and a program that would change either is rejected
> rather than analysed. That is what makes the current engine sound without a
> metaclass layer.
>
> This document outlines the future work to extend POMAD to support more dynamism
> at the class layer and at the metaclass and decorator layers, which is what would
> let those admission checks be relaxed.

## 1. Contents

In this document we describe POMAD, an abstract domain for the Python object model and its control transfer. We describe the parts of the concrete semantics that dispatch, exception behaviour and control transfer depend on: the object model and the workload the analysis has to admit (§2.1), and the completion of expressions and statements (§2.2); record the design decisions with the alternatives considered (§3), including the representation of control transfer (§3.7), the treatment of `finally` and the granularity of completions (§3.8), the error policy for machine-raised exceptions (§3.9), the encoding of a dispatch site (§3.10), the representation of values (§3.11), object shape (§3.12), instantiation under an uncertain class (§3.13), contracts and summaries (§3.14), the representation of collections (§3.15), the evaluation of comprehensions (§3.16), hashability (§3.17), the naming of cells stored into static slots (§3.18), and the unrolling of bounded loops (§3.19); specify the resulting domain: cells and values (§4.1), the two-level hierarchy abstraction and its order domain (§4.2), attribute resolution (§4.3), calls and operators (§4.4), the transfer of completions through statements (§4.5), exceptions, handler matching, the narrowing at handler entry and the error policy (§4.6), the combination with the value domains (§4.7), the origin, restriction and encoding of candidate class sets (§4.8), object storage and the rigid-shape rule (§4.9), the execution of class statements (§4.10), calls, summaries and contracts (§4.11), callables and decorators (§4.12), scopes and closures (§4.13), collections (§4.14), comprehensions (§4.15), hashability (§4.16), default arguments (§4.17), unpacking (§4.18), operators and protocols (§4.19), signature binding (§4.20), and string formatting and the builtin models (§4.21); state the soundness argument (§5.1), the admission rules it rests on (§5.2), the precision limits (§5.3), the termination and cost argument (§5.4), and the feature coverage with its deferrals and rejections (§5.5); give the staging of the sources of uncertainty and the validation method for each stage (§6); and, in an annex, describe how the interpreter becomes generic over languages and whether it is syntax-directed or graph-based (Annex A), and, in a second annex, specify the taint component and distinguish the property it establishes from information-flow security (Annex B).

## 2. The concrete semantics

In this section we describe the object model and the workload the analysis has to admit (§2.1), then the completion of expressions and statements and the routing rules of the compound statements (§2.2).

### 2.1 Objects

In this section we describe the parts of CPython's object model that dispatch and exception behaviour depend on, then the workload the analysis has to admit.

Every object carries an `ob_type` pointer to a class object. A class object is itself an object: its `ob_type` points to `type` or to a metaclass, and `type` points to itself. A class object holds `tp_bases` (the declared bases), `tp_mro` (the C3 linearization of its ancestors, a tuple of class pointers), and `tp_dict` (its namespace). An instance holds either a dictionary or, for a class with `__slots__`, a fixed array of fields addressed through member descriptors stored in the class dictionary.

Attribute lookup on an instance (`object.__getattribute__`) walks `type(o).__mro__` for the first dictionary containing the name. If that entry is a data descriptor (its own type defines `__set__` or `__delete__`: a `property`, a slot member), the descriptor's `__get__` is the result. Otherwise the instance's own storage is consulted; if it lacks the name, the entry found on the MRO is the result, with `__get__` applied for non-data descriptors (a function becomes a bound method); if nothing was found, `__getattr__` is tried when the class defines it, and AttributeError is raised otherwise. Attribute lookup on a class (`type.__getattribute__`) has the same shape one level up: data descriptors on the metaclass's MRO, then the class's own MRO walk, then non-data entries on the metaclass's MRO. Calling any object dispatches through its `ob_type` in the same way: `C()` runs `type(C).__call__`, which invokes `C.__new__` and `C.__init__`; `w()` runs the `__call__` found on `type(w)`'s MRO. Binary operators consult a method on `type(a)` and a reflected method on `type(b)`, with the reflected one tried first when `type(b)` is a strict subclass of `type(a)` that overrides it. `except Y` matching tests `Y` against `type(exc).__mro__` directly; `isinstance` and `issubclass` additionally go through the metaclass's `__instancecheck__` and `__subclasscheck__`, which is how `ABCMeta.register` makes virtual subclasses without an MRO edge.

The workload contains class decorators (registration, `typing.final`, `functools.total_ordering`, `dataclass`), metaclasses that inject or read the namespace (`ABCMeta`, ORM field collection), classes chosen conditionally (`C = A if flag else B`), `__mro_entries__` substitution (`Generic[T]`), and, rarely, metaclasses that define `mro()`. An analysis that requires one fixed MRO per class has to reject every class statement carrying a decorator or a `metaclass=` keyword, and treats a conditionally chosen class as a different problem from a decorated one, although both are uncertainty about which class object a name refers to. The domain below treats the three layers (instance, class, metaclass) with one resolution rule and represents each source of uncertainty either as a points-to fact or as uncertainty about the order of one class's `tp_mro`.

### 2.2 Control transfer

In this section we describe how expressions and statements complete in CPython and how the compound statements route completions.

An expression completes normally with a value or abruptly with an exception. Sub-expressions are evaluated left to right (the receiver, then the arguments, then the call; the right-hand side of an assignment before its targets), `and`, `or` and the conditional expression short-circuit, and the first abrupt sub-expression ends the expression with its exception, leaving the effects of the sub-expressions before it in place. A statement completes normally, or with an exception, or with `break`, `continue` or `return v`. The compound statements route completions as follows.

- `try`: the try body runs; on an exception, the `except` clauses are tested in order and the first whose class expression names an ancestor of the exception's type runs its body; class expressions are evaluated lazily, clause by clause, at match time; `else` runs only when the try body completed normally, so a `break`, `continue` or `return` leaving the body skips it as an exception does; an exception raised in a handler or in `else` is not matched by the same statement's clauses; `finally` runs on every completion, and when it completes normally the pending completion is reinstated, otherwise its own completion replaces the pending one, so a `return` in `finally` discards a pending exception (the discarded exception becomes `__context__` of a new one). `except E as e` unbinds `e` on every exit from the handler, normal or abrupt. PEP 765 (Python 3.14) issues a warning for `return`, `break` and `continue` that exit a `finally` block, with an error planned.
- loops: `break` ends the loop normally and skips `else`; `continue` and normal completion of the body start the next iteration; `else` runs on exhaustion; an exception or a `return` leaves the loop without `else`.
- `with`: `__enter__` runs first; `__exit__` runs on every completion of the body; an exception is suppressed and the statement completes normally when `__exit__` returns a true value; an exception raised by `__exit__` replaces the pending completion.
- calls: `return v`, or falling off the end with `None`, becomes the value of the call expression; an exception becomes the exception of the call expression; `break` and `continue` cannot cross a function boundary.
- `except Exception` does not catch `SystemExit`, `KeyboardInterrupt` or `GeneratorExit`, which derive from `BaseException`; a bare `except:` catches everything. `yield` and `await` suspend the frame and add a third way for an expression to complete.

## 3. Design decisions

In this section we record each design decision with the alternatives considered and the reason for the choice.

### 3.1 Representation of a value's type

In this section we choose how the type of a value is represented.

Alternatives: (a) a set of type tags on each variable and heap cell, with one static MRO per tag; (b) a may-points-to set on the `ob_type` field, over a universe of class cells, with the class's MRO, namespace and metaclass abstracted as the content of the class cell.

We adopt (b). Under (a), a decorated or conditionally chosen class has no tag, since the tag is the class and the class is unknown; under (b) it is a may set on the `ob_type` edge, the same fact as `C = A if flag else B`. Under (b), narrowing at `isinstance` is a strong update of one edge and reaches every alias of the object through points-to, whereas under (a) every alias holds its own tag set and is narrowed separately or not at all. Under (b) the metaclass is the `ob_type` of the class cell and class-attribute reads through it are the instance rule applied one level up, so no second lookup mechanism is needed. The tag needed by the value encoding (the constructor of a `Val`) is recovered from (b) as the solid base of the target class, which is computed from `tp_bases` and therefore stays exact when the MRO does not.

### 3.2 Placement of class facts

In this section we choose where the facts about a class are stored.

Alternatives: (a) each abstract value carries the facts of its candidate classes; (b) class cells are ordinary cells in the per-state abstract heap; (c) class cells form a static graph built at class statements and referenced by identity, and the per-state heap holds only `ob_type` edges into it and the mutable values in class dictionaries.

We adopt (c). Under (a) the facts are duplicated in every value that may point to the class and joined at every merge. Under (b) they are flow-sensitive state, and every transfer function joins them although nothing changes them. The admission rules in §5.2 (no assignment to `__class__` or `__bases__`, class-dictionary key set fixed at the class statement) make the content of a class cell constant after its creation except for the dictionary values, so (c) loses nothing. The graph is built during module initialization and frozen before function bodies are analyzed. A class statement executed more than once (in a loop, or in a function called repeatedly) yields aged cells and a summary as an allocation site does (§3.5), and a summary class cell takes weak updates on `keys` and `values`. The two type edges live in different places because they change at different times: the instance-to-class edge (`type` on an instance cell) is per-state heap, since instances are created in function bodies; the class-to-metaclass edge (`meta` on a class cell) is part of the static graph, since a class object's `ob_type` is fixed at its creation, so the uncertainty of a metaclass is frozen uncertainty, exact per disjunct and a may set after a collapse (§4.2), never flow-sensitive state.

### 3.3 Abstraction of an uncertain MRO

In this section we choose the abstraction of the set of MROs a class may have.

Alternatives: (a) the unbounded set of candidate linearizations; (b) the strict partial order every candidate agrees on, with may and must ancestor sets; (c) two levels: a set of at most K exact class graphs, each assigning exact bases to every class so that its MROs are computed by C3 and a merge failure is a TypeError branch, collapsing to (b) per class when the set exceeds K.

We adopt (c). (a) is exact but factorial in the number of ancestors and has no bounded representation. (b) is quadratic, has finite height, its join is a bit-matrix intersection, and dispatch needs only the restriction of the order to the classes defining one name (§4.3), so a weak order still devirtualizes most sites; but it is non-relational across names (if one candidate resolves `f` and `g` from `A` and another resolves both from `B`, (b) admits `f` from `A` with `g` from `B`) and across classes (the order of `C`'s bases and the order of its subclass `D`'s MRO vary together, and (b) records each separately). C3 is a function of exact bases, so on the first level of (c) every lookup is exact, both correlations are kept, and an inconsistent hierarchy is a real branch at the class statement (§4.6) rather than a `⊥`. The sources of variation in the workload (a conditionally chosen base, a decorator returning a new class, a metaclass editing `bases`) each split the graph set in two, and a program has one or two of them, so K = 4 covers it and the collapse is rare. (b) is what a disjunct set collapses to: the α of §4.2.1 applied, per class, to the MROs of the disjuncts.

### 3.4 Resolution under uncertain ownership

In this section we choose how the candidate targets of a name are computed from the order.

Alternatives: (a) the candidates are the minimal elements, under the partial order, of the set of ancestors defining the name; (b) the candidates are the ancestors that may define the name and are not preceded by an ancestor that must define it and must be present.

We adopt (b). (a) is exact when the set of defining ancestors is known, and under-approximates otherwise: with `A` before `B`, `A` possibly defining `m` and `B` definitely defining it, (a) reports `A` alone, and the concrete lookup reaches `B` whenever `A` lacks `m`. (b) reduces to (a) when may and must coincide.

### 3.5 Instance storage and strong updates

In this section we choose how the attribute set of an instance is tracked.

Alternatives: (a) no must information, so every attribute read may raise AttributeError; (b) a full shape analysis with materialization; (c) recency abstraction (Balakrishnan and Reps, SAS 2006): one singleton cell per allocation site for the most recently allocated object and a weakly updated summary for the others; (d) k-recency: singleton cells for the k most recently allocated objects at a site, a summary for the others, and a count on the summary.

We adopt (d) with k = 2, and k = 3 at most. (a) leaves an AttributeError edge on every read, and the fatal-exception encoding (§4.6) turns each such edge into a proof obligation. (b) provides more than dispatch needs. (c) makes `self.x = v` in `__init__` a strong update to the must key set of the cell under construction, which is where must membership is created; with user functions inlined, a source-level site is cloned per call path, so (c) also separates two calls of one factory. What (c) leaves weak is any write to the previous object from the same site: `a = C(); b = C(); a.x = 1` in straight-line code, and `node = Node(); node.next = prev; prev.back = node; prev = node` in a loop, where the previous iteration's node is already in the summary at the back edge, so the back pointer is a weak update and the chain is lost after one step. (d) keeps the previous k objects as singletons, so both writes are strong and the loop head carries a precise chain of length k followed by the summary; this is what shape analysis obtains with instrumentation predicates, obtained by age instead. The count on the summary in `{0, 1, ≥2}` keeps the (k+1)-th object strongly updatable until the (k+2)-th allocation, since after the first fold the summary holds exactly one object. Each allocation renames every pointer into the site's cells, so the cost of an allocation grows with k, and beyond k = 3 the renaming cost outweighs the sites that benefit. Slotted classes have an exact key set fixed by the class and need none of this for their attribute set.

### 3.6 Numeric component

In this section we choose the numeric component of the value domain.

Alternatives: (a) intervals over unbounded integers; (b) signs; (c) intervals whose bounds are program constants and ±∞, plus symbolic bounds of the form `len(x) + c` for index variables.

We adopt (b) for the first version and (c) when index bounds are needed. (a) has infinite height and reintroduces widening, and a reduction applied after widening can undo the extrapolation, so every reduction in §4.7 would need its own termination argument. (b) and (c) are finite. The one relational fact indexing needs is `0 ≤ i < len(xs)` for range loops, which (c) expresses without a relational domain.

### 3.7 Representation of control transfer

In this section we choose how control transfer is represented in the abstract state.

Alternatives: (a) a control-flow graph with one exceptional edge from each raising site to the enclosing handler, and ordinary edges for `break`, `continue` and `return`; (b) a normal state and an exceptional state at each program point, with `break`, `continue` and `return` as graph edges; (c) completion records: the abstract state at a point is a cardinal power keyed by the completion kind in {normal, raise, break, continue, return}, with the `raise` slice partitioned further by the exception's class and the `return` slice carrying a value; §3.8 refines each abrupt slice into completions keyed by source site.

We adopt (c). `finally` reinstates or replaces a pending completion, so the pending kind is data that the transfer function of `finally` reads and writes; under (a) and (b) the kind is encoded in the graph, and a `finally` block reached by four kinds of edge is either duplicated per kind by the graph construction or analyzed on the join of its inputs with the kinds no longer separable afterwards. Under (c) the `finally` body is applied to each pending slice (§3.8), the five kinds are a finite key, and the exception effect of the quad-directional system is the `raise` slice at each location. Expressions complete with `normal v` or `raise e` only, since `yield` and `await` are rejected (§5.2).

### 3.8 Analysis of `finally` and exits from it

In this section we choose how the `finally` body is analyzed and which exits from it are admitted.

Alternatives for the body: (a) join the pending slices, analyze the body once, and reinstate each pending kind from the joined result; (b) analyze the body once per pending slice and reinstate each from its own result.

We adopt (b). Under (a) the reinstated `normal` and `raise` states share every fact the body computed, and the narrowed exception state entering the block (§4.6) is lost at the join. (b) costs at most five analyses of the body, and fewer in practice, because `break` and `continue` slices exist only inside a loop and are consumed at its boundary.

Alternatives for exits: (a) model `return`, `break` and `continue` in `finally` with the override rule of §2.2; (b) reject them, following PEP 765, and keep `raise` as the only override; (c) a language-version switch: (a) for versions before 3.14, where the exits are legal and existing programs use them, and (b) from 3.14 on, where PEP 765 warns and an error is planned.

We adopt (c). Under (a) alone every program is analyzed as CPython runs it, including a `return` in `finally` that discards a pending exception, but nothing distinguishes that from the deprecated idiom on a version that will reject it; under (b) alone a program written for 3.13 or earlier is rejected although it runs. The switch is a parameter of the language module (Annex A.2). Under 3.14 and later the override rule of §4.5 has two cases, normal completion reinstates and `raise` replaces; before 3.14 it has five, and a `return`, `break` or `continue` completion of the `finally` body also replaces every pending completion.

Alternatives for the granularity of abrupt completions: (a) one slice per kind, joined at the consumer's entry; (b) one completion per (kind, class, source site), buffered until consumed, the consumer's body run once per completion and its `normal` output joined at its exit, with a cap K per (kind, class) beyond which surplus completions join into one whose source is `⊤`.

We adopt (b). Under (a) the consumer runs on `F(⊔ sᵢ)` and loses every fact that differs by source: the initialization of a name assigned between two raising sites (`x = f(); y = g()` in the try body, `use(x)` in the handler: `x` is uninitialized if `f` raised and initialized if `g` raised, and the join carries an UnboundLocalError edge that neither source has), the variable narrowed at the origin, and the class when the clause's narrowed set has several members. Under (b) it runs on `⊔ F(sᵢ)`, which is at least as precise for monotone `F`, and an obligation failing inside the consumer is attributable to the site that raised. Provenance is one hop deep: a completion produced inside a consumer is keyed by its own site, so nesting does not multiply completions, and a site inside a loop contributes one completion per key at the loop's fixpoint. The cap keeps the key set finite (sites plus `⊤`), which §5.4 relies on.

### 3.9 Error policy

In this section we choose how exceptions raised by the virtual machine are treated.

Alternatives: (a) one tier for every machine-raised exception, all obligations or all edges; (b) a policy per category of machine-raised exception, drawn from {abort, model-if-handled, model, assume}, with preset packs; (c) a policy per site, by pragma.

We adopt (b), with (c) permitted as an override of the pack at a site. Under (a) a program in the EAFP style (partial operations wrapped in `try` rather than guarded) either fails verification at every wrapped call or pays a raise edge at every dispatch site; under (b) the packs of §4.6 name the three points that correspond to programming styles, and a category that can neither be proved absent nor usefully modelled (MemoryError, an asynchronous interrupt) gets `assume`, which (a) cannot express. Explicit raises in user code are outside the policy and always produce a completion, because the program's own raises are its specification of failure.

### 3.10 Encoding of a dispatch site

In this section we choose how a dispatch site with several candidate classes is encoded for the verifier.

Alternatives: (a) one case per candidate class; (b) one case per distinct resolved target, each case carrying the subset of candidate classes that resolve to that target as the class set of the receiver inside the callee; (c) a contract on the base method, every override verified against it under the behavioural-subtyping conditions, and the site verified against the contract alone; (d) (b) where the candidate set is closed and the resolved targets do not reach the site's own function through the hierarchy, and (c) elsewhere.

We adopt (d). Under (a) classes that inherit one implementation (`Rect(Square)` without an override of `area`) produce identical cases; under (b) they collapse, so a site over five classes with three implementations has three cases, and the subset carried into each case keeps a nested `self.helper()` inside the target precise when `helper` is overridden further down the hierarchy. (c) costs nothing per subclass and is the only option in two situations: an open candidate set (a parameter of a library entry point whose caller is outside the program) and recursion through the hierarchy (`Group.area` calling `child.area()` over children whose set contains `Group`), where inlining does not terminate and the contract is the induction hypothesis. Its price is that an override doing more than its contract states is invisible at the site, so (d) uses it only where (b) cannot apply. The two tests, closedness of the set and whether the resolved targets reach the site's function through `cand`, are computed from information the analysis already holds (§4.8).

### 3.11 Representation of a value

In this section we choose the shape of an abstract value.

Alternatives: (a) a set of tags together with one instance of each component domain (bag, sign, interval, size) shared across the tags; (b) a product indexed by the candidate classes, each key carrying the components that have a meaning for that class, with `⊥` for a class the value cannot have.

We adopt (b). Under (a) a value tagged `{int, str, A}` carries an interval and a string bag that have no interpretation when it narrows to `A`, and reductions are needed to keep them consistent with the tag set; under (b) the component for `int` abstracts only the concrete values that are integers, the tag set is the support of the map, narrowing is restriction, and the product loses nothing relative to the partition by class, because the summands are disjoint. Transfer functions are then written per key, which is how the operator tables are organized (§4.4).

### 3.12 Object shape

In this section we choose which mutations of an object's own key set are admitted.

Alternatives: (a) open shapes, as CPython executes them: a key may be added to or removed from any object at any time; (b) rigid shapes: an object's own key set is fixed at the end of its initialization phase, values remain mutable with their kind preserved, as mypy and ty require; (c) declared shapes: every key must be declared by `__slots__` or an annotation.

We adopt (b). Under (a) every attribute read carries an AttributeError edge unless the key is a must key at that point, and `keys` becomes flow-sensitive state on class cells, which §3.2 excludes; under (c) most existing code is rejected. (b) is what the type checkers already enforce, so a program that passes them satisfies it, and it makes the key universes of instances and classes computable once per class (§4.9).

### 3.13 Instantiation under an uncertain class

In this section we choose how the result of `C()` is represented when `C` may be one of several classes.

Alternatives: (a) one cell per allocation site with `type` equal to the candidate set; (b) one cell per allocation site and candidate class, each with exact `type`.

We adopt (b). Under (a) the keys established by `A.__init__` and by `B.__init__` join into one key set and the correlation between the object's class and its keys is lost; under (b) each cell has the keys its own `__init__` established, the result's pointer part is the set of cells, and k-recency ages per (site, class). The cost is one cell per candidate, which the partition of §4.7 pays already.

### 3.14 Contracts and summaries

In this section we choose how calls to analyzed functions, to recursive functions, and to unanalyzed code are summarized.

Alternatives: (a) a contract for every function, written in the contract DSL and assumed at every call; (b) inferred summaries as least fixpoints for analyzed functions, including recursive ones, and contracts for boundaries, library code and the verifier, certified as post-fixpoints when a body is available.

We adopt (b). The domain has finite height, so the summary of a recursive function is a least fixpoint computed by iterating its body from `⊥` with the current summary assumed at the recursive calls, and it terminates without a contract; under (a) every recursive function needs a hand-written invariant that the interpreter computes itself. A contract is a post-fixpoint: certifying it means analyzing the body once with the contract assumed at the recursive calls and checking the result against it, which places it above the least fixpoint (§4.11). The verifier still needs contracts for recursion, since it cannot inline a recursive call, and for boundaries and libraries, where nothing is analyzed. A function with neither a body nor a contract is rejected by default; a `havoc` switch substitutes the sound `⊤` summary of §4.11, so that a program can be analyzed around one missing model.

### 3.15 Representation of collections

In this section we choose how the contents of a collection are represented.

Alternatives: (a) one summary element per collection, with size and emptiness; (b) a spatial window: up to k explicit positions at each end of a sequence, up to L explicit literal keys or elements of a dictionary or set, and a summary for the rest.

We adopt (b). Under (a) `a, b = xs`, `xs[0]`, `xs[-1]` and the last elements appended in straight-line code read the join of everything the collection ever held, and a comprehension over a small literal list cannot compute its image; under (b) those positions are exact and strongly updatable while they exist, and the summary is what (a) was. The window is the spatial form of k-recency: `append` renames the suffix and folds its oldest position into the summary as an allocation folds the oldest aged cell, and the renaming touches one cell rather than every pointer into a site, so the spatial k can exceed the temporal one; k = 3 or 4 covers unpacking and the end-access idioms, and L for dictionaries and sets can be larger, since it bounds a key set.

### 3.16 Evaluation of comprehensions

In this section we choose how a comprehension is evaluated.

Alternatives: (a) always as the loop it desugars to, with the back-edge join and a fixpoint; (b) always as a map of the iteratee over the source's element summary; (c) as a map when the body writes nothing, and as the loop otherwise.

We adopt (c). (b) is unsound when the body writes a cell that a later iteration reads (an iteratee calling a closure over a counter is a fold), and (a) loses the image of an explicit source, which is exact under (c) whenever the body's write footprint is empty. The footprint is computed by analyzing the filter and the iteratee once on the witness, and calls inside them contribute theirs by §4.11 (a body its analyzed footprint, a contract its declared one), so the choice is made by the analysis rather than by syntax.

### 3.17 Hashability

In this section we choose how hashability is decided.

Alternatives: (a) a hashability flag on values, set at allocation and joined; (b) a sort per class cell derived from the resolution of `__hash__`, structural for tuples and frozensets, projected onto values as the join over their keys.

We adopt (b). Hashability is a property of the class, fixed at class creation by rules CPython applies in `type.__new__`, so under the closed class graph (b) knows the sort of nearly every value statically and discharges key and element checks without a runtime fact; (a) carries a flag that (b) recomputes from the class set, and cannot express the structural cases. The two sorts, Hashable and MaybeHashable with an injection from the first into the second, are also what makes the verifier's datatypes well typed (§4.16).

### 3.18 Naming of cells stored into static slots

In this section we choose how a cell that is stored under a key of a class or module cell during an initialization phase is named.

Alternatives: (a) by allocation site and age only, as every other cell (§3.5); (b) renamed to its destination slot when it is stored under a must key of a class cell, a module cell, or another cell named this way, during the initialization phase of the holder.

We adopt (b). Methods built by a metaclass are made in a loop over the fields, `for fname in fields: def getter(self): ...; ns[fname] = getter`, and under (a) the (k+1)-th getter from the same `def` site folds into the summary, whose closure is the join of all field names, so `obj.c` reads `self._data` at the join of every field. Under (b) the getter stored under `c` is the cell `C.__dict__["c"]`, distinct from the others whatever the field count; the rigid shape of §3.12 makes the binding permanent, so the name is stable, and the slot is exactly what the MRO walk of §4.3 reaches, so the name the analysis uses and the path the semantics takes coincide. Site-and-age naming remains for cells reachable only from anonymous places.

### 3.19 Unrolling of bounded loops

In this section we choose when a loop is executed iteration by iteration rather than joined at its back edge.

Alternatives: (a) always the back-edge join of §4.5; (b) iteration by iteration when the source is a fully explicit collection of definite size `n ≤ 2k` that the body does not write, and (a) otherwise.

We adopt (b). Under (b) the iteration count is known and each iteration is a separate transfer, so the result is exact and the cost is `n` transfers; under (a) a loop over a three-element tuple of field names during a class statement joins the three field names into one and every generated object into one summary. The condition that the body does not write the source (a footprint check, §4.11) excludes the case where an `append` inside the loop extends the iteration, which Python permits for lists and which the back-edge join covers.

## 4. The domain

In this section we specify the domain fixed by the decisions of §3, after an informal description of the shape of a state and one example configuration.

Informally, an abstract state is a graph of cells joined in one chain. An instance cell points, through its `type` edge, to a class cell; the class cell belongs to a static graph built by the class statements, carries the order of its ancestors and its dictionary as keys with certainty and values, and points through `meta` to its metaclass cell in the same graph; a value in that dictionary may point to a function cell, whose code is one `def` of the program and whose closure points to closure cells shared with the frame that created them; the instance cell's own storage holds its attributes as keys with certainty and values, and every value is indexed by class and may point to further cells. Each link can be uncertain, and each is uncertain in its own way: the `type` edge is a may set; the class graph is a set of exact disjuncts, or an order per class after a collapse; the dictionary's keys are fixed after the class statement while its values are per-state and may be may sets; a function cell's code is exact in every state and its closure cells hold joins; an instance's keys are must, may or absent. No link is ever uncertain about instructions.

The program below and the state at its last statement show one configuration. `Fields` generates a getter per field and a `register` method closing over a list allocated in its frame; `Point` uses it; `main` builds a `Point` or a `Base` under a condition and calls a method defined on `Base`.

```python
class Fields(type):
    def __new__(mcs, name, bases, ns):
        registry = []
        for fname in ns["fields"]:
            def getter(self, fname=fname):
                return self._data[fname]
            ns[fname] = getter
        def register(self):
            registry.append(self)
        ns["register"] = register
        return super().__new__(mcs, name, bases, ns)

class Base:
    def describe(self):
        return "base"

class Point(Base, metaclass=Fields):
    fields = ("x", "y")
    def __init__(self, x, y):
        self._data = {"x": x, "y": y}

def main(flag):
    p = Point(1, 2) if flag else Base()
    return p.describe()
```

The state at `return p.describe()`, with `flag` unknown, is:

    class graph (one disjunct, frozen after module initialization)
      Base    bases (object)   precedes [Base, object]           meta {type}
              keys  describe: function, must  ->  Base.__dict__["describe"]
      Fields  bases (type)     precedes [Fields, type, object]   meta {type}
              keys  __new__: function, must   ->  Fields.__dict__["__new__"]
      Point   bases (Base)     precedes [Point, Base, object]    meta {Fields}
              keys  fields:   value, must     ->  tuple, explicit, positions {"x"} {"y"}, size 2
                    __init__: function, must  ->  Point.__dict__["__init__"]
                    x:        function, must  ->  Point.__dict__["x"]   code getter, defaults fname -> str {"x"}
                    y:        function, must  ->  Point.__dict__["y"]   code getter, defaults fname -> str {"y"}
                    register: function, must  ->  Point.__dict__["register"]   closure registry -> L
      L       list cell allocated in the frame of Fields.__new__ under the class statement of Point; size 0, empty

    heap at the statement
      P  Point@main¹   exists maybe-present   type {Point}   keys _data: must -> D
      D  dict@Point.__init__¹   keys x: must -> int {1}, y: must -> int {2}; size 2
      B  Base@main¹    exists maybe-present   type {Base}    keys none
      environment   flag -> bool {True, False}      p -> {Point: {P}, Base: {B}}

    dispatch at p.describe()
      case Point: cand(Point, describe) = {Base}   (Point's keys lack the name; Base must own it)
      case Base:  cand(Base, describe)  = {Base}
      one target, Base.__dict__["describe"], devirtualized; result str {"base"}

Several decisions are visible in it. The two getters are distinct cells named by their slots (§3.18) with exact defaults, because the loop over the explicit tuple `("x", "y")` ran iteration by iteration (§3.19); `registry` is a closure cell, allocated in the metaclass frame, shared by the `register` function cell and outliving the frame (§4.13); `P` and `B` are two cells with exact `type`, one per allocation site and candidate class (§3.13), and `p` is indexed by class (§3.11); both are maybe-present because each allocation is conditional, and the state does not record that exactly one of them exists (§5.3); the dispatch is partitioned by class and collapses to one target through `cand` (§3.10, §4.3). Nothing in the state names a piece of code other than by its `def` site.

### 4.1 Cells and values

In this section we define the abstract heap and the abstract values.

The abstract heap is a finite graph of cells of two kinds: class cells and instance cells.

A class cell exists for each class statement, for each synthetic class produced by a decorator that returns a new object (§6), and for each builtin type; a class statement executed more than once yields aged cells and a summary as in §3.5. It holds:

- `bases`: the declared bases, exact;
- `may`, `must`: the may and must ancestor sets, with `must ⊆ may`, both defined by membership of `tp_mro`;
- `precedes`: on the disjunctive level the exact `tp_mro` of the disjunct, on the collapsed level the partial order of §4.2 on `may`;
- `keys`: the dictionary key set with certainty, `mustKeys ⊆ mayKeys`, each key carrying a kind in {value, function, classmethod, staticmethod, data}, derived from the class of the entry's value and never declared: the entry binds on a read through an instance iff its class resolves `__get__` (a function, a classmethod, a staticmethod, a property, a slot member, a user descriptor), it is data iff its class resolves `__set__` or `__delete__` (a property, a slot member, a user descriptor with a setter), and it is a plain value otherwise, so a `functools.partial` or an instance of an ordinary class stored under a key is called without a receiver; the kind is may-data when the resolution is uncertain;
- `meta`: the may set of class cells that `ob_type` may point to;
- `virtual`: the may set of class cells registered as virtual ancestors through `ABCMeta.register`, consulted by `isinstance` and `issubclass` only;
- `values`: an abstract value per key, held in the per-state heap.

An instance cell exists per allocation site and age (§3.5): for a site `s`, aged cells `s¹, …, sᵏ` and a summary `s*`. The aged cell `sⁱ` denotes the i-th most recently allocated object at `s`, when at least i allocations have occurred; `s*` denotes every older object. Each cell holds:

- `type`: the may set of class cells that `ob_type` may point to;
- `keys`: the storage key set with certainty, exact for slotted classes; the certainty of a key is the initialization status of that attribute (absent from `may` is uninitialized, in `must` is initialized, in `may` but not `must` is maybe-initialized);
- `values`: an abstract value per key;
- for a collection, an emptiness status in {empty, non-empty, maybe-empty} and a definite size that is exact or unknown; both are properties of the location, so a may alias over two collections denotes both sizes;
- for an aged cell, `exists` in {absent, present, maybe-present}; for the summary, `count` in {0, 1, ≥2}.

An allocation at `s` renames the state: `sᵏ` folds into `s*`, each `sⁱ` becomes `sⁱ⁺¹`, and the fresh cell becomes `s¹` with `exists = present`. Folding joins `type` and `values` pointwise, joins `keys` (a key in `must` on one side only becomes maybe-initialized), turns every pointer to `sᵏ` into a may pointer to `s*`, and increments `count`. A definite collection size survives a fold only when the folded sizes are equal; otherwise the summary keeps the emptiness status alone. A write through a name that must point to an aged cell with `exists = present`, or to a summary with `count = 1`, is a strong update; every other write is weak. A conditional allocation leaves `s¹` with `exists = maybe-present`, and a later allocation shifts it to `s²` unchanged, so writes through it stay weak until a test settles its existence.

An abstract value is a product indexed by class cells (§3.11): `v = λt. v_t` with `v_t ∈ D_t`, where `D_t` is the component domain of class `t` and `v_t = ⊥` when the value cannot be of class `t`. The tag set of a value is its support, `tags(v) = { t : v_t ≠ ⊥ }`; join is pointwise; narrowing to a set of classes restricts the map and sends the other keys to `⊥`. The components are:

- `int`: a literal bag (the program's integer literals the value may equal, or `*` for a value produced by an operation whose result is not a literal), a sign in {negative, zero, positive}, and an interval whose bounds are program constants, `len(x) + c` terms and loop-bound names, or ±∞;
- `bool`: a bag within `{True, False}`; `isinstance(x, int)` keeps the key because the class cell of `bool` has `int` as a must ancestor, and arithmetic on it lands under `int`;
- `float`: a bag, a sign, an interval, and `nan` and `inf` flags;
- `complex`: a bag only, since it has no order;
- `str` and `bytes`: a bag, a definite size and an emptiness status, carried on the value because these have no cell;
- `None`: a unit;
- every pointer class (user classes, `list`, `dict`, `set`, `tuple`, functions, classes, iterators): the may set of cells whose `type` is that class, the class-specific components being on the cell; a bound method is an immutable pair of pointer parts carried on the value rather than a cell (§4.12).

For a scalar key the representation tag is the key itself; for a pointer key it is the solid base of the class, computed from `bases`. A name carries an initialization status in {uninitialized, initialized, maybe-initialized} above bottom, which is the lattice used for key certainty. Two names must alias when both must point to the same aged cell with `exists = present`, or to a summary with `count = 1`. Must-alias is also kept as a relation on names in its own right, because a pair that must alias through `sᵏ` still must alias after the fold sends both into `s*`, and the derived form loses that. Two distinct cells never denote the same object, so names pointing to disjoint cell sets must not alias.

### 4.2 The order domain

In this section we define the two levels of the hierarchy abstraction, then the order domain of the collapsed level: its abstraction and concretization (§4.2.1), its lattice (§4.2.2), and the facts C3 supplies for free (§4.2.3).

The class graph of §3.2 is a set of at most K exact graphs. Each disjunct assigns exact `bases` to every class cell; its `tp_mro` per class is computed by C3, and a merge failure is a TypeError branch at that class statement (§4.6). Each source of variation (a conditionally chosen base, a decorator returning a new class, a metaclass editing `bases`) splits every disjunct it applies to in two. When the set exceeds K it collapses to one graph whose cells carry the order domain below, obtained by applying α of §4.2.1 to each class's set of MROs across the disjuncts. Resolution (§4.3) runs per disjunct on the first level, and a site whose candidates differ across disjuncts is partitioned by disjunct, one more finite key (§5.4).

#### 4.2.1 Definition

In this section we define the abstraction and concretization functions and state the Galois property they satisfy.

Let `V` be a class cell's may ancestor set and `S` the set of its candidate MROs, each a strict total order on a subset of `V` containing the must set. The abstraction is

    α(S) = { (a, b) : a precedes b in every L ∈ S that contains both }
    γ(P) = { L : L is a linear extension of P }

`α(S)` is an intersection of strict total orders and is therefore a strict partial order. When the ancestor set is fixed, every strict partial order is the intersection of its linear extensions (Szpilrajn), so `α(γ(P)) = P` and the pair is a Galois insertion. Not every linear extension is a legal MRO; restricting `γ` to C3-valid extensions makes `α ∘ γ` a closure operator with `P ⊆ α(γ(P))`, so distinct elements may denote the same set and the pair is a Galois connection with a reduction operator rather than an insertion. Both readings are sound, because the restriction only removes linearizations.

#### 4.2.2 Lattice

In this section we define the carrier, the order, the join and the meet, and bound the height.

The carrier is the set of transitively closed irreflexive relations on `V`, plus a distinguished element `⊥` with `γ(⊥) = ∅`. The order is `P ⊑ Q` iff `P ⊇ Q`: more known precedence is more precise. `⊤` is the empty relation. The join is intersection, which preserves transitive closure. The meet is the transitive closure of the union when that closure is acyclic, and `⊥` otherwise; `⊥` also arises when the C3-restricted `γ` is empty without a cycle. Total orders are the maximal consistent elements and are pairwise incomparable, so there is no total order at the bottom. The height is at most `|V|(|V|-1)/2 + 2`, so no widening is needed. Accumulating constraints on a class cell is a sequence of meets; merging control-flow paths is a join.

#### 4.2.3 Facts C3 supplies

In this section we list the precedence pairs that C3 fixes regardless of the unknown parts, and the case in which none of them holds.

For a class linearized by C3 (no `mro()` override on the metaclass), the following pairs hold whatever the unknown parts are: the class itself precedes every ancestor; `object` is preceded by every ancestor; every pair related by a base's order whose two endpoints are must-ancestors of that base holds in the class's order (monotonicity); direct bases are ordered as declared (local precedence). A pair with a may-only endpoint is not inherited: in a candidate where the base's linearization lacks that endpoint and it enters through another base, C3 is free to place it on either side. The order therefore starts near-total and loses pairs only where the uncertainty applies. The closure of the inherited pairs is cyclic exactly when every candidate merge fails; a cycle that closes only with a pair excluded by the may-only condition means some candidate may fail; the two are the definite and the possible `cond` of the TypeError at the class statement (§4.6). For a class whose metaclass overrides `mro()`, none of these holds: the override may drop declared bases from `tp_mro` (CPython checks only the layout compatibility of the returned classes), so `must` collapses and `may` is not the declared closure. When the override's body is a list literal or a filtered `super().mro()`, the order is recovered by analyzing it; otherwise the class is rejected (§6).

### 4.3 Attribute resolution

In this section we define the resolution of a name on an object through the abstract heap.

For a class cell `C` and a name `m`, let

    D_may(C, m)  = { A ∈ may(C)  : m ∈ mayKeys(A) }
    D_must(C, m) = { A ∈ must(C) : m ∈ mustKeys(A) }
    cand(C, m)   = { A ∈ D_may(C, m) : ¬∃ B ∈ D_must(C, m). (B, A) ∈ precedes(C) }
    absent(C, m) ⟺ D_must(C, m) = ∅

`cand(C, m)` is the set of ancestors whose dictionary the concrete walk may stop at; it is the set of minimal elements of `D_may` when `D_may = D_must`. The site devirtualizes on `C` when `cand` is a singleton and `absent` is false. Each candidate carries the kind of its entry.

For an instance read `o.m` with `T = type(cell(o))`, the result is the join over `t ∈ T` of the following. Let `K = cand(t, m)`. Candidates in `K` of kind data contribute the result of their `__get__`: the field value for a slot member, the summary of `fget` for a property. If every candidate in `K` must be data, nothing else contributes. Otherwise the instance storage contributes `values(m)` when `m ∈ mayKeys(cell(o))`, and contributes it alone when `m ∈ mustKeys(cell(o))`. Otherwise the non-data candidates contribute: a function as a bound-method value (the function cell paired with `cell(o)`), a classmethod bound to `t`, a staticmethod or plain value as is. If `absent(t, m)` and `m ∉ mustKeys(cell(o))`, then `__getattr__` contributes its summary when it resolves on `t`, and the AttributeError edge is live otherwise. In these terms the three kinds of attribute are: an instance attribute, a hit in the instance's own storage with no data descriptor above it on the chain; a method, a function found in a class dictionary, reached only when own storage lacks the name and bound on the way out; a class attribute, a plain value in a class dictionary, read through the instance until own storage shadows it.

For a class read `C.m` the rule is the same with each `M ∈ meta(C)` in the role of the type and the walk of `C`'s own MRO in the role of the object's own storage: data candidates from `cand(M, m)`; then `cand(C, m)`, with functions left unbound and classmethods bound to `C`; then the non-data candidates from `cand(M, m)`; then AttributeError.

The order and the callables are held by different cells. `tp_mro` and `precedes` reference class cells only; the callables live in the dictionaries of those classes, and resolution is the walk of the one followed by a lookup in the other:

    instance cell ──type──▶ class cell C ──precedes──▶ [C, B, A, object]      (class cells only)
                                             │
                                             └─keys/values─▶ C.__dict__["m"] ──▶ function cell
                                                                                  ├─code ──▶ body and signature
                                                                                  ├─closure ──▶ closure cells
                                                                                  ├─defaults ──▶ values and cells
                                                                                  └─globals ──▶ module cell

Uncertainty in the MRO is therefore uncertainty about which class's dictionary is consulted first, never about the callable itself. Three consequences follow: one function cell is reached through many MROs, so `A.__dict__["m"]` is the same cell whether the receiver is an `A`, a `B` or a `C`, and its closure cells are shared by every subclass as in CPython; the metaclass chain is the same picture one level up, so a method defined on the metaclass is a function cell in the metaclass's `values`, bound to the class object rather than to an instance; and the destination naming of §3.18 names a function cell by the slot the walk reaches. The two sets of pointers meet only inside the class statement (§4.10), where the metaclass's `__new__` holds the bases, the computed order and the freshly allocated function cells at once; when it returns, the order is on the class cell, the callables are in its dictionary, and nothing references one from the other.

Writes go to own storage, never up the chain. `o.m = v` runs `object.__setattr__`: a data descriptor for `m` on the chain of `type(o)` takes the write through its `__set__` (the field of a slot member, the summary of `fset` for a property); otherwise the write lands in the instance's own storage, strongly or weakly by §4.1, and a class attribute of the same name is untouched, so `self.count += 1` reads the class attribute and writes an instance key. `C.m = v` runs `type.__setattr__`: a data descriptor on the metaclass chain takes it; otherwise the write lands in `C`'s own dictionary, and when `m` is inherited that is a new shadowing key. Under the rigid-shape rule of §4.9 a write is admitted only when `m` is in the universe of the receiver's own storage, so both shape-changing cases are rejected outside the initialization phase.

The alternative order, instance storage first and then the class, is rejected: a data descriptor on the MRO takes priority over the instance dictionary, which is what makes a slot or a property unshadowable and the analysis of a slotted class exact.

`super()` inside a method of class `A` on receiver `o` resolves `m` on the classes that may follow `A`: for each `t ∈ type(cell(o))`, the candidates are `{ B ∈ D_may(t, m) : B ≠ A ∧ (B, A) ∉ precedes(t) }` minus every `B` for which some `C ∈ D_must(t, m)` has `(A, C) ∈ precedes(t)` and `(C, B) ∈ precedes(t)`. A class incomparable to `A` is kept, because some linearization places it after `A`; restricting to the classes that must follow `A` would drop it and under-approximate. This is the one lookup that consumes the order beyond its minimal elements, since it needs the classes after `A` rather than the least element.

### 4.4 Calls and operators

In this section we define call dispatch and binary-operator dispatch.

A call `f(args)` is classified by the keys of `f` (§4.12) and joins the following over the cells in its pointer part. A function cell contributes its summary, with a TypeError edge when the arity of `args` does not match its signature. A bound-method cell contributes the function's summary with the receiver prepended. A call on a value whose pointer part holds class cells is partitioned by class cell (§3.13). For each class cell `C` the call resolves `__call__` on `meta(C)`; for the default `type.__call__` this is `__new__` resolved by `cand(C, __new__)` followed by `__init__` resolved by `cand(C, __init__)`. The result has the pointer part of the return of `__new__`: a fresh cell for the site and `C`, with `type = {C}`, when `__new__` is `object.__new__`, and an existing cell when `__new__` returns one (a cached instance); `__init__` runs only on the cases where the result is an instance of `C`. The pointer part of the call's value is the union over the candidate classes of these cells, so an object built from an uncertain class is a set of cells, each with exact `type` and the keys its own `__init__` established. `meta(C)` is exact per disjunct of the class graph (§4.10), so the metaclass is a may set only after a collapse; an unanalyzable metaclass `__call__` is rejected (§5.2). Any other instance cell contributes the resolution of `__call__` on its `type`, and the TypeError edge when that is absent. Scalars contribute the TypeError edge.

A binary operator `a ⊕ b` is applied per pair of keys `(ta, tb)` of the operands' indexed values (§4.1), on the components `a_ta` and `b_tb`; each pair's result is placed under the result class of the table cell, or of the resolved method's summary, and results landing on the same class join. For builtin pairs the table cell has a fixed result class except where the component decides it: `int ** int` yields `float` when the exponent is negative, and a real base raised to a non-integral power yields `complex` when the base is negative. For a pair involving a user class the pair resolves `__op__` on `ta` and `__rop__` on `tb`: the reflected method is tried first when `ta ∈ must(tb)`, `ta ≠ tb`, and `cand(tb, __rop__)` is disjoint from `cand(ta, __rop__)`; it is tried second when `ta ∉ may(tb)` or when both resolutions devirtualize to the same owner; both orders are joined otherwise. A candidate is skipped when its summary may return NotImplemented, and the TypeError edge is live on a pair when every candidate on it may be skipped; under `abort` the obligation is on that pair alone, and surviving it drops the pair from both operands.

### 4.5 Completions

In this section we define the abstract transfer of completions through statements.

The abstract state at a point is a `normal` state (a heap and an environment) together with a buffer of abrupt completions, each keyed by (kind, class, source site) with kind in {raise, break, continue, return}. A `break` or `continue` completion carries a heap and an environment; a `return` completion carries them with an abstract value; a `raise` completion carries them with the pointer part of the exception (§4.6), and its class key is the exception's class partition. Two completions with the same key join. The transfer of a statement takes the `normal` state of its input and produces a `normal` state and a buffer; a compound statement routes the completions of its components, and a consumer runs its body once per completion it consumes:

- sequencing: the `normal` state of a statement is the input of the next, and the buffers of the statements of a block are unioned, joining on equal keys;
- expressions: the transfer of an expression produces a `normal` value with its post-state and one `raise` completion per raising sub-expression, each with the exceptional state of §4.6 at that site, in evaluation order;
- `try`: each `raise` completion of the try body is matched against the clauses in order (§4.6) and the first clause that may catch it runs its body once on that completion's narrowed state; the `else` body runs once on the `normal` state of the try body; the pending buffer is the union of the handlers' buffers, the `else` buffer, the `break`, `continue` and `return` completions of the try body, and the unmatched remainders of its `raise` completions; with `finally`, the body runs once per pending completion and once on the `normal` state, a `normal` completion of the body reinstates the pending completion under its own key, and a `raise` completion of the body replaces it by a completion keyed by the raising site inside `finally`, so replacements of several pending completions share a key and join; under the pre-3.14 setting of §3.8, a `return`, `break` or `continue` completion of the body replaces the pending completion in the same way, keyed by the exiting statement's site, and a pending `raise` so replaced is discarded;
- loops: under the condition of §3.19 (a fully explicit source of definite size that the body does not write) the body is executed once per position in order and its completions are handled as below on each; otherwise the `break` completions of the body join into the `normal` output of the loop without passing through `else`; the `continue` completions and the `normal` state join into the back edge; `raise` and `return` completions propagate in the buffer; exhaustion feeds `else`; no completion accumulates across iterations, because `break` and `continue` are consumed at the loop boundary and a site inside the body contributes one completion per key at the fixpoint;
- `with`: a `try` with a `finally` whose body is the resolution and call of `__exit__` on the manager's `type` (§4.3) with the pending exception as argument; when the summary of `__exit__` may return a true value the `raise` completion also contributes to the `normal` output, and when it must return a true value it contributes only there;
- calls: the `return` completions of the callee join at the call boundary into the `normal` value and post-state of the call expression; each `raise` completion of the callee becomes a `raise` completion of the call site, keyed by the callee's site; falling off the end returns `None`;
- `except E as e`: `e` is initialized and points to the matched cells inside the handler and is uninitialized on every exit from it; a bare `raise` inside the handler re-raises the cells `e` points to under the handler's site.

The buffer holds at most K completions per (kind, class); a completion beyond the cap joins into one whose source is `⊤`. Each key is drawn from a finite set and each completion's state is an element of the finite-height state lattice, so the buffer has finite height (§5.4).

### 4.6 Exceptions

In this section we define the representation of a raised exception, handler matching, the narrowing applied when a completion enters a handler, and the two tiers of exceptions.

Exception classes are class cells. The payload of a `raise` completion is a may set of instance cells whose `type` is in the exception classes; `raise E(...)` allocates such a cell (§4.4) and emits a `raise` completion keyed by the statement's site, and the exception effect at a location is the union of the payloads of the `raise` completions in the buffer there. Matching uses `tp_mro` directly, since CPython does not consult `__subclasscheck__` for `except`, so `virtual` is not read.

Clause narrowing. The k-th clause `except E_k` (a tuple clause naming several classes acts as their union) receives the cells `e` with `type(e)` narrowed to `{ t : E_k ∈ may(t) ∧ ∀ j < k. E_j ∉ must(t) }`, since a cell that an earlier clause must catch has been taken by it; the remainder after the last clause is `{ t : ∀ j. E_j ∉ must(t) }` and is the unmatched part of the pending completion. Narrowing composes along the propagation path: a cell reinstated by `finally` reaches the clauses of the enclosing statement with the narrowing of every clause it passed without a must match.

Origin narrowing. A raise edge at a site is live under a condition on the state, and the exceptional state the site emits is its pre-state narrowed by that condition, which is the complement of the surviving-edge reduction of §4.7: KeyError from `d[k]` restricts the literal bag of `k` to the literals outside the location's must keys; ZeroDivisionError from `x / y` sets the sign of `y` to zero; IndexError from `xs[i]` restricts `i` to the outside of `[-size, size)` or the collection to empty; a fatal operator cell restricts the tag pair to the fatal cells; a demoted AttributeError (below) restricts `type(o)` to the classes where the name is absent. The narrowing is applied at the site, where the completion is created; once completions beyond the cap of §4.5 join into the `⊤`-source completion, only the join of their narrowed states survives and the per-site condition cannot be recovered. It is sound when the site's cell is the only source of that class at the site, which §5.2 secures by rejecting overrides of the methods behind table cells on subclasses of builtin collections. A call site applies no origin narrowing of its own, because the `raise` slice of the callee already carries the narrowed state of the site inside the callee.

The exceptional state. The state emitted at a raise includes the effects of the sub-expressions evaluated before the raising one and excludes the effect the raise skips: the target of `x = f()` stays uninitialized in the `raise` completion, the store of `a[i] = v` does not happen when the index fails, and an `__init__` that raises leaves its cell with the keys written before the raise in `must` and the others absent.

Provenance. A `raise` statement in user code always produces a completion, whatever its class. The policy below applies to sites where the virtual machine, a builtin, or generated code raises. The class hierarchy decides matching and the site's category decides the policy, and the two are independent: `FrozenInstanceError` is a subclass of AttributeError, `UnicodeDecodeError` of ValueError, and `LookupError` is an ancestor of KeyError and IndexError, so under the EAFP pack a clause naming AttributeError catches a modelled `frozen` completion while the `dispatch` sites in the same try body abort.

Policy values. Let `cond` be the condition under which a site's raise edge is live, computed by the component named in the table below; it is the same term whatever the policy. Under `abort` the site emits the obligation `¬cond`, emits no completion, and its continuation assumes `¬cond`. Under `model` the site emits a completion whose state is the pre-state narrowed by `cond` (the origin narrowing above), and its continuation assumes `¬cond`. Under `model-if-handled` the site behaves as `model` when a lexically enclosing clause names an ancestor of the class, and as `abort` otherwise. Under `assume` the site emits neither obligation nor completion, and the assumption `¬cond` is recorded in the certificate.

Categories and packs. Each category is a set of classes raised at a kind of site; the packs `strict`, `EAFP` and `full` assign a value to every category, and a pack may be overridden per category or per site (§3.9).

| category | classes, by site | `cond` discharged by | `strict` | `EAFP` | `full` |
| --- | --- | --- | --- | --- | --- |
| `dispatch` | TypeError, AttributeError, NameError, UnboundLocalError raised by resolution, calls, operators and name lookup (including an uninitialized local or closure cell, §4.13), and the TypeError of an inconsistent MRO at a class statement | `cand` and `absent`, arity, the operator table, initialization status, the C3 merge (§4.2.3) | abort | abort | model |
| `key` | KeyError, and the TypeError of an unhashable key | the dictionary cell's keys, the literal bag, the hashability sort (§4.16) | abort | model | model |
| `index` | IndexError, and the ValueError of an unpacking mismatch | definite size, emptiness, sign | abort | abort | model |
| `arith` | ZeroDivisionError, OverflowError | sign; the float table | abort | abort | model |
| `value` | ValueError and its subclasses raised by builtin conversions and methods | the literal bag | abort | model | model |
| `exhaustion` | StopIteration from `next` | emptiness | abort | abort | model |
| `frozen` | FrozenInstanceError from the generated `__setattr__` of a frozen dataclass | a frozen flag on the class cell | abort | abort | model |
| `recursion` | RecursionError | the inlining depth | abort | abort | model |
| `io` | OSError and its subclasses from library I/O | none: the edge is always live | abort | model | model |
| `async` | MemoryError, KeyboardInterrupt | none | assume | assume | assume |

The `strict` pack states that every partial operation has its precondition proved, which is the verification default; `EAFP` accepts programs that wrap partial operations in `try` instead of guarding them; `full` models every execution CPython can produce, except the `async` category, which no pack models. Value-level categories are not decided by the object model: their `cond` is read from the scalar, emptiness, size and key components of §4.7. The alternative of full unwinding for every category under every pack is rejected because it makes every dispatch site a branch in the encoding; the alternative of a single scope-dependent demotion rule for the whole `dispatch` category is the `model-if-handled` value, which no preset uses and which a site may select.

### 4.7 Combination with the value domains

In this section we define how the object-model domain combines with the scalar components, and list the reductions between them.

The combination is a reduced cardinal power keyed by the target of `ob_type`: the state is partitioned by the may target of the receiver's `type` at dispatch sites (and by the pair of targets at operator sites), and the scalar, string, size and heap components live inside each partition. The alternative, a flat reduced product of a tag set with each component, is rejected because every transfer function of the object model is a different function per tag (truthiness, operator tables, whether `is` is meaningful, whether a value needs a cell), and a product cannot express that. Class cells are consulted by the partitions as an environment (§3.2) and never stored in them.

Reductions inside a partition:

- Surviving a fatal edge narrows the inputs that made it live, and the handler entered by the same edge receives the complement (§4.6): after `a + b` with `a` keyed `{int, str}` and `b` keyed `{int}`, the `(str, int)` cell is fatal, so the `str` key of `a` goes to `⊥`; after `o.m` succeeds, `type(cell(o))` narrows to the classes where `m` is not absent; after `x / y`, the sign of `y` narrows to non-zero.
- `is` and `is not` update the heap (must-alias or must-not-alias) and intersect the values on the true branch; `x is None` narrows the scalar part. `==` narrows values only through `__eq__`; when no class in `type(cell(x))` may define `__eq__`, it is identity and yields the same heap facts as `is`.
- `if x:` narrows by partition: `≠ 0` for integers, non-empty for strings and collections, false for `None`, and for instances the resolution of `__bool__` then `__len__`; classes defining neither are truthy and leave the false branch.
- `isinstance(x, B)` narrows `type(cell(x))` to `{ t : B ∈ may(t) ∪ virtual(t) }` on the true branch and to `{ t : B ∉ must(t) }` on the false branch; `type(x) is B` narrows to `{B}`.
- Literal bags meet resolution: `getattr(o, s)` with a bag for `s` that does not contain `*` is a finite set of resolutions, and a dictionary read meets the key set of the dictionary cell, with the KeyError edge dead when every literal is a must key.
- Inside one key: a bag without `*` gives the interval as its hull and the sign as its projection, an interval prunes the bag to the literals inside it, and a definite size fixes the emptiness status. Across keys no reduction is needed, since the keys partition the value (§3.11).

Reduction is one idempotent decreasing function applied after each transfer and at each test, iterated pairwise to a fixpoint. Each component has finite height, so the iteration terminates without a widening (§5.4).

### 4.8 Candidate class sets

In this section we define where the candidate class set of a receiver comes from, what restricts it, and how a site is encoded from it.

Origin. `C()` yields a cell with `type = {C}` (§4.4), and the set travels through assignments, fields and returns under the strong and weak updates of §4.1. It grows at three places: joins (`s = Circle() if f else Rect()`), collection elements (`[Circle(), Rect(), Group(...)]` gives the element summary `{Circle, Rect, Group}`), and boundaries (a parameter of an entry point, a value from unanalyzed code). It shrinks at `isinstance`, at `type(s) is C`, and at every surviving dispatch (§4.7). A receiver known only by its base class therefore arises at boundaries and at joins, not from the hierarchy itself.

Restrictions. The analyzed program is closed: every object is allocated at a site of the program, so a class without an allocation site never enters a `type` set. An abstract class never does either, because `Shape()` with an unimplemented abstract method is a TypeError of the `dispatch` category (§4.6) and is therefore an obligation rather than an allocation. A hint `B` on a boundary parameter is assumed in the assert-then-assume style and yields `{C : B ∈ must(C)}` intersected with the allocated classes. A boundary whose caller is outside the program is declared open; its set is the full sub-hierarchy in the program plus an unknown subclass, and the encoding below does not apply to it.

Encoding. For a site `s.m(...)` with `T = type(cell(s))`, the cases are the distinct elements of `⋃_{t ∈ T} cand(t, m)` (§4.3), and the case for a target `A.m` carries `{ t ∈ T : A ∈ cand(t, m) }` as `type(self)` into the callee, so a class whose resolution is uncertain appears in every case it may reach. A site whose set is closed and whose targets do not reach the site's own function through `cand` is encoded by these cases (§3.10); otherwise the contract of the base method stands for the call. The `devirt` and `deferred` counts of §6 are counts of targets, so a site with one target over several classes counts as devirtualized.

### 4.9 Object storage and shape

In this section we define the own storage of instances and classes, its key universe, the initialization phase after which the universe is fixed, and the TypedDict shape.

Storage. A default instance owns a dictionary, created on first write, to which CPython adds a key on any write; a slotted class stores each slot at a fixed offset of the instance struct and exposes it through a member descriptor in its own `tp_dict`, the instance has no dictionary unless a base provides one or `'__dict__'` is listed in `__slots__`, an unset slot reads as AttributeError, and a slot name that is also a class variable is a ValueError at class creation. Both are one instance cell with `keys` and `values` (§4.1). They differ in three ways: the universe below is declared for slots and inferred for dictionaries; a slot is a data descriptor and can neither be shadowed nor coexist with a class attribute of its name; `vars(o)` and `o.__dict__` exist only for dictionary objects, a read being a view of the cell and an assignment to `__dict__` being rejected. A class's own storage is its `tp_dict`: everything its body defines and everything its metaclass and decorators inject. A metaclass's `tp_dict` holds what is callable or readable on the class object only.

Phases and universes. Every object has an initialization phase: for a class, the class statement (§4.10); for an instance, `__new__` and `__init__`, plus `__post_init__` for a dataclass; for a module, its initialization. At the end of the phase the object's own key set is fixed (§3.12). The universe of an instance of class `C` is the union over `C`'s chain of the names assigned to `self` in `__init__`, the annotated class-body names not marked `ClassVar`, the slots, and the dataclass fields; it is computed once per class from the class bodies and the `__init__` bodies, and the analysis of `__init__` supplies each key's certainty. The universe of a class is the key set of its namespace at the end of the class statement. A write is admitted iff its target name is in the universe of the receiver's own storage, and the kind of the entry is preserved; `del`, `setattr` and `delattr` with a non-literal name, and a first assignment to a name outside the phase are rejected. A read may resolve through the chain as in §4.3.

TypedDict. A TypedDict value is a `dict` at run time (`type(d) is dict`, and `isinstance(d, TD)` raises), so the cell's `type` is `dict` and the cell carries a `shape` reference to the declaration, which fixes the key universe with certainty (`Required` keys are must keys, `NotRequired` keys are may keys, `total=False` makes the undecorated keys may, and `ReadOnly` from PEP 705 forbids the value write) and the value type per key, inherited declarations merging their universes. The dictionary interface is admitted for reads and value writes (`d[k]`, `get`, `in`, iteration, `items`, `copy`, and `update` with an argument whose shape is a subshape); shape-altering operations are rejected (`del`, `pop` and `clear` on required keys, an undeclared key in a write or in an `update`). `"k" in d` promotes the may key `k` to must on the true branch; KeyError on `d["k"]` has `cond` false for a required key and open for a not-required one.

### 4.10 Class statements

In this section we define how a class cell is built by executing the class statement on the abstract state, and the admission test on its result.

The input is the abstract syntax tree, and a class statement is executed as PEP 3115 specifies, on the abstract state at the statement: the base expressions are evaluated to values whose pointer parts hold class cells, and a may set among them splits the disjunct set of the class graph (§4.2); `__mro_entries__` is resolved on a non-class base; the metaclass is computed as the most derived among the explicit `metaclass=` argument and the metaclasses of the bases, a conflict being a TypeError of the `dispatch` category; `__prepare__` is resolved on the metaclass and yields the namespace, a dictionary cell for the default and the summary's result for an analyzable override; the body is executed with the namespace cell as its scope, so assignments and `def` statements become its keys and function cells its values; the metaclass is called as in §4.4, its `__new__` computing the MRO by C3 within each disjunct, running `__set_name__` on the values and `__init_subclass__` on the parents, and its `__init__` following; the decorators are applied bottom-up, a decorator returning its argument leaving the cell in place and one returning another object producing a synthetic cell (§6); the class name is bound to the result. Metaclasses and decorators are user functions inlined like any other, or builtins with models (`ABCMeta`, `dataclass`, `functools.total_ordering`, the metaclasses of TypedDict and `enum`).

Name mangling is applied before execution: an identifier with two leading underscores and at most one trailing underscore, occurring anywhere in a class body including its methods, nested functions and comprehensions, as a name, an attribute name or a keyword, is rewritten to `_C__x` with `C` the class name stripped of leading underscores; dunder names are left alone. Owners in `keys` are the mangled names.

The admission test is on the result, not on the code: the class cell is admitted iff, at the end of the statement, the key set of the namespace is a must set with no `*` key and every value has a determinable kind. A metaclass that generates names from `*` strings fails the test and the statement is rejected. The cell keeps its keys, kinds and values; the function cells among the values keep their bodies for inlining and summaries; the statement's syntax tree is not kept. The instance universe of §4.9 is computed at the same time from the class body and the bodies of `__init__` along the chain.

Generated methods. A `def` or a `lambda` executed inside a metaclass's `__new__`, `__init__`, `__init_subclass__` or `__set_name__`, or inside a decorator, is an allocation of a function cell in that frame (§4.12): its code is the body's syntax tree and signature, its defaults are evaluated there, its globals are the metaclass's module, and its closure is the set of closure cells of that frame the body captures (`cls`, `name`, a field name, a `registry` dictionary allocated in the frame), which are heap cells (§4.13) and outlive the frame. `ns[name] = func` or `setattr(cls, name, func)` stores the cell under a key of the class cell inside the phase, with the kind derived from its class (§4.1), and §3.18 names it by that slot. Nothing is evaluated at that point beyond the `def`. Its effects are computed when a program calls it: `obj.m` binds the cell to the receiver, and the call inlines the body on the caller's state with the closure cells read at call time, so `self._data[fname]` or `registry[self]` writes through the ordinary transfers with whatever the captured cells hold then; the memo table of §4.11 keys on the input projection, which includes the closure cells' contents, so two generated methods with one code and different captures are analyzed apart. The loop-capture pitfall is reproduced by construction: getters defined in one loop share the loop variable's cell and read the last field, unless the code writes `fname=fname` or calls a factory, whose inlined call has a fresh frame and a fresh cell per field; §3.19 keeps such a loop exact when the field tuple is explicit. Generation by `exec` of a string has no syntax tree: the standard-library generators are builtin models (§4.21), and a project's own `exec` is rejected (§5.5).

### 4.11 Calls, summaries and contracts

In this section we define how calls are analyzed by inlining, what a call site receives from a callee, how recursion is detected and summarized, and what a contract denotes and how it is certified.

Inlining. A call to a function with an analyzable body is analyzed by inlining: the body is executed on the caller's state with the call string extended by the site, and every cell allocated in the body is named by (call string, syntactic site), so two frames of one function under different call strings have disjoint states and disjoint cells. States are never merged across distinct inputs. Two frames whose inputs coincide, projected onto what the callee can reach (its parameters, the cells reachable from them, and the globals it reads), have identical outputs, so a memo table keyed by that projection serves the second frame without loss.

Completions at a call site. A call site receives two kinds of completion from a callee: `normal`, from a `return` or from falling off the end, and `raise`; `break` and `continue` are bound to a loop in the callee's own body and cannot cross the boundary (§4.5). StopIteration raised by a function called in a loop body is an ordinary `raise` completion and leaves the loop without `else`; the `for` statement consumes StopIteration only from the iterator's `__next__`, which the loop's transfer treats as exhaustion, and a StopIteration raised inside a generator body is a RuntimeError under PEP 479. A contract therefore specifies `return T` and `raise E` completions only.

Recursion. Recursion is detected statically, as the strongly connected components of the call graph over the resolved candidate sets of §4.8, and dynamically, by the callee being on the frame stack; the static components decide the mode before analysis, and the dynamic check confines it to the cases that can recurse (a call over `{Circle, Group}` is recursive on the `Group` case only). The four situations are:

- body, no contract: the component is analyzed in summary mode. Its frames are not inlined further; it gets one input, the join of the entry state and of every recursive-call state, projected as above; its summary is the least fixpoint obtained by iterating the bodies of the component with the current summary at its internal call sites, starting from `⊥` (no completions, no writes), which terminates by §5.4. Allocation sites inside the component are named by the entry's call string and age and fold under k-recency (§3.5). The correlation between depth and state is lost, which the domain could not express in any case;
- body and contract: the bodies are analyzed once with the contract assumed at the internal call sites and the result is compared with the contract. A result below the contract makes the contract a post-fixpoint, hence above the least fixpoint, and it stands for every call in the component (the entry call may still be inlined one level). If the comparison fails, the least fixpoint is computed as in the first case and compared: a contract above it is sound although not a post-fixpoint, and is kept; a contract below it is unsound and is reported as a verification failure, never silently replaced;
- contract, no body: the contract summarizes the function and is recorded as a trusted assumption in the certificate. Recursion cannot enter it, but higher-order recursion can pass through it, which its callback clause carries;
- neither: rejected by default; under the `havoc` switch of §3.14 the call gets the sound `⊤` summary: any value under every class, any exception class, every cell reachable from the arguments and the globals weakly updated to `⊤`, and one summary cell of unknown class allocated. It exists to analyze around one missing model, and downstream obligations fail on it.

Contracts. A contract is written in the contract DSL and denotes an element of the summary lattice (input projection to completions and heap effects), so that its certification is a lattice comparison; its clauses are the components of that element:

- precondition: a predicate over the probes of the parameters (keys and their certainty, sign, emptiness, class set, must-alias between parameters); at a call site an obligation, discharged by the abstract state or passed to the verifier, then assumed for the body;
- footprint: the access paths from parameters and globals the function may read and write, everything outside it unchanged; this frame condition is what makes unmentioned cells sound, and it is certified against the body's writes when a body exists;
- heap effects on existing cells: per written path, a new abstract value, `unchanged`, or `havoc` within its class; effects on key certainty (an `__init__` contract establishes the must keys of the instance universe of §4.9) and on collection size and emptiness. Strength is not stated: the heap decides it from the target cell's existence and count (§4.1), so a contract cannot claim a strong update on a summary cell;
- completions: a table of guards over the probes to `return T` (an indexed value, possibly stated in terms of the probes) and `raise E` (a class set and the keys of the exception cell); machine-raised categories inside the callee are its own obligations under its pack and appear only when modeled there;
- allocation effects: each `allocates C` clause is a synthetic allocation site owned by the call site and behaves as any site under k-recency (aged cells for calls in straight-line code, a summary in a loop, `count ≥ 2` when the contract allocates unboundedly); the fresh cell's `type`, must keys and values come from the clause, and its pointer may appear in the return value or in a heap effect;
- callback clause: for a higher-order function, which parameter callables it invokes, with what argument abstraction, and that their `raise` completions become its own.

Nothing about termination is needed for partial correctness, and a contract with an empty footprint and no allocations is pure by construction. The verifier consumes contracts in every case, since it cannot inline a recursive call and the contract is its inductive invariant.

### 4.12 Callables

In this section we define the representation of callable objects and how a call site classifies its callee.

A callable is an object whose class defines `__call__` (in CPython, whose type has `tp_call`). The model has five kinds, all under pointer keys of the indexed value (§4.1):

- Function cells, allocated by the evaluation of a `def` statement or a `lambda`; a nested `def` is therefore an allocation site in its enclosing frame and ages and folds under k-recency. A function cell holds its code (the body and the signature: parameters, `*args`, `**kwargs`), its defaults as abstract values evaluated at definition time (a mutable default is one cell shared by every call, which the model reproduces), its globals (the module cell), its closure, and its own keys, since a function has a dictionary: the initialization phase of a function object is its `def` statement together with the decorators applied to it, so `functools.wraps` and `__wrapped__` are within the phase and a later `f.x = v` is outside the universe (§4.9). Its `type` is the `function` builtin cell, whose data descriptors serve `__name__`, `__defaults__` and the rest.
- Closure cells. A variable captured by a nested function is a cell shared by the enclosing frame and every function object closing over it; the frame reads and writes it through the cell, `nonlocal` writes it from inside, and the function reads it at call time rather than at definition time, so `[lambda: i for i in range(3)]` yields three functions reading the loop's final `i`. Strong updates apply when the cell is a singleton.
- Bound methods, produced by the read rule of §4.3 when a function is found on the chain: an immutable pair (`__func__`, `__self__`) of pointer parts carried on the value rather than as a cell, since CPython creates a fresh method object on every read and equality on it compares the two components. A bound builtin method (`xs.append`) is the same pair with a builtin summary as `__func__`.
- Class cells, callable through `__call__` on their metaclass (§4.4), and instance cells whose class resolves `__call__` (§4.4), including instances of `functools.partial`, modeled as a builtin class with a callback clause forwarding to its `func` with the stored arguments prepended.
- Builtin functions, cells of the builtin table with tabulated summaries (§5.2), including the higher-order ones (`map`, `sorted` with `key`) through callback clauses.

A call site classifies the callee by the keys of its value: a function key is inlined or summarized (§4.11), partitioned by function cell when several are possible; a method key runs its function with `__self__` prepended, per pair; a class key follows §4.4; any other pointer key resolves `__call__` on its class; a scalar key makes the TypeError edge live. Arity is checked against the signature of each function cell: the positional count and the literal keyword set against the parameters and defaults, `*args` and `**kwargs` binding to a tuple cell of definite size and a dictionary cell with must keys, so a wrapper `def wrapper(*args, **kwargs): return f(*args, **kwargs)` forwards an exact arity; a mismatch is a TypeError of the `dispatch` category. Recursion is detected on function cells, not on names, so a recursive closure and a recursive method are handled by §4.11 alike. Generator functions and coroutines are rejected (§5.2).

Decorators. A decorated definition is the definition followed by the call `f = deco(f)` for each decorator from the innermost outwards, at definition time, and the name is bound to the result of the last call, not to the function the `def` created. The result is one of three things: the same function cell, whose keys the decorator may extend within the phase (`functools.wraps` copies the name, the docstring and the annotations, sets `__wrapped__`, and merges the original's dictionary into the wrapper's); a new function cell, a wrapper closing over the original through a closure cell (§4.13), which inlining of the wrapper follows into the original; or an instance cell of another class with a `__call__` model and a callback clause to `__wrapped__` (`functools.lru_cache` returns an `_lru_cache_wrapper`). A decorator with arguments is `deco(args)` first and its result applied second. A method decorator runs during the class body, before the class object exists, and the namespace holds whatever it returns (`property`, `staticmethod`, a wrapper, a cache object), which §4.10 kinds when the class cell is built. The initialization phase of a function object (§4.9) therefore ends after its last decorator.

Code is static. A function object's code is the compilation of one `def` or `lambda` in the program text, and the only ways to obtain a code object that is not in the text are `exec`, `eval`, `compile`, the construction of `types.FunctionType` or `types.CodeType`, and assignment to `__code__`, all of which §5.2 rejects. The universe of code is therefore the finite set of `def` and `lambda` sites plus the builtin summaries, a closed universe like the literals and the class statements, and the code component of a function cell is exact in every cell. A callable the analysis is unsure of is a value whose pointer part is a may set of function cells, each with exact code; the domain of programs is the powerset of the sites and needs nothing richer. What abstract execution of the metaclass layer or of a decorator leaves uncertain is everything around the code, each of which is a value of the domain: which site (`ns[name] = f if flag else g` stores a may set, and a call through the slot is partitioned by callee), the closure (captures whose contents are joins, inlined as such), the defaults and the globals, the result of an uncertain decorator (one candidate per decorator, each with exact code), and the class of the stored object and hence its kind (a slot holding a function on one case and a `functools.partial` on the other has a may-kind, and the read rule partitions). The checks on the metaclass layer are then three: no runtime code construction, which keeps the universe closed; an exact key set for the namespace at the end of the class statement (§4.10), since a `*` key means the analysis does not know under which name a method was stored, which is the limit that exists, and it is a limit on names rather than on code; and a determinable kind for every entry, which fails only when the class of the stored object is outside the model. A `__getattr__` returning `lambda *a: self._call(name, *a)` has fixed code and a closure holding `name` as a `*` string, and a pipeline built by folding `lambda x: f(g(x))` over a list of functions has one lambda site whose closure holds may sets for `f` and `g` resolved at the inner calls; both are ordinary values.

### 4.13 Scopes and closures

In this section we define the classification of names, the allocation and status of closure cells, and the scope rules of class bodies and comprehensions.

Classification. CPython classifies every name of a function body statically, by its symbol-table rules: local, cell (a local captured by a nested function), free (captured from an enclosing function), or global (declared, or by default when the name is only read); a name assigned anywhere in the body without `nonlocal` or `global` is local for the whole body. The language module (Annex A.1) uses the same rules, so the classification is computed once per function and selects the transfer of each read and write: a local is a frame entry, a cell or free name goes through a closure cell (§4.12), a global goes to the module cell.

Cells. A closure cell is allocated at entry of the frame that owns it, with initialization status `uninitialized`, before any assignment; every function object created in that frame that captures the name shares the cell, and every read of the name, from the frame or from a closure, reads the cell at the time of the read. So a loop variable is one cell for the whole loop and closures created in the loop read its final value, and a default argument, evaluated once at definition time, is the way to snapshot a value. `del` on a cell name returns the cell to `uninitialized`. A read of an `uninitialized` cell is a NameError (free name) or an UnboundLocalError (local name) of the `dispatch` category with `cond` the initialization status (§4.6), so reading a captured variable before the enclosing assignment is discharged by the same component as any other uninitialized read.

Class bodies. The class body executes with the namespace cell as its scope (§4.10), but that scope is not an enclosing scope for the functions defined in it: an unqualified name in a method body resolves through the method's own classification to a global, never to the class namespace, so a class-level name is reachable from a method only through `self`, the class name or `__class__`. A comprehension in a class body evaluates its outermost iterable in the class scope and everything else in its own scope.

Zero-argument `super()`. The compiler gives every function that mentions `super` or `__class__` inside a class body a `__class__` cell, bound to the class object when the class statement completes; `super()` reads that cell and the function's first positional parameter and resolves as in §4.3. A `super()` in a nested function that has no such cell is a RuntimeError at run time; it is rejected statically, since the classification decides it.

Comprehensions. A comprehension has its own scope: its iteration variables do not leak into the enclosing function, its outermost iterable is evaluated in the enclosing scope and the rest in the comprehension scope, and a walrus target inside it binds in the enclosing scope (PEP 572). The inlining of comprehensions in 3.12 (PEP 709) changes none of this.

### 4.14 Collections

In this section we define the representation of sequences, dictionaries and sets, the existence of explicit positions, and the transfer of the collection operations.

Sequences. A list or tuple cell holds three segments: an explicit prefix of up to k positions `0, …, k-1`, an explicit suffix of up to k positions `-1, …, -k`, and a middle summary with one element value; the size and emptiness components of §4.1 describe the whole. An explicit position carries an existence status derived from the size, in the lattice of aged cells: position `j` exists iff the size is greater than `j`, position `-j` iff the size is at least `j`, so position `0` exists iff the cell is non-empty. With definite size `n ≤ 2k` the cell is fully explicit and the middle is empty; a tuple is a fully explicit cell up to `2k` and is a composite. An existing explicit position holds an exact value and takes strong updates; the middle takes weak ones. The collection cell itself is an allocation and ages and folds under §3.5 independently of its contents.

Operations. `append(v)` renames the suffix: `v` becomes position `-1`, each suffix position shifts by one, the former `-k` folds into the middle by a join, and the size increases by one; `pop()` shrinks the suffix and materializes the new `-k` from the middle with the summary's value; `pop(0)` and `insert(0, v)` do the same on the prefix; `insert(i, v)` with a literal `i` inside a window shifts that window. `xs[i]` with a literal or interval index reads the join of the positions the index may hit, the middle included when the interval may reach it, and writes strongly to one existing position or weakly to every position it may hit; an index with `*` is a weak read or write across all segments; the `cond` of the `index` category is `i ∈ [-size, size)` (§4.6). A slice read `xs[a:b:c]` never raises: out-of-range bounds clamp, so `xs[10:20]` on a short list is empty; with literal bounds inside the windows and a unit step it is a fresh explicit cell, with a definite size and a unit step it is explicit up to the windows, and otherwise it is a summary cell of size at most the source's. Slice assignment `xs[a:b] = ys` replaces the range and changes the size by `len(ys) - (b - a)`, explicit when both cells are fully explicit and summary with unknown size otherwise; `del xs[a:b]` renumbers the same way; an extended-slice assignment requires equal lengths, a ValueError of the `index` category. Bounds go through `__index__` (§4.19). `reverse()` swaps the windows; `sort()` keeps the size and sends every position to the join, smashing the windows into the middle; `extend` and `+` compose `append`. Iteration yields the join of the three segments, except over a fully explicit cell, where it yields each position in turn (§4.15). Size and emptiness follow each operation: `append` is size plus one and non-empty, `clear` is size zero and empty.

Dictionaries and sets. A dictionary cell holds up to L explicit literal keys, each with a value and a certainty (§4.1), and a `*` summary key with a summary value; a set cell holds up to L explicit literal elements with certainty and a `*` summary. Explicit literal keys of numeric classes are canonicalized across `int`, `float` and `bool`, since `1`, `1.0` and `True` are one key (§4.16). Insertion order is known when every key is explicit, so iteration over such a dictionary is precise, and it is the join of the keys otherwise. Exceeding L, or a write with a `*` key, smashes the explicit keys into the summary.

Element values are non-relational with each other: "sorted", "all distinct" and "each element aliases the previous one's `next`" are not expressible, and a list built in a loop has exact values for the last k elements appended and for the first k when they were appended before the loop.

### 4.15 Comprehensions

In this section we define the evaluation of list, dictionary and set comprehensions, the map and fold rules, and the treatment of filters, nested clauses and generator expressions.

Lowering. `[e for x in src if c]` denotes `acc = new(); for x in src: if c: acc.append(e)`, with `acc` allocated at the comprehension's site; the dictionary and set forms replace `append` by a keyed store and by `add`. The comprehension has its own scope (§4.13). The rule is chosen by analyzing `c` and `e` once on the witness, the element summary of `src` or any of its explicit positions, and reading the write footprint of that analysis (§4.11).

Map rule, for an empty footprint. The iterations are independent and the result is the image of `src` under `e` restricted by `c`. Over a fully explicit source, `c` is evaluated per position: must-true keeps the position, must-false drops it, and when every position is decided the result is a fully explicit cell of the kept values in order, of definite size. When some position's `c` is undecided, the later positions become uncertain, so the result is a summary cell whose element value is the join of the kept and undecided values, with size in `[must-kept, n]` and non-empty when at least one position is must-kept. Over a summary source the result's element value is `e` on the witness, its size is `n` without a filter and at most `n` with one, and it is maybe-empty with a filter unless `c` is must-true on the witness. Allocations inside `e` are ordinary allocations at the comprehension's site and age and fold under §3.5.

Fold rule, for a non-empty footprint. An iteration may read what the previous one wrote, so the lowering is analyzed as the loop it is, with the back-edge join of §4.5 and the fixpoint that §5.4 guarantees; the element value of `acc` is the join over the iterations of `e`, `acc` is a summary cell with `len(acc) ≤ len(src)` from the symbolic bounds of §4.1, and the state after the comprehension is the loop's exit state. A call inside `e` or `c` with a body contributes its analyzed footprint, one with a contract its declared footprint, so a pure contract keeps the map rule; a callee with neither is rejected, or under `havoc` forces the fold with `⊤` as the element.

Kinds. A list comprehension keeps duplicates and its size follows the rules above; a set comprehension deduplicates, and its result is explicit when the element bag of `e` has no `*` at every kept position and summary otherwise, with size at most the list's; a dictionary comprehension is explicit when the key expression's bag has no `*` at every kept position, a later duplicate overwriting an earlier one, and summary otherwise. Nested `for` clauses multiply: an explicit result needs every source explicit and the sizes multiply; an inner iterable that depends on the outer variable is evaluated per outer position under the map rule and inside the loop under the fold rule. A `raise` completion of `e` or `c` is a completion of the comprehension, and `acc` is unreachable after it.

Generator expressions. A generator expression is a generator and is rejected as such (§5.2), except in the argument position of a builtin that consumes it eagerly (`list`, `tuple`, `set`, `dict`, `sum`, `min`, `max`, `sorted`, `any`, `all`, `str.join`), where it denotes the corresponding comprehension; `any` and `all` stop early, which the fold rule covers as an unknown iteration count and which the map rule does not distinguish. `map` and `filter` follow the same rules through the callback clauses of their contracts.

### 4.16 Hashability

In this section we define the hashability sorts, their derivation from the class graph, the structural cases, the contract on `__hash__` and `__eq__`, and the equality facts the key model respects.

Sorts. Every class cell has a sort, Hashable or Unhashable, and every value has a sort in {must-Hashable, must-Unhashable, uncertain}, the join over its keys (§4.1). The verifier's datatypes have two sorts, `Hashable` and `MaybeHashable`, with an injection from the first into the second: a dictionary takes `Hashable` keys and `MaybeHashable` values, a set or frozenset takes `Hashable` elements, a list or tuple takes `MaybeHashable` elements. The analysis knows the sort of every value before encoding and places the injection; an uncertain sort encodes as `MaybeHashable`.

Derivation. `hash(o)` calls `type(o).__hash__`, so the sort of a class cell is `cand(C, "__hash__")`: a function makes it Hashable, `None` makes it Unhashable. The rules that place `None` are applied by the class-statement execution of §4.10, as `type.__new__` applies them: a body defining `__eq__` without `__hash__` gets `__hash__ = None`; `@dataclass` with `eq=True` and `frozen=False` gets `None`, with `frozen=True` a generated hash, with `unsafe_hash=True` a forced one, and with `eq=False` keeps identity; an explicit `__hash__ = None` is literal; a class with neither method is Hashable by identity. Builtins are tabulated: `list`, `dict`, `set` and `bytearray` are Unhashable and the rest Hashable, except that a tuple or frozenset is Hashable iff every element is: for a fully explicit cell the meet over its positions, otherwise the sort of its element summary, so `(1, [2])` is Unhashable and `tuple` appears in both sorts of the grammar.

Checks. A dictionary key, a set element and a frozenset element must be Hashable; a dictionary value, a list element and a tuple element may be MaybeHashable. These are the `cond` of the unhashable-key TypeError of the `key` category (§4.6): a must-Hashable key discharges it, an uncertain one leaves it to the pack, and a must-Unhashable one is a definite error.

Contract. The sort is the first of three conditions on a key:

- consistency: `a == b` implies `hash(a) == hash(b)`; admitted in two forms, the syntactic one, where `__hash__` and `__eq__` are generated from the same field tuple (a frozen dataclass, or `hash` of the tuple of the fields that `__eq__` compares), and the verified one, where both bodies are analyzable and the implication is an obligation for the verifier; rejected otherwise;
- stability: a key's hash must not change while the object is in a container; every hashable builtin is immutable and identity hashing is stable under mutation, so the condition is that a class with a field-based `__hash__` carries the frozen flag of §4.6, while an identity-hashed class may be mutable;
- purity: `__eq__` and `__hash__` have an empty footprint and no `raise` completion (§4.11), so that dictionary and set operations, which call them on every access and on every collision, need no calls in their transfers.

Equality facts. `1 == 1.0 == True` with equal hashes, so explicit literal keys of numeric classes are one key (§4.14). `nan != nan`, so a key whose `nan` flag is set is found by identity only, and a lookup with a fresh `nan` is a KeyError even on a dictionary that holds one.

### 4.17 Default arguments

In this section we define the evaluation and storage of default arguments, the binding of a parameter to its default, and the treatment of a default that is a heap object.

Concrete. Each default expression is evaluated once, when the `def` or the `lambda` executes, in the defining scope, and the resulting object is stored on the function object (`__defaults__`, a tuple, and `__kwdefaults__`, a dictionary). A call that omits the argument binds the parameter to that stored object, the same one on every such call; a call that passes the argument, even as `None`, does not touch the default; `*args` and `**kwargs` are fresh per call; there is no late binding. A default that is an integer, a string, `None` or a tuple of immutables is a value the parameter starts from; a default that is a list, a dictionary, a set or an instance is one object shared by every call that omits the argument, and a write through the parameter is visible on the next call. For a method the default is evaluated when the class body runs and is shared across the calls of every instance. The criterion is reachability, not the default's class: `def f(t=([],))` has an immutable default that reaches a shared mutable list.

Model. A default is evaluated at definition time on the state of the frame executing the `def` (module initialization for a top-level function, the class statement for a method) and stored on the function cell (§4.12). An immutable default is a scalar component of that value, and binding copies it. A mutable default is an allocation at the `def` site in that frame, an aged cell of the site, and the function cell's `defaults` holds a pointer to it; a call that omits the argument binds the parameter to that cell. Writes through the parameter are writes to the shared cell, strong while it is a singleton; along straight-line calls the accumulation is tracked under the window of §4.14, in a loop the window folds into the middle, and in summary mode (§4.11) the cell is reachable from the function cell and is therefore in the input projection, so recursion through a shared default is covered by the same fixpoint.

Binding. With literal keywords and positional counts the parameter is either the argument or the default. When a call forwards a `**kwargs` dictionary whose keys are not all explicit (§4.14), the parameter's value is the join of the default and the possible argument, and the arity check of §4.12 is uncertain, which is a `dispatch` obligation under the pack. The `acc=None` idiom is exact: the parameter enters keyed `{None, list}`, `if acc is None` narrows it, and `acc = []` allocates inside the call, so each inlined call has its own cell. A module-level sentinel (`_missing = object()`, `if x is _missing`) is a must-alias test on one cell. `functools.partial` stores its arguments on the partial cell (§4.12), the same sharing modeled the same way; a dataclass `field(default_factory=list)` allocates per generated `__init__` call, and the dataclass model rejects an unhashable plain default at class creation as dataclasses do, on the sort of §4.16.

Contracts and policy. A shared default cell is global state: a contract for a function that reads or writes it must name it in its footprint (§4.11), which certification checks when a body exists. Rejecting mutable defaults is a policy rather than a soundness question, since the model is exact and `def fib(n, cache={})` is a memoization idiom it handles; the switch `mutable-default-write` (§5.2) rejects a write to a cell reachable from a default under `strict` and allows it under `EAFP` and `full`, and reads are admitted under every pack. Assignment to `__defaults__` and `__kwdefaults__` is rejected (§5.2).

### 4.18 Unpacking

In this section we define assignment unpacking, starred targets, and argument unpacking.

Concrete. `a, b = rhs` evaluates `rhs` once, then iterates it: `iter(rhs)` and one `next` per target, with TypeError when `rhs` is not iterable and ValueError on a count mismatch. A starred target `a, *rest, b = rhs` needs at least the number of non-starred targets and makes `rest` a fresh list whatever `rhs` was. Targets are assigned left to right after the whole right side is evaluated, and a subscript or attribute target evaluates its subexpressions at its turn, so `i, xs[i] = 0, 5` stores into `xs[0]` and `a, a = 1, 2` leaves `2`. A tuple display on the right is built before any assignment, so `a, b = b, a` swaps. A dictionary unpacks its keys, a string its characters, an iterator is consumed.

Transfer. For each key of the right-hand value (§4.1): a class with neither `__iter__` nor the sequence protocol makes the TypeError edge of the `dispatch` category live; a sequence cell (§4.14) gives target `j` the value of position `j` when it is in the prefix window, of position `j - n` when it is in the suffix window, and the middle value otherwise, with the count condition `size = n` (or `size ≥ fixed` with a star) as the `cond` of the ValueError in the `index` row of §4.6; on the surviving edge the size becomes definite `n`, so a summary cell of unknown size with `n ≤ 2k` becomes fully explicit, its unknown positions materialized with the middle value. A starred target is an allocation at the statement's site, a list of size `n - fixed` with positions copied from the source's windows when `n` is definite and a summary of size at least zero otherwise, and the surviving edge narrows the source to `size ≥ fixed`. A dictionary cell unpacks its keys in insertion order when they are all explicit and the join of the keys otherwise; a string unpacks into single-character strings, which are not program literals, so each target gets `*` of definite size one under the `str` key; an iterator is rejected outside a `for` source. Nested targets apply the rule recursively; targets are assigned in order, each subscript or attribute target resolved by §4.3 and §4.14 at its turn.

Displays and returns. A tuple display unpacked by the same statement is lowered to a parallel assignment without an allocation, which the front end may do because the tuple is dead after the statement (Annex A.5). `return a, b` builds an explicit tuple cell, read exactly by `x, y = f()` under inlining, and a contract's `return T` may be a fully explicit tuple; `for k, v in d.items()` over an explicit dictionary yields per-key pairs by the map rule of §4.15.

Argument unpacking. `f(*xs)` binds positions to parameters by §4.20 and checks arity against the size of `xs`, exact when definite and a `dispatch` obligation otherwise; `f(**d)` binds keywords from the explicit keys of `d` and joins each parameter with its default when a `*` key is present (§4.17).

### 4.19 Operators and protocols

In this section we define augmented assignment, the values of `and` and `or`, rich comparisons, structural equality, the numeric tower, and the protocol methods the transfers consult.

Augmented assignment. `x op= y` evaluates the target's subexpressions once (`xs`, then `i`, for `xs[i] += v`), reads the target, resolves `__iop__` on its class, and, when that is absent or returns NotImplemented, applies the binary rule of §4.4; the result is then assigned to the target by the write rule of §4.3 or §4.14. For a list, `__iadd__` is `extend` in place and `__imul__` repeats in place, visible through every alias of the cell; for a set, `|=`, `&=`, `-=`, `^=` are in place; for a dictionary, `|=` is in place; for `int`, `str`, `tuple` and every immutable class, `__iop__` is absent and the statement rebinds the target to a fresh value. One row per class in the operator table decides which.

`and`, `or`, `not`. `a and b` is `a` when `a` is falsy and `b` otherwise, and `a or b` symmetrically; neither returns a bool. The transfer is: `a` narrowed by the falsy half of the truthiness test of §4.7, joined with the value of `b` evaluated on the state where `a` is truthy, when `a` may be truthy (and symmetrically for `or`), so the effects and completions of `b` are conditional on that branch. `not a` is the bool of the test. A chained comparison `a < b < c` is `a < b and b < c` with `b` evaluated once.

Rich comparisons. `a < b` resolves `__lt__` on the class of `a` and the reflected `__gt__` on the class of `b`, with the priority rule of §4.4 (the reflected method first when the right operand's class is a strict subclass overriding it); each is skipped when its summary may return NotImplemented, and when both are skipped the TypeError edge of the `dispatch` category is live, except for `==`, which falls back to identity, and `!=`, which is the negation of `==` unless `__ne__` is defined. The result is an arbitrary value; for the builtin pairs it is a bool: numeric classes compare across `int`, `float` and `bool`, `str` and `bytes` lexicographically, sequences lexicographically and elementwise, sets by inclusion, `None` only under `==` and `!=`, and comparisons with `nan` are false. `sorted`, `min`, `max`, `list.sort` and `in` call these methods, so a class used with them has `__lt__` and `__eq__` under the purity condition of §4.16.

Structural equality. `==` on two sequence cells is false when their definite sizes differ, the conjunction of the per-position comparisons when both are fully explicit, and unknown (the bag `{True, False}`) when a middle or a `*` key is involved; dictionaries compare key sets and values, sets compare element sets, and `!=` is the complement. `x in c` resolves `__contains__` (a hash lookup for a dictionary or set, decided on explicit keys and unknown on `*`; `==` per position for a sequence) and, on a class without `__contains__`, folds over `__iter__` as §4.15 does.

Numeric tower. Binary operations promote `bool` to `int`, `int` to `float`, and `float` to `complex`; `/` yields `float` (or `complex`), `//` and `%` floor toward negative infinity with the sign of the divisor, `divmod` gives both; `**` follows §4.4; `round(x)` yields an `int` by round-half-to-even and `round(x, n)` a `float`; integers are unbounded and bitwise operators act on the infinite two's complement, a negative shift count being a ValueError of the `value` category; `int()` and `float()` from a string are `value` raises, conversion of an out-of-range float to `int` and float overflow are `arith` raises (OverflowError), the `math` domain errors (`sqrt(-1)`, `log(0)`) are `value` raises, and `math.floor` and `math.ceil` yield `int`. Each rule is a table cell over the components of §4.1 (bag, sign, interval, `nan` and `inf` flags) per key pair, and `nan` propagates through every arithmetic operation.

Protocols. The transfers consult a fixed set of methods, each with its result condition: `__index__` for subscripts, slice bounds and `range`, which must yield an `int` (TypeError otherwise); `__int__` and `__float__` for conversions; `__bool__` then `__len__` for truthiness (§4.7), `__len__` yielding a non-negative `int` (TypeError, ValueError otherwise); `__contains__` as above; `__reversed__`, or `__len__` with `__getitem__` on a class without it; `__iter__` and `__next__` through `for` only (§4.15). Iteration of a class with `__getitem__` and no `__iter__` (indexing from zero until IndexError) is rejected (§5.2).

### 4.20 Signature binding

In this section we define the binding of arguments to parameters.

A signature has positional-only parameters (before `/`), positional-or-keyword parameters, an optional `*args` or a bare `*`, keyword-only parameters, and an optional `**kwargs`, with defaults on any parameter that admits them (§4.17). Positional arguments fill the positional-only and then the positional-or-keyword parameters in order; a surplus goes to `*args` or is a TypeError. Keyword arguments bind positional-or-keyword and keyword-only parameters by name; a keyword naming a positional-only parameter or an unknown name goes to `**kwargs` or is a TypeError; a parameter bound twice is a TypeError; a parameter left unbound takes its default or is a TypeError. All of these TypeErrors are the arity edge of the `dispatch` category. A bound method prepends `__self__`; a class call binds `__new__` and `__init__` separately (§4.4); a builtin's contract carries its signature.

The abstract binding is exact when the positional count and the keyword names are literal, which they are at every direct call. With `*xs` the count is the size of `xs`, exact when definite and otherwise a join over the possible counts with the edge live; with `**d` the names are the explicit keys of `d`, must keys binding for sure, may keys joining the parameter with its default, and a `*` key making the edge live (§4.18). `*args` binds to a fresh tuple cell of definite size when the count is known, and `**kwargs` to a fresh dictionary cell whose keys are the surplus keywords with their certainty, so a forwarding wrapper preserves exact arity through one level.

### 4.21 String formatting and the builtin models

In this section we define string formatting and the builtin models the workload needs beyond the collection classes.

Formatting. An f-string evaluates each replacement field in order, applies the conversion (`str`, `repr`, `ascii`), and calls `format(value, spec)`, which resolves `__format__` on the value's class; `object.__format__` with a non-empty spec is a TypeError. `str(o)` resolves `__str__` and falls back to `__repr__`; both are called by formatting and by `print`, so they are under the purity condition of §4.16 or are modeled. `%` formatting raises TypeError on an argument count mismatch (`dispatch`) and ValueError on a bad specifier (`value`); `.format` raises KeyError or IndexError on a missing field (`key`, `index`). The result of every formatting operation is `*` under the `str` key, non-empty when a literal part is non-empty; when every part is a literal bag without `*` and every conversion is the identity, the bag of the concatenation is computed instead.

`hasattr(o, name)` is `getattr` with the AttributeError edge turned into a value: `True` when `name` is not absent on every class of `o` and in the instance's must keys or a must owner, `False` when it is absent on every class and not in the may keys, and the bag `{True, False}` otherwise; the true branch narrows as a surviving `getattr` does (§4.7) and the false branch to the classes where the name is absent.

Builtin models. `collections.defaultdict` is a dictionary cell with a `default_factory` callback clause: a read of a missing key calls the factory, stores the result under the key, and returns it, so the KeyError edge is dead and each miss is an allocation when the factory allocates; `Counter` is the same with `0` as the factory's value and no store on read; `OrderedDict` is a dictionary with `move_to_end` and `popitem(last)` acting on the explicit key order; `deque` is a sequence cell whose prefix and suffix windows are its two ends, with `maxlen` as a definite size bound and `appendleft`/`popleft` as the prefix operations of §4.14; `namedtuple` and `typing.NamedTuple` generate a class cell that subclasses `tuple`, with `_fields`, a data descriptor per field bound to a position, and a fully explicit instance cell; `enum.Enum` generates a class cell whose members are instance cells that are also its class attributes, each with `name` and `value`, identity comparison, iteration in definition order, `Color(v)` as a lookup by value with a `value` raise on a miss and `Color["NAME"]` as a lookup by name with a `key` raise, `auto()` as consecutive integers, and `IntEnum`/`StrEnum` inheriting the sort of §4.16 and the operators of their base.

## 5. Soundness

In this section we give the concretization, the admission rules the argument rests on, the precision limits, and the termination and cost argument.

### 5.1 Concretization

In this section we state the concretization and the shape of the soundness argument.

A concrete state is a heap graph: objects with an `ob_type` edge, class objects with `tp_bases`, `tp_mro` and `tp_dict`, storage maps, and an environment. The concretization of an abstract heap is the set of concrete graphs admitting a homomorphism onto it that maps every object to a cell of the right kind, every edge to a may edge, every present key to a may key, every must key to a present key, every aged cell `sⁱ` with `exists = present` to the i-th most recently allocated object at `s` (to nothing when `absent`, to either when `maybe-present`), every summary to the remaining objects of its site with a number of them in the concretization of `count`, and every `tp_mro` to a linear extension of the cell's `precedes` (C3-valid when the metaclass does not override `mro()`) over a set between `must` and `may`. The concretization of an indexed value is the union over its keys of the concretization of each component (§3.11). A concrete completion is a kind paired with a state and the site that produced it, and the concretization of the buffer of §4.5 is the union, over its completions, of the concretization of the completion's state tagged with its kind and site, a completion with source `⊤` standing for any site. Concrete resolution, call dispatch, handler matching and the routing rules of §2.2 are functions of the concrete graph and completion; their abstract versions in §4 are monotone over-approximations under the homomorphism, because each step of the concrete walk stops at a dictionary that the abstract candidate set contains, or fails where the abstract edge is live, and each routing rule of §4.5 is the concrete rule applied to each completion. The same argument covers class reads and metaclass reads, since a class cell's `meta` is a type edge like any other and no rule inspects which layer it is on.

### 5.2 Admission rules

In this section we list the concrete behaviours that would change the content of a class cell after its creation, bypass the resolution rule, or invalidate a narrowing, and how each is handled.

- Assignment to `__bases__` or `__class__`: admitted in module initialization, while the class graph is being built on the disjunctive level (§4.2); a `__bases__` assignment recomputes the MROs of the assigned class and of its subclasses by C3 within each disjunct, a `__class__` assignment moves the `type` edge, and both are pruned by CPython's layout check, which confines the new bases or class to the solid-base partition of the old one. Rejected in function bodies, after the graph is frozen (§3.2).
- `del` on a class or instance attribute: rejected; it rewrites a key set the abstraction treats as constant.
- A write to a name outside the universe of the receiver's own storage, a first assignment outside the initialization phase, a change of an entry's kind, and `setattr` or `delattr` with a non-literal name (§4.9): rejected; the universe is fixed at the end of the phase and only values are mutable.
- Assignment to `__dict__`, and to `__code__`, `__defaults__`, `__kwdefaults__`, `__closure__` or `__globals__` of a function: rejected.
- A write to a cell reachable from a default argument (§4.17): rejected under `strict` and allowed under `EAFP` and `full`, by the `mutable-default-write` switch; reads are admitted under every pack.
- A metaclass whose `__call__`, `__prepare__` or `__new__` has neither an analyzable body nor a model, and a class statement whose namespace key set is not a must set without `*` keys at its end (§4.10): rejected.
- Overrides of `__setattr__`, `__delattr__`, `__getattr__` and `__getattribute__`: `o.x = v` runs `type(o).__setattr__`, so an override is itself a resolution on the class cell; it is routed through `cand` when the override is analyzable, and the class is rejected otherwise.
- Overrides of `__instancecheck__` and `__subclasscheck__`, and `ABCMeta.register`: `register` adds to `virtual`; other overrides are rejected. `__subclasshook__` on the `collections.abc` classes tests whether a method resolves and is answered by `cand`.
- `is` on integers and strings: rejected, since interning makes the result implementation-defined and the heap facts of §4.7 would be unsound.
- Metaclasses overriding `mro()` with a body that is not a list literal or a filtered `super().mro()`: rejected (§4.2.3).
- Subclasses of builtin collections overriding `__getitem__`, `__missing__`, `__len__` or `__contains__`: rejected; origin narrowing (§4.6) assumes the table cell is the only source of the exception class at the site.
- `return`, `break` and `continue` that exit a `finally` block: rejected under language version 3.14 and later, modeled by the override rule of §4.5 before (§3.8).
- `except` clause expressions other than a class name or a tuple of class names: rejected; a class expression that raises at match time would be a new pending completion.
- `yield` and `await`: rejected; each adds a third expression completion (§3.7). A generator expression is admitted only in the eager argument positions of §4.15.
- A class with a field-based `__hash__` and no frozen flag, an `__eq__` or `__hash__` with a non-empty footprint or a `raise` completion, and a `__hash__` and `__eq__` pair whose consistency is neither syntactic nor verified (§4.16): rejected.
- Reads of `__context__` and `__cause__`: rejected; a replaced completion is discarded rather than chained.
- `assert` statements: treated as user raises of AssertionError; the `-O` flag, which removes them, is not modeled.
- Mutation of a dictionary or set during iteration over it (RuntimeError): rejected.
- Iteration of a class by `__getitem__` without `__iter__`, `except*` and exception groups, `__del__`, weak references, threads and `asyncio`, `eval`, `exec`, `compile`, `types.FunctionType`, `types.CodeType`, `globals()`, `locals()`, `from m import *`, dynamic imports and import cycles, `memoryview` and `ctypes`, `pickle`, and `contextlib.contextmanager` without a model: rejected (§5.5).
- Builtin types: class cells with exact `precedes`, exact `keys` with kinds, and tabulated summaries for their methods, including the category of each raise they can produce.

### 5.3 Precision

In this section we state what the domain does not capture.

After a collapse (§3.3) the order domain is non-relational across names and across classes, and the cardinal power is non-relational across variables: a function returning `(int, int)` or `(None, None)` yields two values each tagged `{int, None}`, and the partition recovers the correlation only when a test on one of them splits the state. The disjunctive level of §3.3 is the repair for the first, up to its cap; trace partitioning on the test is the repair for the second. Summary cells with `count = ≥2` receive weak updates only, so must keys are created in constructors and in strong updates to aged cells, and a write to an object older than the k most recent at its site leaves the AttributeError edge of a later read live unless the key was already a must key.

### 5.4 Termination and cost

In this section we state why the analysis terminates without widening, what bounds its cost, and the condition the reductions have to satisfy.

Every component of the state has finite height: sets over the program's names, cells, classes and literals; the order domain of §4.2, with height at most `|V|(|V|-1)/2 + 2` per class; the sign, initialization and emptiness lattices; and the definite-size component, which is flat (height 2, infinitely wide), so a size that grows in a loop reaches unknown at the loop head in one step rather than climbing. The cardinal powers of §4.5 and §4.7 are keyed by finite sets, so the state lattice has finite height, polynomial in program size. With monotone transfer functions, Kleene iteration from bottom therefore reaches the least fixpoint: there is no widening or narrowing pass, the result does not depend on iteration order or on the choice of widening points, and it is the same under every worklist strategy. Precision is lost only where the domain is non-relational (§5.3), so a disagreement with the oracle of §6 is a transfer-function error or an admission gap and never an extrapolation.

Cost is bounded by state size rather than by iteration count. The height bounds the number of iterations, and the size of a state is the sum, over the live partition keys and buffered completions, of the size of one state; keys multiply when a site sits inside a loop, inside a handler, with several candidate receiver classes, under several disjuncts of the class graph. The invariant that keeps both finite is that every abstract universe is drawn from program syntax (literals, names, allocation sites, class statements) and every disjunctive component has a cap and a rule for what exceeds it: the literal bag collapses to `*`, the k-th aged cell folds into the summary, the disjunct set of §3.3 collapses to the order domain, the window of a collection folds into its middle (§4.14), and the completion buffer of §4.5 joins its surplus into a completion with source `⊤`. Components that would break the invariant are intervals over unbounded integers, congruences, string prefix or suffix domains, and length intervals; the symbolic bounds of §3.6 keep it, because their bound set is the finite set of `len(x) + c` expressions in the program.

Alternatives for the iteration in the presence of reductions: (a) plain Kleene iteration on `reduce ∘ f`, with each reduction audited for monotonicity; (b) iteration of `x ⊔ F(x)`, which produces an ascending chain regardless of monotonicity.

We adopt (a). A reduction that is decreasing but not monotone can make plain iteration oscillate in a finite lattice, and (b) removes the risk at the price of a post-fixpoint that may lie above the least one. The reductions of §4.7 are few, and each is a set intersection (tests and surviving edges), a bijective renaming (allocation) or a join (the fold), all monotone, so (a) keeps the least fixpoint.

### 5.5 Feature coverage

In this section we record which Python features the domain covers, which are deferred, and which are rejected with the reason.

Covered by the sections above: the object model and its uncertainty (§4.1 to §4.4, §4.8 to §4.10), completions and exceptions (§4.5, §4.6), closures, decorators and callables (§4.12, §4.13), collections, comprehensions and hashability (§4.14 to §4.16), default arguments, unpacking, operators and protocols, signature binding, formatting and the builtin models (§4.17 to §4.21), and, through the tables of §4.6, the exception categories of each.

Deferred: `match`/`case` (PEP 634). It lowers to operations the domain has: literal patterns are bag equality with `None`, `True` and `False` by identity, value patterns call `__eq__`, capture patterns are assignments, sequence patterns are the unpacking of §4.18 with the extra tests that the subject is a `Sequence` and not `str`, `bytes` or `bytearray`, mapping patterns are key membership with `.get` calls and a fresh dictionary for `**rest`, class patterns are `isinstance` narrowing with attribute reads through `__match_args__` (a builtin class matches the whole subject positionally), guards are `if`, and there is no fallthrough, so the statement is an `if`/`elif` chain. The one subtlety is that bindings are not atomic: a capture binds even when a later sub-pattern or the guard fails, so after the statement those names are maybe-initialized. It is deferred for the size of its binding logic, not for its semantics.

Rejected, with the reason:

| feature | reason |
| --- | --- |
| iteration by `__getitem__` without `__iter__` | couples iteration to the `index` category; rare |
| `except*`, ExceptionGroup | new matching semantics and partial re-raise |
| `sys.exc_info`, `__traceback__`, `__context__`, `__cause__` | frames and chaining are outside the state |
| `__del__`, weak references, `gc` | finalization timing is not a function of the program |
| `eval`, `exec`, `compile`, `types.FunctionType`, `types.CodeType`, `globals()`, `locals()`, dynamic `setattr`/`delattr` | code and names outside the syntax tree (§4.12) |
| threads, `asyncio`, signals | single-threaded execution is an assumption of the certificate |
| generators, coroutines, `yield`, `await` | a third expression completion (§3.7); generator expressions in eager positions are admitted (§4.15) |
| `contextlib.contextmanager` | generator-based; the common managers get models |
| `from m import *`, `importlib`, import cycles | names outside the syntax tree; partially initialized modules |
| `memoryview`, buffers, `ctypes` | shared mutable memory outside the object model |
| `pickle` | arbitrary reconstruction; `copy.deepcopy` is a contract allocating a summary graph |

## 6. Staging and validation

In this section we give the order in which the sources of uncertainty are admitted and the method for checking each stage against CPython.

| stage | admits | domain change |
| --- | --- | --- |
| 0 | decorators that return their argument and do not modify its namespace (registration, `typing.final`) | none: the decorator is analyzed and the class name rebound to its result |
| 1 | decorators and metaclasses that inject names with the order left exact (`functools.total_ordering`, `dataclass` through a builtin model, `ABCMeta`) | may entries in `keys`; `precedes` stays total |
| 2 | unknown order over a known candidate set (`bases` edited by an analyzable metaclass `__new__`, `__mro_entries__` with an unknown substitute) | a split of the graph set; `precedes` and may/must ancestors after a collapse |
| 3 | class-attribute reads through the metaclass | resolution on `meta` (§4.3) |
| rejected | `mro()` overrides that resist analysis | none |

`dataclass` returns its argument but generates methods by `exec`, so analyzing the decorator recovers the order and not the namespace; it belongs to stage 1 with a model, not to stage 0. A decorator returning a new class object (`dataclass(slots=True)`) yields a synthetic class cell whose `bases` are those of its argument.

Validation is differential against CPython and keyed by pack: a golden is a triple of program, pack and expectation. For each class in a test program the oracle records `__mro__`, `__bases__` and the owner of each member name; for each raising site it records the exception raised, its category, and the clause, if any, that caught it. The analysis output is accepted when every candidate set contains the recorded answer and, at each recorded raise, the site's category has policy `abort` and the output carries an obligation there, or the policy is `model` and the output carries a live edge caught by a clause whose narrowed set (§4.6) contains the recorded class, or the policy is `assume`. Precision per stage is measured as the number of dispatch sites that devirtualize and the number that split, counted by target (§4.8), on the same programs and under the same pack.

## Annex A. A language-generic interpreter

In this annex we describe what separates the language-independent core of the interpreter from a language module (A.1), the interface through which a module supplies its rules (A.2), the labels that JavaScript and Java completions need (A.3), what each of those two languages changes in the module (A.4), and the choice between a syntax-directed interpreter and a control-flow-graph one (A.5).

### A.1 Core and module

In this section we list what the interpreter shares across languages and what a language module supplies.

The core is the heap of §4.1 (cells, k-recency, existence, key certainty), points-to and must-alias, the scalar components parametrized by a literal universe, completions and their buffering (§4.5), the partitions by kind, receiver class and source, the reduction plumbing of §4.7, the finite-height fixpoint of §5.4, and the policy mechanism of §4.6 (the values, the packs, and the use made of a site's `cond`) without its table.

A module supplies the resolution theory (what the type edge points to, the ancestor structure, the lookup rule, the call rule, and whether the class graph is constant), the operator tables with their result tags and exception categories, truthiness, the scalar constructors and their literal universes, the binding rules for names (§4.13 for Python), the builtin cells and their summaries, the category table with its default packs, and the admission rules. For Python these are §2.1, §4.3, §4.4, the table of §4.6, and §5.2.

### A.2 Module interface

In this section we define the two kinds of rule a module supplies and the form each takes.

Alternatives: (a) one rule language for everything, a declarative DSL interpreted at analysis time; (b) one host-language implementation per language, with no shared interpreter; (c) declarative data for the rules that are tables, and host-language functions supplied through a typeclass for the rules that are transfer functions.

We adopt (c). Dispatch rules are tables: a cell per operator and tag pair with a result tag and a category, a lookup order, a truthiness row per tag, a category per builtin raise. They are data, they are compared and diffed as data, and a DSL expresses them completely. Transfer rules are not tables: an allocation renames the state (§4.1), a test narrows several components at once (§4.7), a call routes completions (§4.5), a `finally` re-runs a body per pending completion; each reads and writes the abstract state with sequencing, iteration and the state's full type. Under (a) the DSL grows into a programming language; under (b) the core is written once per language. Under (c) the interpreter is one function, generic in a typeclass `LangSemantics L` whose fields are: the op type of the module's IR extension; the language version, which selects the version-dependent rules (the exits from `finally` of §3.8); the literal universe; the dispatch tables, as data; the resolution theory, as a record of functions (`resolve`, `call`, `kind`); the transfer function per op, from a state to a state and a buffer; the narrowing function per test form; and the category table. The core IR is a fixed inductive type with the module's ops as a parameter, so the interpreter's own code names no language.

### A.3 Labels

In this section we extend completions with labels.

A `break` or `continue` completion carries an optional label. A loop or a labeled block consumes a completion whose label is absent or equal to its own and propagates the others; `switch` in JavaScript and Java is a labeled block for `break`, with fallthrough as the sequencing of its cases. The buffer key of §4.5 becomes (kind, label, class, source site). Python's completions are the label-free instance, so the extension changes no Python rule.

### A.4 JavaScript and Java

In this section we state what each language changes in the module and what it leaves in the core.

JavaScript: the type edge is `[[Prototype]]` and its target is a mutable heap object, so class cells leave the static graph of §3.2 for the per-state heap under k-recency, and the ancestor structure is a chain, a total order in the domain of §4.2, changed by `setPrototypeOf`. The lookup rule is own property then chain, with accessor properties in the data-descriptor position; a miss yields `undefined` rather than a completion, so the `dispatch` category produces a value, and the miss condition narrows the receiver as in §4.7. `var` hoisting and the temporal dead zone of `let` are the initialization lattice with a ReferenceError category; truthiness adds `NaN`, `""` and `undefined` to the false values; `return` in `finally` overrides and is admitted, which is the pre-3.14 setting of the version switch of §3.8.

Java: the type edge is the runtime class in a static class graph, the ancestor structure is a chain plus interfaces with a fixed resolution for default methods, and the lookup rule is static except for virtual dispatch on the receiver's class. Declared types feed §4.8 as assumed facts, so candidate sets are closed by the type system. Checked exceptions are `model` by default; the `dispatch` category is NullPointerException, ClassCastException and ArrayIndexOutOfBoundsException, with `cond` from nullness, the class set and the size component; integer overflow wraps, so `arith` reduces to division by zero. `finally` overrides as in JavaScript.

### A.5 Syntax-directed or control-flow graph

In this section we choose the form of the interpreter.

Alternatives: (a) a syntax-directed interpreter over a region-structured IR, as in §4.5; (b) a worklist over a control-flow graph with exceptional edges; (c) (a) as the core, with reducible graphs raised to regions by a relooper and irreducible ones analyzed by (b) inside an opaque region whose exits are its completions.

We adopt (c). Under (a) every mechanism of §4.5 is carried by the traversal: `finally` runs per pending completion by re-running its body, the buffer keeps sources apart, and a control-dependence label is scoped by nesting. Under (b) each becomes an explicit device: `finally` is duplicated per exit or driven by a completion register whose value partitions the block, sources are kept apart by one exceptional edge per (site, class) and a partition of the handler by predecessor edge merged at its exit, control dependence needs postdominators, and loops need the worklist; nothing in §5.1 depends on the choice, and the routing rules of §4.5 become edge construction in the front end. (b) accepts any input and (a) needs structured input. (c) keeps the interpreter as specified and moves graph-shaped inputs to the front end: a reducible graph becomes regions with labeled `break` and `continue` (Ramsey, "Beyond Relooper", ICFP 2022), bytecode inputs carry exception tables that already define the handler regions, and CPython duplicates `finally` at compile time, so raising is cheap for them; only an irreducible graph pays for (b), and it pays inside one region.

## Annex B. Taint analysis and information flow

In this annex we define the two properties that are both called "information flow" (B.1), specify the taint component POMAD can carry and the property it establishes (B.2), record the decision on implicit flows and side channels (B.3), and fix the vocabulary the reports use (B.4).

### B.1 Two properties

In this section we distinguish explicit-flow taint tracking from information-flow security.

Taint tracking is a property of single executions over an instrumented semantics: every value carries a provenance set of source sites, an operation unions the provenance of its operands according to a propagation table, control flow leaves provenance untouched, and the property is that no value whose provenance contains a source of class S reaches a sink of class S. It is a trace property, checked one run at a time, and it captures data dependence only: the attacker controls the bytes of a value, and the question is whether those bytes reach a sink. This is what injection defenses need (SQL, shell, path, HTML), and it is what the deployed tools compute (Pysa, CodeQL, and the analyses in the tradition of Livshits and Lam 2005 and Tripp et al. 2009).

Information-flow security, in the sense of non-interference (Goguen and Meseguer 1982), is a property of pairs of executions: any two runs that agree on the public inputs agree on the public outputs, whatever the secret inputs. It is a 2-safety hyperproperty (Clarkson and Schneider 2010), not a trace property, and it is what confidentiality needs. Denning and Denning 1977 and the type system of Volpano, Smith and Irvine 1996 enforce it by tracking, in addition to data dependence, the control dependence of every assignment on the conditions that guard it, the implicit flows: after `if secret == k: x = 1 else: x = 0`, `x` carries the secret's label although it was assigned from constants, and so does every variable assigned in either branch, and every statement that runs only because a guarded abrupt exit did not take place (the exceptional `pc`). With implicit flows tracked, non-interference still comes in flavours that differ on what the observer sees: termination-insensitive variants ignore whether the program terminates and termination-sensitive ones do not; timing-sensitive variants require that execution time not depend on the secret, which no abstract domain over program syntax can establish, since time is a property of the machine; and further channels (memory, cache, exceptions observed from outside, resource exhaustion) each add an observation. The two properties are not a weaker and a stronger version of one thing: taint is a trace property about the integrity of data, and non-interference is a hyperproperty about confidentiality under an observer model that has to be stated.

### B.2 The taint component and the property it establishes

In this section we specify the taint component and state what it proves.

Component. A label is a map from sink class to a may set of source sites, carried on the scalar part of an indexed value (§4.1) under every key, and meaningful only on `*` values: a value in the literal bag is a program constant and its label is empty by construction. Sources are rows of the builtin tables (§5.2): `input`, `os.environ`, `sys.argv`, file reads, a framework's request object, each returning `*` with its site under the classes it taints. Sinks are rows too, and a sink of class S at a call site is an obligation `label(arg)[S] = ∅`, in the `abort` tier of §4.6 and discharged like a fatal edge: statically when the argument's bag has no `*`, by the verifier otherwise. Sanitizers are rows that return a fresh `*` with the label cleared for their class (`html.escape`, `shlex.quote`, a parameterized query API); a validator that returns a bool is control rather than data and does nothing under this component, so the admitted form is the one that returns the value (`x = validate(x)`, raising on bad input), which the trusted-code threat model lets a project enforce. The propagation table is per operation and per key: concatenation, `%`, `.format`, f-strings, `join`, slicing and `str()` of a labelled value propagate; comparisons yield unlabelled booleans; `len` and arithmetic cut the label for the injection classes and keep it for a class that opts in; a value stored in a cell carries its label in `values`, so containers, attributes and exception cells propagate through the ordinary transfers. Two facts of the domain act as sanitizers without a model: the literal narrowing of §4.7 (`x == "admin"`, `x in ("a", "b")`, `x in table` for a dictionary with explicit keys) leaves `x` with a bag and therefore no label on the true branch, and a lookup `table[x]` on that branch reads literal values.

Property. Over the instrumented semantics of B.1, the label is a may over-approximation of provenance, and the argument of §5.1 applies unchanged (labels are may sets, joins are monotone, the height is the number of source sites). The property established at a sink of class S is explicit-flow integrity: on every execution, the provenance of the argument excludes every source of class S. The threat model is the standard one for injection: the program is trusted and its inputs are not. The claim does not cover laundering through control, `out = ""; for c in x: if c == "a": out += "a"; ...`, which rebuilds `x` from constants with an empty label; that requires adversarial code, which the threat model excludes, and it is the boundary of the claim rather than a defect of the tracking. Attacker-controlled choice among constants (`role = "admin" if x == k else "user"`) is not flagged either, and it is bounded by the bag: an enumeration obligation at the sink ("every member of the bag is an allowed table name") is the check for it, and it is stronger than a taint bit.

### B.3 Implicit flows and side channels

In this section we choose whether the component tracks implicit flows, and we state what remains outside any abstract interpretation.

Alternatives: (a) explicit flows only, as in B.2; (b) explicit flows plus a program-counter label per sink class, joined into every assignment under a guard whose condition carries the class, with the merge rule (every variable assigned in either branch takes the guard's label) and the exceptional-`pc` rule (a guarded abrupt exit extends the label to the continuation until the paths rejoin, which the completion buffer of §4.5 carries as a `pc` on each completion); (c) non-interference proper, as a relational verification condition on the self-composition of the program (Barthe, D'Argenio and Rezk 2004), discharged by the verifier.

We adopt (a) as the default, (b) as an opt-in per sink class, and we place (c) outside the abstract interpreter. Under (a) the injection classes get the property they need and labels stay sparse. Under (b) a confidentiality class (a secret reaching a log or the network) gets termination-insensitive non-interference on the admitted subset, at the cost that nearly every value downstream of a branch on the secret is labelled, which is the correct answer for confidentiality and noise for injection; (b) also invalidates the literal-narrowing sanitizer for that class, since knowing which branch was taken is information about the value. (c) is a different kind of obligation, two copies of the program and an equality of their public outputs, which the SMT encoding can express for one function and the domain cannot express at all; it is the only route to a claim about a hyperproperty. No option provides timing, memory or termination channels: a discrete domain over the syntax tree has no notion of time, and the termination channel is a property of loop structure that (b) ignores by construction. Exceptions as a channel are covered by (b) to the extent of the exceptional `pc`: a `raise` under a secret guard labels the continuation, but an exception observed by a handler outside the program is an output that the observer model has to include explicitly.

### B.4 Vocabulary

In this section we fix the terms the tool's reports and its documentation use.

Under (a) the tool reports "taint" or "explicit-flow integrity" for a sink class, naming the source classes, the sanitizers and the threat model; it does not report "information flow", "non-interference" or "no leak". Under (b) it reports "termination-insensitive non-interference on the admitted subset" for the classes that opt in, and it names the channels not covered: termination, timing, memory, and every observation outside the declared sinks. Under (c), when the verifier discharges a self-composition condition, the report says for which function, which public outputs and which observer model. A report that says "information flow" while tracking explicit flows only overstates by one hyperproperty, and the overstatement is a false statement rather than a loose one: a user who reads "no information flow from the password to the log" and receives explicit-flow tracking has been told something false about `if password == guess: log("ok")`.