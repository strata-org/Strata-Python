# CPython as an oracle for the Python front end

CPython's own regression suite states, in executable form, what Python means. This
suite takes test methods from it, rewrites each into a self-contained program, runs
that program under **`pyInterpret`** and under **CPython**, and compares. There are no
`.expected` files: **CPython is the expectation.**

    bash run_cpython_oracle.sh                      # whole manifest, ~130s
    bash run_cpython_oracle.sh --filter test_dict --keep
    bash run_cpython_oracle.sh --workers 8

It runs with the other suites by default (`StrataPythonTestExtra/CpythonOracleTest.lean`);
`CPYTHON_ORACLE=0` skips it.

## What the suite is for

**A construct Strata cannot handle is a RESULT, not a reason to look away.** The
selector excludes a method only when the generated program would not *mean* the same
thing as the original. Everything else is attempted on purpose, so most methods
currently come back as coverage gaps — that is the intended output, not a problem.

Consequently a finding does **not** fail the run — failing on gaps would leave the
build permanently red and train everyone to ignore it. What fails is a **change from
the recorded baseline**.

## baseline.txt

`baseline.txt` records the outcome for every method — one line, `<stem> <bucket>` — and
is checked in. It is a single file rather than the one-file-per-case convention the
golden suites use, because there is one datum per method and nothing to diff within it.

    bash run_cpython_oracle.sh            # diff against the baseline; any change fails
    bash run_cpython_oracle.sh --update   # record the current state

A difference fails in **either** direction, and the run prints which methods moved:

* a method that used to `agree` and no longer does is a **regression**;
* one that used to be a gap and now agrees is an **improvement**, and recording it makes
  the file double as a coverage log.

This is what makes the suite a test rather than a report. Without it a regression would
look exactly like the status quo, since the expected state for most methods is "gap".

The two exclusion buckets (`oracleNotClean`, `loweringBroken`) are recorded in the file
like any other outcome, but a method **moving into or out of one is ignored** by the
diff. Both depend on the machine rather than on Strata — which CPython tests skip or
assert on bytecode, and which generated programs need a C-API hook, a warnings filter or
a platform library.

Recording them and ignoring the transition is the symmetric choice: leaving them out
instead makes a method excluded *here* look like a brand-new method on a machine where it
runs, which fails just as loudly as the churn being avoided. A genuine appearance or
disappearance — a change in what the selector picks — still fails. `oracleMissing` is not
an exclusion: it means the oracle produced no outcome at all, which is a harness
malfunction and must be able to fail the run.

## Why only the interpreter

The verifier is deliberately not used. Its verdicts are conditional — every SARIF
result reads *"always true/false if reached, **reachability unknown**"* — so pairing
them with an oracle needs a reachability fact plus a per-obligation location join. The
interpreter answers the question directly: run the same program CPython ran, and see
whether Strata agrees. Everything that made the earlier verifier-based version
awkward (SARIF, location alignment, `relatedLocations`, per-obligation verdicts) went
away with it.

## Where the corpus comes from

`CPython312Runtime` is already a build-tool dependency. It is a thin from-source
wrapper: its `pkg.src` holds the upstream release tarball, and the *built* runtime
strips the `test` package entirely, so there is no `Lib/test` on disk anywhere.
`corpus.py` reads test sources straight out of the tarball, and `plan.py` extracts the
`test` package once so `test.support` is importable. Nothing is downloaded, and the
corpus is pinned by the version set. The patch version is globbed rather than
hardcoded, because the package revision moves when the version set advances.

The suite refuses to run under an interpreter that cannot support it. `plan.py` uses
`ast` on the CPython sources, so an older Python silently drops every file using syntax
it does not know — python3.9 selected 270 methods where 3.12 selected 790 on the same
manifest, with no error at all. The driver checks the version and that `strata_python.gen` imports, and exits 3
(a skip) if either fails.

## What gets generated

    <prelude>                     module-level definitions the method needs
    class Base: ...               base classes defined in the same file
    class DictTests(Base):
        thetype = frozenset       class-body attributes, unchanged
        def setUp(self): ...      the fixture, unchanged
        def helper(self): ...     only the helpers this test calls
        def test_foo(self):
            pass                  see below
            assert self.d['a'] == 1    assertions lowered, `self` untouched
    _cpython_oracle_case = DictTests()
    _cpython_oracle_case.setUp()
    _cpython_oracle_case.test_foo()

**The method stays in its class.** That is the whole design, and it is worth saying why,
because the obvious alternative was tried first and is much worse. Hoisting the body into
a module-level function means rewriting `self.x` to a local `self_x`, and that rewrite is
only sound when the `self` in question is the fixture's — which takes four separate
scope rules to decide (a nested function shadows only the parameter it declares; `self`
can be bound by assignment; a default argument evaluates in the enclosing scope; a
nested function writing fixture state needs a `nonlocal`). Every one of those rules was
found by a generated program misbehaving, not by reading code. Keeping the class makes
all four moot, and measured **410 agreeing methods against 88** for the hoisting
version, with `needsTriage` falling from 351 to 7.

Keeping the class is only possible because `pyInterpret` can now execute a program that
instantiates one. It could not before: V2 left the synthetic `__main__` unmarked as an
interpret entry, so `GlobalParameterization` gave it an `inout $heap` parameter that
nothing supplied, and every allocating program died with `expected 1 arguments, got 0`.

Each piece of the shape earns its place:

* **The class, pruned to the methods the test needs** — the test method, the fixtures,
  and the transitive closure of helpers it calls. Emitting the class whole would let one
  untranslatable sibling poison every other method in it, since the front end translates
  the whole class: `test_a` would fail because `test_z` uses `exec`.
* **Base classes defined in the same file**, so an inherited helper resolves by ordinary
  attribute lookup. A base from anywhere else is dropped — emitting it would mean
  translating `test.support` — and the method is rejected only if it actually reaches
  something that base supplied.
* **`unittest.TestCase` is dropped**, because every assertion is lowered and so nothing
  inherited from it is needed. The alternative, a stub base reimplementing `assertEqual`
  and friends, is modelling the very thing lowering exists to avoid.
* **A leading `pass`** in each emitted method, because V2 promotes a leading run of
  asserts into that method's `requires` (`splitPreconditions`). A generated body is often
  *entirely* asserts, so without it they stop being statements to execute.
* **The prelude**, carrying the transitive closure of module-level names the class
  touches. An import Strata cannot model is fine — attempting it is the point.
* **Class-body attributes stay class attributes**, which is what they were.

`self.fail(...)` lowers to `assert False`, and `with self.subTest(...)` inlines its
body — subTest only groups, and the body runs either way. Skip-only decorators
(`@skipIf`, `@support.cpython_only`, …) are dropped and the method attempted; if CPython
skips it there is no expectation. `@expectedFailure` is *not* in that set, because it
inverts the result rather than gating it.

Assertions are **lowered, not modelled**: `self.assertEqual(a, b)` becomes
`assert a == b`, and `with self.assertRaises(E): body` becomes a `try`/`except` with a
flag. The lowered form *is* the assertion's meaning, so there is no model to get
subtly wrong. Only assertions whose meaning is exactly expressible are lowered,
because a weaker obligation could pass where CPython fails. Widening coverage means
adding a case to `lower.py`; `selector.py` refuses any method whose assertions it
cannot lower, and the two must agree exactly or generation fails after selection has
already accepted the method.

"Exactly expressible" is a higher bar than it first looks, and two of the three most
common assertions in the corpus turned out to clear it after all:

* `assertRaisesRegex` (233 occurrences) keeps its pattern rather than dropping it:
  unittest checks `expected_regex.search(str(exc))`, so the generated handler asserts
  exactly that. `import re` is added to the prelude **only** when a lowering used it —
  an unconditional import would change what the front end is asked to translate in the
  other 1,300 programs.
* `assertAlmostEqual` is `a == b or round(abs(b - a), places) == 0`, or
  `abs(a - b) <= delta` when `delta` is given; supplying both is a `TypeError` in
  unittest and is refused here too.

What stays out: the `assertXEqual` family also checks operand types, and `assertWarns`
needs the warnings machinery. The cautionary case is `assertTrue`, which an earlier
version *modelled* as `expr != 0`: `assertTrue([])` fails in unittest while `[] != 0`
holds, so that was unsound in the direction that matters. Lowered to a plain
`assert expr` it is exact, which is the whole argument for lowering over modelling.

Ordering matters inside `prepare.py`: assertions are lowered **before** `self` is
rewritten. The other way round, `self.assertEqual(...)` becomes
`self_assertEqual(...)` before the lowering can see it, and every method loses every
assertion.

## The invariant that holds this together

Predicting statically which rewrites preserve meaning proved to be a losing game:
`__qualname__` encodes its enclosing scope, a zero-argument `super()` needs a class
cell, a helper assigning to `self.X` becomes a local write. So it is not predicted.
**`runner.py` runs every generated program under CPython and compares it to the
original**; a program that behaves differently is excluded as `loweringBroken` and
counted in the report.

That check is what found `__qualname__`, bare `super()`, a fixture-field scan that was
treating `self.addCleanup` as fixture state, and every scoping bug listed under
Coverage below. It took `loweringBroken` from 59 down to 5, and those 5 are all
environment-dependent rather than mistranslations: a `BytesWarning` filter, a C-API
hook on `set`, coroutine origin tracking, `sys.excepthook`, and a missing `libffi`.

## Runtime

About **130 seconds** for the whole language-level corpus (66 files, ~1,340 methods) at
4 workers; `runner.py` parallelises per method.

`pyInterpret` is listed in the package's `defaultTargets`, which matters for more than
convenience. Without it, this script and `run_py_interpret.sh` each compiled the binary
from scratch *at the same time* — testMain launches the test files concurrently — and
the two `lake` invocations clobbered each other's intermediate objects. The visible
failure landed in a **third** suite: `AnalyzeGoldenTest` died compiling
`EliminateDeterministicHoles` with "no such file or directory". Being a race, it passed
three builds before it bit.

Each generated program runs in its **own temporary working directory**. Some CPython
tests create files relative to the cwd (`test_fstring` makes a `tempcwd`), so a shared
cwd let two of them race under the worker pool and swap buckets between runs — which a
baseline turns from an invisible quirk into a visible, and useless, flake.

The worker count is small and fixed on purpose. This suite is one of ~21 test files
that testMain launches concurrently, and a development build was killed for low memory
at that concurrency before this suite did any work. CPython's own regrtest makes the
same call with `-j`.

## What this design gives up

Three things are rejected rather than answered wrongly, each found by the
generated-program check rather than by inspection:

* **a base class from outside the file** (`ExtraAssertions`,
  `FloatsAreIdenticalMixin` from `test.support`) is dropped, so a method reaching one of
  its helpers is rejected. Rejecting the whole class instead cost 283 methods, since most
  mixins are never touched by the method under test.
* **`self` passed to an external callable** — `check_syntax_error(self, 'x + 1 = 1')`
  hands the TestCase to a `test.support` helper that calls `self.assertRaisesRegex` on
  it. The unittest base is gone, so that API is not there.
* **an assertion that survives lowering** — the lowering rewrites assertion
  *statements*, so one used as a value has no method to dispatch to.

Each was first observed as a `loweringBroken` program; converting them into rejections
took that bucket from 242 to 6. A `super()` call is rejected the same way when it would
reach past every emitted base — `super().setUp()` has nothing to resolve to once
`unittest.TestCase` is dropped.

## Coverage

The manifest's 66 files hold **2,260 test methods** in TestCase classes. The selector
takes **1,443**; generation skips 45 more, so **1,398 methods and 5,525 assertions** are
attempted, of which **410 agree** with CPython. The 817 it declines break down as:

| count | reason | tractable? |
|---|---|---|
| 168 | the method uses `exec`/`eval`/`compile`/`globals`/`locals`/`vars` | no — out of scope: the assertion lives in a string the interpreter never evaluates, so a pass is vacuous |
| 143 | a helper the method calls is itself rejected | no — 99 use `compile`, 31 `eval`, 13 assert on source positions |
| 130 | a free name with no module-level definition to emit | **a gap, not scope**. Measured: removing this rule gains 23 agreements and 40 invalid comparisons |
| 128 | reaches something through `self` that is not on the emitted class | no — a `test.support` mixin helper; the suite deliberately does not emit the unittest framework |
| 98 | an assertion that does not lower exactly | **a gap, not scope** — `assertFloatsAreIdentical` and `assertExceptionIsLike` are `test.support` helpers (so out of scope), but the `assertXEqual` family is not: it also checks operand *types*, so `a == b` would be strictly weaker |
| 81 | `self` passed to an external callable that uses the unittest API | no — same framework dependency |
| 29 | `super()` reaches past every emitted base | no — `super().setUp()` resolves into `unittest.TestCase`, which is not emitted |
| 26 | asserts on line numbers or code positions | no — the generated file has its own line numbers |
| 14 | a decorator that changes what the test means, not whether it runs | no |

`with self.assertRaises(E) as cm` IS lowered: the exception is copied into a local that
outlives the handler, and `cm.exception` is rewritten in the statements that follow the
block. Any other attribute of `cm` is refused rather than approximated. `assertWarns` and
`assertWarnsRegex` lower to `warnings.catch_warnings(record=True)` plus an
`any(issubclass(w.category, W))` assert. Keywords beyond `msg` are forwarded to the
callable, since that is what unittest does with them. Zero-argument `super()` and
`__qualname__` are not rejected at all — keeping the class made both work.

45 methods are still refused at generation: 35 use an assertion as a *value* rather than
as a statement, so the lowering has no statement to rewrite, and 9 carry an assertion form
that does not lower.

**Dynamic code is out of scope, and the measurement says why it has to be stated that
way.** Such a method does run — the body is copied verbatim — and 92 of them are recorded
as **agreeing**. That is the argument for excluding them, not against: `agree` means the
interpreter ran to completion as CPython did, so when the assertion under test lives
inside the `exec`'d string the interpreter never evaluated it, and the pass is vacuous. A
vacuous pass is worse than a gap, because it reads as coverage.

Two neighbouring rules were checked the same way, by removing them and measuring, and
both are kept: without the source-position rule the suite gains 3 agreements and 4
invalid comparisons, without the free-name rule 23 and 40.

## Reading the report

`build/report.json`, summarised on stdout. Buckets are classified **by exit code**,
because AGENTS.md's review policy is that translator diagnostics on stderr are not a
stable interface — consumers use the exit code and the `RESULT:`/`DETAIL:` lines only.

| bucket | exit | meaning |
|---|---|---|
| `agree` | 0 | ran to completion, as CPython did |
| `untranslatable` | 1 | Strata could not translate the program |
| `needsTriage` | 2 | a runtime problem, where CPython ran clean |
| `error` | other | including timeouts |

**`pyInterpret` emits no `RESULT:` line**, so the exit code is all there is — and exit 2
conflates the two cases this suite most wants to separate: an assertion the interpreter
evaluated to **false** (a possible semantic bug) and an expression it **could not
reduce** (a coverage gap). The raw message is carried in `detail` so a human can tell
them apart. Making the split reliable needs `pyInterpret` to emit a `RESULT:` line the
way `pyAnalyze*` does.

**`needsTriage` is not a bug report.** An assertion coming back false is often the
interpreter silently treating an unmodelled operation as a no-op or as identity rather
than getting Python wrong: `b is not b.replace(b'', b'')` is false because
`bytearray.replace` is unmodelled and hands back the same object — a defect, but a
different one from getting `is` wrong. Of the first nine such cases examined, exactly
one, `'%d' % False == '0'`, was a genuine semantic bug.

Two buckets are **exclusions**, where no conclusion about Strata is drawn:

| bucket | meaning |
|---|---|
| `loweringBroken` | the generated program does not behave as the original under CPython |
| `oracleNotClean` | CPython itself does not run the method cleanly: it fails, errors, or is **skipped**. Some tests assert on bytecode, which varies by build; and a skip-only decorator, though dropped from the generated program, is still live when the oracle runs the pristine source — a method CPython never ran states no expectation to compare against |
