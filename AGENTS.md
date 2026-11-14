# AGENTS.md - StrataPython

Guide for AI agents working with the StrataPython package.

For purpose, file structure, namespace table, and dependencies, see
[`README.md`](./README.md). The notes below cover only the conventions and
workflows that aren't obvious from reading the code.

## Architecture: which translation path?

There are two Python-to-IR pipelines:

1. **Through Laurel** (`PythonToLaurel.lean` + `PySpecPipeline.lean`) — main
   pipeline. Combines Python source with PySpec type specifications, resolves
   overloads, and produces typed Laurel that compiles to Core. Used by
   `pyAnalyzeLaurel`. **All new work should target this path.**
2. **Direct to Core** (`PythonToCore.lean`) — **deprecated.** Bypasses Laurel.
   Still used by `pyInterpret` and `pyAnalyzeToGoto`, but lacks PySpec /
   overload support. Do not extend this path; if you need new behavior here,
   consider porting the consumer to the Laurel path instead.

Within the Laurel path there are two **front-ends**, selected by the `--v2`
flag on `pyAnalyzeLaurel` (`pyAnalyzeV2` is an alias for `pyAnalyzeLaurel
--v2`):

- **V1** (default) — `pythonAndSpecToLaurel`, then `laurelToCore`. The shipping
  front-end; it is what supports `--spec-dir` / `--dispatch` / `--pyspec`.
- **V2** — `pyAnalyzeV2ToCore` (`FineGrainLaurel/Elaborate.lean`): Resolution →
  Translation → Elaboration → Core. Under construction. It honors `--spec-dir`
  / `--dispatch` / `--pyspec` (existing PySpec models bind through name
  Resolution), and still differs from V1 on most of the golden corpus.

Both front-ends run the `StrataPythonTest/tests/` corpus in CI, twice over — once
verified and once executed — each run against its own per-front-end set:

| Suite | Driver | V1 set | V2 set |
|---|---|---|---|
| analyze (SMT verification) | generated children from `StrataPythonTest/AnalyzeGolden/Generate.lean` | `expected_laurel_v1/` | `expected_laurel/` |
| interpret (concrete execution) | generated children from `StrataPythonTest/InterpretGolden/Generate.lean` | `expected_interpret_v1/` | `expected_interpret/` |

The interpret suite is the exception to "the whole corpus": V2 runs all 1,478 cases,
V1 only the 310 hand-written ones. The 1,168 imported regression cases are V2-only
since V1 is slated for deletion. The discriminator is an
`expected_interpret/<case>.desired` sidecar — every imported case has one and no
hand-written case does — so a new import is V2-only with no list to maintain.

Watch the directory names — they are not what you would guess: the **unqualified**
path is the **V2** set in both suites. Regenerate with
`lake exe pyAnalyzeUpdate [--v2] --update` (analyze) and
`lake exe pyInterpretUpdate [--v2]` (interpret), both from the package root, and read
[`StrataPythonTest/expected_laurel/README.md`](./StrataPythonTest/expected_laurel/README.md)
and
[`StrataPythonTest/expected_interpret/README.md`](./StrataPythonTest/expected_interpret/README.md)
for why the paths are that way round and what currently differs between them.

Neither suite runs at Lean elaboration time: both shell out to the compiled binary,
so a mismatch is a test failure, not a build error.

## Dyn layout

[`README.md`](./README.md#dyn) lists the directories. The rules:

- New Dyn core work goes in `StrataDyn/`, which must not import `StrataPython*`.
- Python on Dyn goes in `StrataPython/Dyn/`.
- Tests (`StrataDynTest/`, `StrataPythonTest/Dyn/`) are `module` files; `import all` is
  allowed. Check behaviour, well-formedness included, with `#guard` and `#guard_msgs`. Use
  `decide +kernel` only where a later proof uses the result, and never `native_decide`. The one
  exception is a rule or helper in `StrataDynTest/Exec/RuleErrorTest.lean`,
  `TableCheckTest.lean` or `RuleHelpers.lean` that a test expects the "runs as proved" check to
  reject: there `native_decide` (like `sorry` and false axioms) is the test's input.

The scope pass and the translator share their tests. To add one, put `NAME.py` in
`StrataPythonTest/Dyn/dyn_tests/` and:

- add the line `NAME | yes | REJECTS` to `StrataPythonTest/Dyn/dyn_tests.txt` (`no` if
  the translator should not handle it yet; `REJECTS` lists the constructs it must reject and
  the messages of its scope errors, often empty), and write its translator golden
  `NAME.expected.dyn` by running `StrataPythonTestExtra/DynTranslateTest.lean` with
  `DYN_UPDATE=1`;
- write `NAME.symtable` by running `StrataPythonTest/Dyn/scope_symtable.py` with CPython
  3.12, and its scope golden `NAME.expected.scope` by running
  `StrataPythonTestExtra/PyScopeTest.lean` with `PYSCOPE_UPDATE=1`;
- write its ref-to-reg golden `NAME.expected.ssa.dyn` by running
  `StrataPythonTestExtra/DynRefToRegTest.lean` with `DYN_UPDATE=1`, as its own command
  after the translator goldens are written; it also rewrites the summary
  `ref_to_reg.summary`. Do the same whenever a change to the translator changes an existing
  golden.

The translator test fails on any `.py` that is not listed, the scope test on any `.py`
without both scope files, and the ref-to-reg test on any translator golden without its
`.expected.ssa.dyn` golden.
`lake exe pydyn dyn FILE.py` prints the diagnostics and the module for one file.

A PySpec model translates to IR modules (`docs/PythonToDyn.md` §12.13). To add a test, put the
model under a search path such as `StrataPythonTestExtra/Specs/`, add the line `SEARCH_PATH |
MODULE | ok` (or the rule IDs of its rejections) to `StrataPythonTest/Dyn/pyspec_models.txt`,
and write its goldens by running `StrataPythonTestExtra/PySpecDynTest.lean` with
`PYSPEC_DYN_UPDATE=1`. `lake exe pydyn pyspec SEARCH_PATH MODULE` prints one set.

`StrataPythonTestExtra/DynReadTest.lean` reads every golden back with `Module.read`, so a
printer change that breaks reading fails there; `lake exe pydyn read FILE` reads one.
A new program in `StrataPythonTest/Dyn/dyn_tests/` or in `StrataPythonTest/tests/` also needs
its CPython trace and its verdict for the Python semantics' differential test: run
`StrataPythonTestExtra/SemDiffTest.lean` with `SEM_UPDATE=1`.

The axis grid (`StrataPythonTest/Dyn/axes/`) compares the Python semantics with CPython 3.12 on
one generated program per case: an operation with one kind of input, such as an instance of a
subclass of a built-in type, a user method that re-enters the built-in that called it, or a
special method that is a property. `catalog.py` holds the operations and the kinds, and what
CPython must do in each case; `grid.py` writes the programs. `StrataPythonTestExtra/AxisGridTest.lean`
runs them, and fails on a case that doesn't run its operation in CPython (a generator bug), on a
difference from CPython, and on a change of verdict (`grid_expected.txt`). It needs CPython 3.12.
After a change to the catalog, `grid.py` or `trace.py`, run it with `SEM_UPDATE=1`: that compares
CPython's traces under the hash seeds 0 to 7, checks that each case's trace changes without its
operation, and rewrites the verdicts, the known runs (`grid_known/`), the summary and the digest.
A difference that its owner doesn't fix yet is pinned as `<id> | known | <reason>` in
`grid_expected.txt` before the update.

The same test checks coverage: every instruction of `Py.env`, every built-in function and method
that the model implements, and every name and class native that it binds in `typing` and
`dataclasses` must be covered by a case that agrees with CPython and gives a result, or be listed
in `StrataPythonTest/Dyn/axes/not_covered.txt` with the reason. Two kinds of evidence cover a
name:

- observed: a call that CPython's run of the case shows (`cpython_calls.py`), or an instruction
  in the translation of the case's operation;
- declared: a special method that the catalog says the case's operation reaches without a call
  (`len` of a `list` reaches `list.__len__`), in the case's `entries`; and an attribute of
  `typing` or `dataclasses` that the case's code reads, taken from the code, not from a run.

No run checks a declared entry, so `grid_summary.txt` lists the names that only declared entries
cover, each with the first case that declares it, and how many more. A new rule or built-in needs a case in `catalog.py`,
or an entry in `not_covered.txt`; an entry for something that a case now covers fails too. A case
also names what it calls by name in `calls`, and CPython's run must show each of those calls. The
typing and dataclasses cases that are whole programs are files in
`StrataPythonTest/Dyn/axes/typing/`, named `<axis>_<name>.py`.

`StrataPythonTest/Dyn/axes/fuzz.py` writes random programs from the same kinds of input: classes
with special methods of each behaviour and descriptor kind, values and operations, each step in
its own `try`. `StrataPythonTestExtra/AxisFuzzTest.lean` runs the 200 programs of seed 1 against
`fuzz_expected.txt` (update with `SEM_UPDATE=1`, as the grid). A `known` pin holds for one
program: `fuzz_known/` keeps the program beside our run, and the test fails when the generator
gives that id another program. To fuzz further, run
`FUZZ_SEED=S FUZZ_COUNT=N lake env lean StrataPythonTestExtra/AxisFuzzTest.lean`: it runs CPython
under eight hash seeds, pins nothing, and fails on any difference.

## Convention: `open Strata` pattern

Since StrataPython was extracted from the `Strata` package, many files use
`open Strata` to access `Core.*`, `Laurel.*`, `Pipeline.*`, `DL.*`, and utility
types like `SourceRange`, `FileRange`, `DiagnosticModel`. When adding new
files, include `open Strata` (and possibly `open Strata.Pipeline`) if you
reference any of these.

The pipeline orchestration framework (`PipelineM`, `MessageKind`,
`PipelineContext`, `withPhase`, `emitMessageAndAbort`) lives in
`Strata.Pipeline`. The Python-specific pipeline entry points
(`runPyAnalyzePipeline`, `PyAnalyzeOutcome`, `PyAnalyzeConfig`) live in
`StrataPython.Pipeline`.

## How to add a Python translation feature

1. If it's a new expression/statement handler, modify `PythonToLaurel.lean`
   (the Laurel path is the only one taking new work — see Architecture above).
2. If it's a new PySpec feature (new type form, new declaration kind), modify
   `Specs/Decls.lean` for the data type and `Specs/ToLaurel.lean` for the
   translation.
3. Add compile-time tests in `StrataPythonTest/` (no Python dependency).
4. Add runtime integration tests in `StrataPythonTestExtra/` (requires Python +
   `strata.gen`).

## How to add a regex feature

1. Add parsing in `Regex/ReParser.lean` (extends `ReToken` / `ReAST`).
2. Add Core SMT translation in `Regex/ReToCore.lean`.
3. Add test cases to `StrataPythonTest/Regex/ReToCoreTests.lean` and corpus
   entries in `StrataPythonTest/Regex/corpus.tsv`.

## DDM-generated types

`PythonDialect.lean` uses `#load_dialect` and `#strata_gen Python` to generate
the Python AST types at compile time from
`Python/strata-python/dialects/Python.dialect.st.ion`. Key generated types:

- `StrataPython.expr` — Python expressions
- `StrataPython.stmt` — Python statements
- `StrataPython.keyword`, `StrataPython.alias`, `StrataPython.constant`, etc.
- `StrataPython.Python` — the dialect constant (for Ion serialization)
- `StrataPython.Python_map` — dialect map for program parsing

These live in the `StrataPython` namespace. The `#strata_gen Python` macro
also creates a `Python` sub-namespace for the dialect constant itself, so
`StrataPython.Python.toIon` and friends are valid.

## Common code patterns

### Reading a Python Ion file

```lean
let bytes ← StrataDDM.Util.readBinInputSource path
match StrataPython.readPythonStrataBytes path bytes with
| .ok stmts => ...
| .error msg => ...
```

### Running the full Laurel pipeline

```lean
let (outcome, stats, pctx) ← StrataPython.Pipeline.runPyAnalyzePipeline {
  filePath, specDir, dispatchModules, pyspecModules, verifyOptions, ...
}
```

### Translating PySpec to Laurel

```lean
let { program, errors, overloads, ... } :=
  StrataPython.Specs.ToLaurel.signaturesToLaurel filepath sigs moduleName
```

## Custom Instructions

### Review Policies

- Constructs the dictionary map model cannot express are rejected with fatal diagnostics by design (see "Rejection over silent mistranslation" in README.md). The hard errors on non-str-keyed dict quantifiers ("dict quantifier requires str keys") and on non-TypedDict `**kwargs` (`kwargsExpansionError`) are intentional, pinned by requires_int_dict_quant and requires_nontypeddict_kwargs in SpecsTest.lean; do not flag them as regressions.
- `preScanModule`/`translate` in `Specs.lean` always emit module `ghost(...)` signatures before all other signatures, regardless of source position (see "Signature order: module ghosts are emitted first" in README.md). This is intentional, not a bug.
- Translator diagnostic strings on stderr are not a stable interface. Consumers classify runs by exit code and the `RESULT:`/`DETAIL:` lines only, never by message wording.
- UNKNOWN verifier results on fully-havoced `Any` arguments hitting the caller-side map schema quantifier are a known completeness limitation, not a soundness risk; they should not block merges.
