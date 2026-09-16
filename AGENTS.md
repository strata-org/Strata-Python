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
| analyze (SMT verification) | `StrataPythonTestExtra/AnalyzeGoldenTest.lean` → `run_py_analyze.sh` | `expected_laurel_v1/` | `expected_laurel/` |
| interpret (concrete execution) | `StrataPythonTestExtra/InterpretGoldenTest.lean` → `run_py_interpret.sh` | `expected_interpret_v1/` | `expected_interpret/` |

The interpret suite is the exception to "the whole corpus": V2 runs all 1,478 cases,
V1 only the 310 hand-written ones. The 1,168 imported regression cases are V2-only
since V1 is slated for deletion. The discriminator is an
`expected_interpret/<case>.desired` sidecar — every imported case has one and no
hand-written case does — so a new import is V2-only with no list to maintain.

Watch the directory names — they are not what you would guess: the **unqualified**
path is the **V2** set in both suites. Regenerate with
`./run_py_analyze.sh [--v2] --update` / `./run_py_interpret.sh [--v2] --update` from
`StrataPythonTest/`, and read
[`StrataPythonTest/expected_laurel/README.md`](./StrataPythonTest/expected_laurel/README.md)
and
[`StrataPythonTest/expected_interpret/README.md`](./StrataPythonTest/expected_interpret/README.md)
for why the paths are that way round and what currently differs between them.

Neither suite runs at Lean elaboration time: both shell out to the compiled binary,
so a mismatch is a test failure, not a build error.

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
   entries in `StrataPythonTest/Regex/diff_test.py`.

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

- The hard error on non-str-keyed dict quantifiers ("dict quantifier requires str keys") is intentional per the rejection-over-silent-mistranslation policy in README.md. Out-of-repo consumers were enumerated on 2026-09-16: the Strata Benchmarks corpus (StrataInternal/benchmarks, 403 Python files across kiro/bash/aws_samples/ecc) contains no dict quantifier over non-string keys, the Smithy-generated PySpec stubs in ErgoSmithyPythonSDK/generated-strata contain no .values()/.items()/.keys() iteration, and code search finds no other PySpec module using the pattern. Nothing relies on the old warn-and-proceed behavior, so this finding is resolved and should not be re-raised.
- Translator diagnostic strings on stderr are not a stable interface. Out-of-repo consumers were enumerated on 2026-09-16: the production consumer AWSMoogStrataService classifies pyAnalyzeLaurel output by exit code and the RESULT:/DETAIL: lines only (classify_exit_code in src/handlers/analyze.rs), never by the removed "called with unknown/missing keyword arguments" wording; the only other matches are recorded benchmark snapshots (StrataInternal, StrataInternalBenchmarks, IcontractToStrata logs) and Strata source forks, none of which gate CI on the string. The wording still exists on the explicit-positional path, covered by test_positional_missing.py. This finding is resolved and should not be re-raised.
- Non-TypedDict `**kwargs` (for example `**kw: int`) are deliberately dropped from the model with a fail-loud lowering error; only `Unpack[TypedDict]` kwargs are modeled. Pinned by requires_nontypeddict_kwargs in SpecsTest.lean.
- UNKNOWN verifier results on fully-havoced `Any` arguments hitting the caller-side map schema quantifier are a known completeness limitation tracked separately; they are not a soundness risk and should not block merges.
