# Python Verification via Laurel

This document covers the Strata Python verification pipeline, which translates
Python programs through Laurel to Core for SMT verification.

## Prerequisites

1. **Build Strata**:
   ```
   lake build strata
   ```

2. **Install the Python bindings** (requires CPython 3.14):
   ```
   cd Python/strata-python
   pip install .
   ```

3. **Generate the Python dialect file** (one-time setup):
   ```
   cd Python/strata-python
   python -m strata_python.gen dialect dialects
   ```

## Pipeline Overview

There are two kinds of Python input files that flow through the pipeline:

- **Source programs** (`.py`) — the code you want to verify. These are
  translated to Ion format and then verified.
- **PySpec files** (`.py`) — type-stub-like specifications for external
  libraries. These provide type signatures and overload dispatch information
  to the verifier.

```
Source program (.py)                  PySpec library stubs (.py)
        |                                       |
        v                                       v
  [py_to_strata]                           [pySpecs]
        |                                       |
        v                                       v
  .python.st.ion                         .pyspec.st.ion
        |                                       |
        |                              [pySpecToLaurel]
        |                                       |
        |                                Laurel decls
        |                              + dispatch table
        |                               + methods
        v                                       v
                    [pyAnalyzeLaurel --pyspec ... --dispatch ...]
                                    |
                                    v
                          Verification results
```

## Step 1: Convert Source Programs to Ion

Translate a Python source file to a Strata Ion program file:

```
cd Python/strata-python
python -m strata_python.gen py_to_strata \
   --dialect dialects/Python.dialect.st.ion \
   ../../StrataPythonTest/test.py \
   ../../StrataPythonTest/test.python.st.ion
```

The output `.python.st.ion` file contains the Python AST in Strata's Ion
binary format, ready for analysis.

## Step 2: Generate PySpec Ion Files from Library Stubs

If your program calls external libraries, you need PySpec files that describe
their type signatures. Convert a Python spec file to PySpec Ion:

```
lake exe strata pySpecs path/to/service_client.py output_dir/
```

- `python_path` — the `.py` stub file containing type annotations
- `strata_path` — output directory (created if it does not exist)
- Produces `output_dir/<module>.pyspec.st.ion`

**Example** (batch-converting all service stubs in a directory):
```
for pyfile in specs/inputs/*.py; do
    lake exe strata pySpecs "$pyfile" specs/pyspec/
done
```

## Step 3: Verify via the Laurel Pipeline

The primary verification command is `pyAnalyzeLaurel`. It:

1. Reads the Python Ion program
2. Builds a prelude augmented with PySpec-derived declarations
3. Translates Python to Laurel, then Laurel to Core
4. Runs SMT verification and reports results with source locations

```
lake exe strata pyAnalyzeLaurel [flags] <program.python.st.ion>
```

### Flags

`--verbose`
: Print the Python AST, Laurel program, and Core program at each
  stage.

`--pyspec <ion_file>`
: Add PySpec-derived Laurel declarations from an Ion file. Repeatable
  — use once per service. Translates PySpec signatures to Laurel types
  and procedures, and collects the overload dispatch table and method
  registry.

`--v2`
: Use the V2 front-end (Resolution → Translation → Elaboration → Core)
  instead of the default V1 front-end. `pyAnalyzeV2` is an alias for
  `pyAnalyzeLaurel --v2`. V2 is under construction: it honors
  `--spec-dir`, `--pyspec` and `--dispatch` (existing PySpec models bind
  through name Resolution), and still differs from V1
  on most of the golden corpus — see
  [`expected_laurel/README.md`](./expected_laurel/README.md).

`--dispatch <ion_file>`
: Extract only the overload dispatch table from a PySpec Ion file (no
  Laurel translation). Repeatable. Use for files that define overloaded
  factory functions but no service classes.

### Examples

Verify a simple program (no external dependencies):
```
lake exe strata pyAnalyzeLaurel test.python.st.ion
```

Verify a program that uses multiple services:
```
lake exe strata pyAnalyzeLaurel \
    --pyspec specs/pyspec/ServiceA.pyspec.st.ion \
    --pyspec specs/pyspec/ServiceB.pyspec.st.ion \
    my_program.python.st.ion
```

Verify with a dispatch file (for overloaded factory function resolution):
```
lake exe strata pyAnalyzeLaurel \
    --pyspec specs/pyspec/ServiceA.pyspec.st.ion \
    --dispatch specs/pyspec/factory.pyspec.st.ion \
    my_program.python.st.ion
```

Use `--verbose` to see all intermediate representations:
```
lake exe strata pyAnalyzeLaurel --verbose \
    --pyspec specs/pyspec/ServiceA.pyspec.st.ion \
    my_program.python.st.ion
```

### Output

Verification results are printed by default (suppressed in SARIF mode).
Each line shows the source location, outcome, and assertion name:

```
test_arithmetic.py(7, 4): ✅ pass - assert(102)
test_arithmetic.py(14, 4): ❌ fail - assert(200)
```

## Golden Test Suite

`run_py_analyze.sh` is the golden runner for `tests/test_*.py`. It compiles each
test to Ion, runs the analyzer, normalizes unstable assertion-label IDs
(`normalize_labels.py`), and diffs against the golden files.

CI runs it for **both** front-ends, back to back, from
`../StrataPythonTestExtra/AnalyzeGoldenTest.lean`:

```
./run_py_analyze.sh              # V1, goldens in expected_laurel_v1/
./run_py_analyze.sh --v2         # V2, goldens in expected_laurel/
```

Note the paths: `expected_laurel/` is the **V2** set, because V2 was introduced
by rewriting those files in place so the change would be reviewable as a diff
per test. [`expected_laurel/README.md`](./expected_laurel/README.md) explains
that and inventories what currently differs between the two front-ends.

A test is part of a front-end's suite iff that front-end's directory has a
`<name>.expected` for it. Regenerate goldens with `--update` (add `--v2` for the
V2 set), and narrow a run with `--filter <substring>`. Each `--v2` run ends with
a `V1/V2 divergence: N of M golden(s) differ` line.

The two runs share scratch files (`tests/*.python.st.ion`, and `user_errors.txt`
in the working directory), so they must not be run concurrently.

## Interpret Test Suite

`run_py_interpret.sh` runs the same `tests/test_*.py` corpus through `pyInterpret`
— Python → Core → concrete execution, with **no verification**. It answers a
different question from the analyze suite: not "what does the verifier prove" but
"does the model run this program at all, and does it get the right answer".

CI runs it for **both** front ends, back to back, from
`../StrataPythonTestExtra/InterpretGoldenTest.lean`:

```
./run_py_interpret.sh            # V1, expectations in expected_interpret_v1/
./run_py_interpret.sh --v2       # V2, expectations in expected_interpret/
```

The paths mirror the analyze sets: `expected_interpret/` is the **V2** set. See
[`expected_interpret/README.md`](./expected_interpret/README.md).

The two runs do not cover the same cases. V2 runs all 1,478; V1 runs only the 310
hand-written ones, because the 1,168 imported regression cases are V2-only — V1 is
slated for deletion, so a second baseline for them has no consumer. The runner tells
them apart by `expected_interpret/<case>.desired`, which every imported case has and
no hand-written case does, so an import is V2-only without a list to maintain.

Expectations work by absence as much as by presence, which is the main difference
from the analyze goldens:

| Sidecar | Meaning |
|---|---|
| *(none)* | the case must run to completion, exit 0 |
| `<case>.expected` | the case must fail, and its output must match this regex |
| `<case>.skip` | do not run the case; the file holds the reason |

So a case that fails under one front end and passes under the other has a file in
only one of the two sets — the `V1/V2 divergence: N of M case(s) differ` line at
the end of the `--v2` run compares whole cases, not just the files present, over the
310 cases both front ends run.

Regenerate with `--update` (add `--v2` for the V2 set). A stored pattern that still
matches is kept byte for byte, so deliberate relaxations survive; one that no longer
matches is rewritten from the actual failure with assertion identifiers and Ion byte
offsets relaxed. Narrow a run with `--filter <substring>`.

`<case>.desired` sidecars record what a case ought to conclude, rather than what it
does, and `completeness_report.py` is what reads them as expectations. The runner
reads one only to decide whether the V1 run skips the case.

The two runs share `tests/*.python.st.ion`, so they must not be run concurrently.

## Diagnostic Commands

These commands are useful for inspecting intermediate artifacts.

### pySpecToLaurel

Translate a PySpec Ion file to Laurel and print a summary of the resulting
types, procedures, and overload dispatch table:

```
lake exe strata pySpecToLaurel path/to/service.py output_dir/
```

Both arguments are used to locate the Ion file: the module name is derived
from `python_path`'s filename stem, and the Ion file is read from
`strata_path/<module>.pyspec.st.ion`.

**Example output:**
```
Laurel: 42 procedure(s), 3 type(s)
Overloads: 0 function(s)
  type MyClient
  procedure MyClient_put_object(Key:TString, ...) returns(result:TString)
```
