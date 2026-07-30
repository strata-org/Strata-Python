# StrataPython

Python language support for Strata. This package translates Python programs into Strata's intermediate representations (Core, Laurel) for formal verification.

## Building

```bash
lake build
```

This builds the `StrataPython` library and the
`StrataPythonTest` compile-time tests.

## Package Purpose

StrataPython provides:

- **Python AST** - Types generated from the Python dialect DDM definition
- **Python-to-Laurel translation** - Translation through the Laurel IR (higher-level, supports dispatch and overloads).
- **Python-to-Core translation** - *Deprecated.* Direct translation from Python to Core IR, kept for `pyInterpret` and `pyAnalyzeToGoto`; new features should target the Laurel path
- **PySpec pipeline** - Reads Python type specifications (`.pyspec.st.ion`) and generates Laurel declarations for verification
- **Regex support** - Translates Python regular expressions to Core SMT assertions
- **Overload resolution** - Identifies and resolves dispatch-based service overloads

## Dependencies

- `Strata` (parent package) - Core IR, Laurel IR, verification infrastructure, SMT backend
- `StrataDDM` (transitive via Strata) - Dialect Definition Mechanism, Ion format

## File Structure

The package is the repository root:

```
.
├── StrataPython.lean              # Public API (readPythonIon, pySpecsDir, pyTranslateLaurel, etc.)
├── StrataPython/
│   ├── Cli.lean                   # Shared CLI helpers for the Scripts/ executables
│   ├── PythonDialect.lean         # DDM dialect definition + generated types (expr, stmt, etc.)
│   ├── PythonIdent.lean           # Module-qualified Python identifiers
│   ├── ReadPython.lean            # Read Python AST from Ion format
│   ├── PythonToCore.lean          # Direct Python → Core translation
│   ├── PythonToLaurel.lean        # Python → Laurel translation (main pipeline)
│   ├── PySpecPipeline.lean        # PySpec reading, overload resolution, Laurel construction
│   ├── PyFactory.lean             # Core expression factory with regex support
│   ├── CorePrelude.lean           # Python Core runtime prelude
│   ├── PythonLaurelCorePrelude.lean  # Laurel-translated runtime prelude
│   ├── PythonRuntimeLaurelPart.lean  # Runtime support as Laurel declarations
│   ├── PythonLaurelTypedExpr.lean    # Type-tagged Laurel expression builders
│   ├── FunctionSignatures.lean    # Function signature types for Core translation
│   ├── OverloadTable.lean         # Overload dispatch table
│   ├── Specs.lean                 # PySpec file reading, module discovery, translation
│   ├── Specs/
│   │   ├── DDM.lean               # PySpec DDM dialect and serialization
│   │   ├── Decls.lean             # PySpec type declarations (SpecType, FunctionDecl, etc.)
│   │   ├── IdentifyOverloads.lean # AST walker for overload resolution
│   │   ├── MessageKind.lean       # Pipeline message classification
│   │   └── ToLaurel.lean          # PySpec → Laurel translation
│   ├── Regex/
│   │   ├── ReParser.lean          # Python regex parser
│   │   └── ReToCore.lean          # Regex → Core SMT translation
│   └── Pipeline/
│       └── PyAnalyzeLaurel.lean   # Full analysis pipeline (Python → Laurel → Core → SMT)
├── Scripts/                       # Executable entry points (pyInterpret, pyAnalyzeLaurel, etc.)
├── Python/
│   └── strata-python/             # Python tooling package (Ion reader, dialect generator)
├── StrataPythonTest/              # Compile-time tests (built with lake build)
├── StrataPythonTestExtra/         # Runtime tests (run with lake test, require Python)
├── StrataTestMain.lean            # Test driver for StrataPythonTestExtra
├── AGENTS.md                      # Guide for AI agents working in this package
├── lakefile.toml
├── lean-toolchain
└── lake-manifest.json
```

## Spec quantifiers

Within a PySpec function body, each supported `assert P` contributes the formula
`P` to the function's generated preconditions; the imperative `assert` itself is
not part of the logical expression. PySpec expressions may quantify over lists
and dictionaries using `all()` and `any()`:

- **Universal** — `all(P(x) for x in xs)` lowers to `∀`.
- **Existential** — `any(P(x) for x in xs)` lowers to `∃`.

Supported collection forms (the iterable's static type determines the domain):

| Syntax | Domain |
|--------|--------|
| `for x in xs` | List elements |
| `for k in d` or `for k in d.keys()` | Dict string keys |
| `for v in d.values()` | Dict values (via `d[k]` lookup) |
| `for k, v in d.items()` | Dict key-value pairs |

Statement-form universal quantifiers (`for ...: assert ...`) remain supported
for compatibility with generated PySpecs; `assert all(...)` is preferred for
new specifications. List domains currently bind only the element, not its index,
so a quantified assertion message cannot identify the failing index.

An optional `if` guard filters the quantification:
`assert all(len(k) >= 1 for k in Keys if k != sentinel)` lowers to
`∀ k. membership(k) ⟹ (k ≠ sentinel ⟹ len(k) ≥ 1)`.

**Caveat: an `any(...)` (∃) precondition can be refuted but never proven.**
The encoding uses collection membership as the SMT trigger. In goal position
triggers do not synthesize a witness, so a *genuinely satisfied* existential
verifies as `unknown` — not `✔️` — while a *false* one is refuted. An `any(...)`
precondition therefore only flags the case where no element can satisfy it; it
is a bug-finding signal, not a guarantee the verifier can discharge. Do not
write an `any(...)` precondition expecting callers that satisfy it to verify
green.

If you need a guarantee callers can discharge, state it universally or
structurally instead. For non-emptiness, require `len(xs) >= 1`. Where the
witness matters, take it as a parameter and assert a property of it directly —
`assert Needle in Keys` is a membership check the solver can prove, unlike
`assert any(k == Needle for k in Keys)`, which expresses the same requirement
existentially and therefore cannot be.

## Testing

### Compile-time tests (no Python required)

```bash
lake build StrataPythonTest
```

### Runtime tests (require the `strata` Python packages installed)

```bash
PYTHON=python lake test
```

The runtime tests require both the `strata-base` package (from the parent
Strata repository) and the in-repo `strata-python` package:

```bash
pip install <StrataDDM-repo>/Python/strata
pip install ./Python/strata-python
```

### Regex differential tests

```bash
cd StrataPythonTest/Regex
python diff_test.py
```

## Key Namespaces

| Namespace | Contents |
|-----------|----------|
| `StrataPython` | Public API, generated AST types (expr, stmt, etc.), Core translation |
| `StrataPython.ToLaurel` | Python-to-Laurel translation internals |
| `StrataPython.Specs` | PySpec reading, translation, module discovery |
| `StrataPython.Specs.ToLaurel` | PySpec-to-Laurel declaration generation |
| `StrataPython.Specs.IdentifyOverloads` | Overload resolution AST walker |
| `StrataPython.Laurel` | Type-tagged Laurel expression builders |
| `StrataPython.Pipeline` | Full pyAnalyzeLaurel pipeline |
