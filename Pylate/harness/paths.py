"""Every path the harness needs, resolved once.

Each gate used to compute its own relative paths -- `rule_validity.py` alone had
five, one of them reaching into the Lean sources -- so moving a file meant
finding and fixing all of them, and a wrong one failed *quietly*: a gate that
cannot find the `CLAIM:` markers reports `transfer 0/0` rather than an error.

`guard()` is the answer to that: it checks the things whose absence would
otherwise look like a clean run.

Layout this assumes:

    pylate-lean/
      Pylate/ Main.lean Tests/     the Lean package
      corpus/                     the programs under analysis, and their goldens
      harness/                    this directory
        gates/ probes/ generators/ data/
"""

from __future__ import annotations

import os
import sys

HARNESS = os.path.dirname(os.path.abspath(__file__))
#: The Lean library directory. The harness, the corpus and the Lean suites all
#: nest under it, so that everything belonging to Pylate is in one subtree of the
#: host package rather than four sibling directories at its root.
LIB = os.path.dirname(HARNESS)


def _package_root(start: str) -> str:
    """The Lake package root: the nearest ancestor holding a `lakefile.toml`.

    Found by walking up rather than by counting directories, because this harness
    is nested one level deeper inside `StrataPythonFrontEnd` than it is in the
    standalone package, and a hard-coded `dirname` chain silently resolves to the
    wrong directory instead of failing.
    """
    current = start
    while True:
        if os.path.exists(os.path.join(current, "lakefile.toml")):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return start
        current = parent


PACKAGE = _package_root(LIB)

CORPUS = os.environ.get("PYLATE_CORPUS") or os.path.join(LIB, "corpus")
DOC = os.path.join(LIB, "doc")
DATA = os.path.join(HARNESS, "data")
GATES = os.path.join(HARNESS, "gates")
PROBES = os.path.join(HARNESS, "probes")
GENERATORS = os.path.join(HARNESS, "generators")

#: The analyzer, and the Lean suite runner. Built by `lake build`; invoked through
#: the Lake build directory rather than the package `build/bin`, because those
#: entries are Apollo envroot wrappers that do not run inside a Brazil workspace.
#:
#: `PYLATE_BIN` overrides the directory. This package's Lean dependencies are
#: Brazil-provided path deps, so it only builds under `brazil-build`; `Pylate/`
#: itself imports nothing from Strata, so it can be built standalone elsewhere
#: and pointed at from here. Same escape hatch as `PYLATE_CORPUS` above.
BIN = os.environ.get("PYLATE_BIN") or os.path.join(PACKAGE, ".lake", "build", "bin")
PYLATE = os.path.join(BIN, "pylate")
PYLATE_TESTS = os.path.join(BIN, "pylateTests")

#: Lean sources the harness reads: the method inventory, and the transfers, whose
#: `CLAIM:` markers are the transfer-rule inventory.
LEAN = LIB
TRANSFERS = os.path.join(LIB, "Transfers")
METHOD_INVENTORY = os.path.join(LIB, "Tables", "MethodInventory.lean")

PIPELINE = os.path.join(HARNESS, "pipeline.py")

#: The Python dialect the Strata producer needs. `strata_python.gen dialect` can
#: regenerate it but requires Python 3.13, and the version set pins 3.12, so the
#: committed copy is what gets used. It is the right one: the Lean importer
#: accepts every file produced with it across the whole corpus, which is the only
#: thing that could go wrong if it had drifted from `Python.toIon`.
DIALECT = os.path.join(PACKAGE, "Python", "strata-python", "dialects",
                       "Python.dialect.st.ion")


def brazil_python() -> str:
    """The interpreter that can import `amazon.ion` and `strata_python`.

    `build-tools/bin/custom-build` exports `PYTHON` after installing the
    `strata_python` wheel; the bare `sys.executable` has neither module, so the
    Strata producer cannot run under it.
    """
    return os.environ.get("PYTHON") or sys.executable


def make_analyzer_input(source: str, dest_base: str) -> str:
    """Produce the analyzer's input for `source`, returning its path.

    The analyzer reads the Strata AST, so this runs the repo's producer
    (`strata_python py_to_strata`) rather than dumping CPython's AST as JSON.
    `dest_base` is the path without a suffix, so a caller can put the artifact
    beside the corpus program or in a temp directory.
    """
    import subprocess
    out = dest_base + ".python.st.ion"
    subprocess.run([brazil_python(), "-m", "strata_python.gen", "-q",
                    "py_to_strata", "--dialect", DIALECT, source, out],
                   check=True, capture_output=True)
    return out


def data(name: str) -> str:
    return os.path.join(DATA, name)


def corpus(name: str) -> str:
    return os.path.join(CORPUS, name)


def on_path() -> None:
    """Make the shared modules importable from a gate or probe subdirectory."""
    if HARNESS not in sys.path:
        sys.path.insert(0, HARNESS)


def guard(*, binary: bool = True, corpus_dir: bool = False,
          lean: bool = False) -> None:
    """Fail loudly for the conditions that would otherwise pass quietly."""
    missing = []
    if binary and not os.path.exists(PYLATE):
        missing.append(f"analyzer not built: {PYLATE} (run `lake build`)")
    if corpus_dir and not os.path.isdir(CORPUS):
        missing.append(f"corpus directory missing: {CORPUS}")
    if lean:
        if not os.path.isdir(TRANSFERS):
            missing.append(f"Lean transfers missing: {TRANSFERS}")
        elif not any(n.endswith(".lean") for n in os.listdir(TRANSFERS)):
            missing.append(f"no Lean sources under {TRANSFERS}")
    if missing:
        for line in missing:
            print(f"harness: {line}", file=sys.stderr)
        raise SystemExit(2)
