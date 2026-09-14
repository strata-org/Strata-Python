"""Check `Tables.knownMethods` against CPython's own method surface.

The list is hand-maintained, and a hand-maintained inventory drifts. It drifted:
`bytes` carried 40 names where CPython has 42, so `fromhex` and `maketrans` were
not modelled *and* not counted as unmodelled -- invisible rather than declared,
which is the failure the `unmodeled-surface` condition exists to prevent. The
same file already records a stale count of opaque methods discovered the same way.

CPython is the oracle here as everywhere else, so this compares against
`dir(builtin)` rather than against a stub package, restricted to callable members
because a property is an attribute read and not a method. A name CPython has and the
table lacks is a gap that reports as nothing; a name the table has and CPython
lacks is a rule for a method that does not exist.

Run: python3.13 tests/known_methods_oracle.py
"""
from __future__ import annotations

import os
import re
import sys

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()
HERE = paths.CORPUS
TABLES = paths.METHOD_INVENTORY

#: The tag whose Lean name maps to each builtin type. Only the types whose
#: method surface `knownMethods` claims to enumerate are listed; `tobj` and the
#: view tags are program-defined or synthesised and have no CPython counterpart.
TAGS = {
    "tstr": str,
    "tbytes": bytes,
    "tlist": list,
    "tdict": dict,
    "tset": set,
    "ttuple": tuple,
    "trange": range,
}


def table_methods(source: str, tag: str) -> list[str] | None:
    """The names `knownMethods` lists for one tag, or None if it has no arm."""
    marker = f"| .{tag} =>"
    if marker not in source:
        return None
    start = source.index(marker)
    end = source.index("]", start)
    return sorted(set(re.findall(r'"([a-z_0-9]+)"', source[start:end])))


def main() -> int:
    with open(TABLES) as handle:
        source = handle.read()

    failures: list[str] = []
    for tag, builtin in sorted(TAGS.items()):
        listed = table_methods(source, tag)
        if listed is None:
            print(f"  {tag:8} no arm in knownMethods, skipped")
            continue
        # Callable members only. `range.start`, `.step` and `.stop` are
        # properties, so they are attribute reads rather than methods and
        # `knownMethods` is right to omit them; comparing against every public
        # member reported those three as drift on this gate's first run.
        actual = sorted(n for n in dir(builtin)
                        if not n.startswith("_")
                        and callable(getattr(builtin, n, None)))
        missing = [n for n in actual if n not in listed]
        extra = [n for n in listed if n not in actual]
        status = "ok" if not missing and not extra else "DRIFT"
        print(f"  {tag:8} table {len(listed):3}  CPython {len(actual):3}  {status}")
        if missing:
            failures.append(
                f"{tag}: CPython has {missing} which the table does not list, "
                "so they are neither modelled nor counted as unmodelled")
        if extra:
            failures.append(
                f"{tag}: the table lists {extra} which CPython does not have")

    if failures:
        print()
        for failure in failures:
            print(f"FAIL {failure}")
        return 1
    print(f"\nknownMethods matches CPython {sys.version.split()[0]} "
          f"for {len(TAGS)} builtin types")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
