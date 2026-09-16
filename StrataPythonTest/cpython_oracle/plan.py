"""Select eligible methods from the manifest and generate one program per method.

Writes:
  <outdir>/selection.json          what was selected, with obligation locations
  <outdir>/gen/<file>.<method>.py  the program handed to the front end

`--filter` restricts the SELECTION, not just what gets run. Filtering later in the
pipeline would leave the unmatched methods in selection.json with no engine output,
and compare.py would report every one of them as a failure.
"""
from __future__ import annotations

import argparse
import ast
import json
import pathlib
import sys
import warnings

sys.path.insert(0, str(pathlib.Path(__file__).parent))

from corpus import Corpus
from prepare import generate, normalise_source
from selector import select_file


def read_manifest(path: pathlib.Path) -> list[str]:
    out = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            out.append(line)
    return out


def main(argv: list[str]) -> int:
    here = pathlib.Path(__file__).parent
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest", nargs="?", default=str(here / "manifest.txt"))
    ap.add_argument("outdir", nargs="?", default=str(here / "build"))
    ap.add_argument("--filter", default="",
                    help="only methods whose stem contains this substring")
    args = ap.parse_args(argv[1:])
    manifest = pathlib.Path(args.manifest)
    outdir = pathlib.Path(args.outdir)

    gendir = outdir / "gen"
    # Remove EVERY per-stem artifact, not just the .py. A leftover .interp from an
    # earlier run would be read as this run's result.
    if gendir.exists():
        for stale in gendir.iterdir():
            if stale.is_file():
                stale.unlink()
    gendir.mkdir(parents=True, exist_ok=True)

    wanted = read_manifest(manifest)
    methods: list[dict] = []
    skipped: list[dict] = []

    # Parsing the corpus raises CPython's own SyntaxWarnings -- test_fstring alone
    # accounts for 30, from escapes it deliberately gets wrong. They are not about
    # Strata and would drown out the suite's actual output.
    warnings.simplefilter("ignore", SyntaxWarning)

    with Corpus() as corpus:
        available = set(corpus.files())
        for relpath in wanted:
            if relpath not in available:
                skipped.append({"file": relpath, "reason": "not in tarball"})
                continue
            source = normalise_source(corpus.read(relpath))
            for m in select_file(source, relpath):
                stem = f"{pathlib.Path(relpath).stem}.{m['cls']}.{m['method']}"
                if args.filter and args.filter not in stem:
                    continue
                try:
                    program, n_lowered = generate(source, m)
                    ast.parse(program)
                except (SyntaxError, ValueError, KeyError) as e:
                    skipped.append({"file": relpath, "method": m["method"],
                                    "reason": f"generate: {type(e).__name__}: {e}"})
                    continue
                (gendir / f"{stem}.py").write_text(program)
                methods.append({**m, "stem": stem,
                                "assertionCount": n_lowered})
        version = corpus.version
        # Extract the corpus `test` package once. Both the generated-program check in
        # runner.py and oracle.py need `test.support` importable, and the built
        # runtime strips it.
        libdir = corpus.extract_lib(outdir / "cpythonlib")

    selection = {
        "cpython": version,
        "corpusLib": str(libdir),
        "manifest": str(manifest.name),
        "methods": methods,
        "skipped": skipped,
    }
    (outdir / "selection.json").write_text(json.dumps(selection, indent=2,
                                                      sort_keys=True) + "\n")

    per_file: dict[str, int] = {}
    for m in methods:
        per_file[m["file"]] = per_file.get(m["file"], 0) + 1
    n_obl = sum(m["assertionCount"] for m in methods)
    filtered = f", filter={args.filter!r}" if args.filter else ""
    print(f"plan: CPython {version}, {len(methods)} methods, "
          f"{n_obl} assertions{filtered}")
    for f in sorted(per_file):
        print(f"  {f:<26}{per_file[f]:>4} methods")
    if skipped:
        print(f"  skipped: {len(skipped)}")
        for s in skipped[:10]:
            print(f"    {s.get('file')} {s.get('method','')}: {s['reason']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
