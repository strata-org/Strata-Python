#!/usr/bin/env python3
"""Mutants of the rules, each of which a test program must catch.

Each mutant is a textual change to one rule file: an old text, which must occur exactly once, and
the new text. `--check` checks that every old text occurs exactly once, so that the mutants can't
rot silently, and that `mutants_results.txt`, beside this file, records each mutant as caught;
`StrataPythonTestExtra/MutantsTest.lean` runs it in the build. Each result records the git blobs of
the mutated file and of the program that caught it, and `--check` reports the result as stale,
without failing, when either file changes; a change elsewhere (another rule, a golden, a driver)
can also change the catch, and isn't reported. A result without blobs fails the check.

`--run [NAME ...]` runs the mutants (all of them by default) in a git worktree of `HEAD` under a
new temporary directory, so that the package itself is never mutated. It first builds `pydyn`
and the test library there and runs the drivers on the unmutated tree, and stops if one of them fails. Then, one
mutant at a time, it applies the change, rebuilds `pydyn`, runs the semantics against CPython on
the test programs, the corpus and the generated and PyLate programs, records the first program
whose trace or verdict changes, and restores the file. It removes the worktree at the end, also
when it is stopped. It merges its results into `mutants_results.txt` by mutant name. A mutant
that doesn't compile is recorded as broken, and a broken or uncaught mutant fails the run. The
results describe `HEAD`, so it stops if a mutated file has uncommitted changes. It needs CPython
3.12 on `PYTHON` and `PYTHONPATH` set as the build sets them, and it builds `pydyn` and the test
library in the worktree, which with about ten minutes per mutant takes hours, so it is a manual
command. The worktree shares the package's build of its dependencies, so run it only when no
other build of the package runs.

    python3 StrataPythonTest/Dyn/differential/mutants.py --check
    python3 StrataPythonTest/Dyn/differential/mutants.py --run
"""

from __future__ import annotations

import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RESULTS = Path(__file__).resolve().parent / "mutants_results.txt"
SEM = "StrataPython/Dyn/Sem"

# (name, what it breaks, file, old text, new text)
MUTANTS = [
    ("max_last_of_equal", "max keeps the last of equal items",
     f"{SEM}/Library/Iterables.lean",
     "if ← richCompare (if isMax then .gt else .lt) val bv then",
     "if (← richCompare (if isMax then .gt else .lt) val bv) || (← richCompare .eq val bv) then"),
    ("update_ignores_keys", "dict.update ignores the keys() protocol",
     f"{SEM}/Library/Collections.lean",
     "  if hasKeys then return ← dictMergeFirst self x kwargs",
     "  if hasKeys && false then return ← dictMergeFirst self x kwargs"),
    ("sum_no_compensation", "sum adds floats without the compensation",
     f"{SEM}/Library/Sum.lean",
     "if !isZero compensation && !isNaN compensation && !isInf compensation then",
     "if false then"),
    ("hasattr_catches_all", "hasattr catches every exception",
     f"{SEM}/Library/Functions.lean",
     "  let r ← tryCatch (do discard <| getAttr obj name; pure true) fun x => do\n"
     "    if ← isAttributeError x then pure false else throw x",
     "  let r ← tryCatch (do discard <| getAttr obj name; pure true) fun _ => do\n"
     "    pure false"),
    ("sort_no_key_scan", "the sort skips the key scan",
     f"{SEM}/Library/Sort.lean",
     "let compare := if sameType then SortCompare.object else .safe",
     "let compare := SortCompare.safe"),
    ("pop_ignores_finger", "set.pop ignores the finger",
     f"{SEM}/Set.lean",
     "match t.nextEntry t.slots.size (t.finger % t.slots.size) with",
     "match t.nextEntry t.slots.size 0 with"),
    ("lower_no_final_sigma", "str.lower without the final-sigma rule",
     f"{SEM}/Library/Unicode.lean",
     "def lower (s : String) : String := mapAt s fun a i _ => lowerAt a i",
     "def lower (s : String) : String := mapAt s fun _ _ c => toLower c"),
    ("binary_no_subclass_rule", "the binary protocol drops the subclass rule",
     f"{SEM}/Proto/Ops.lean",
     "let revFirst ← if sameType || !(← isUserObject b) then pure false",
     "let revFirst ← if true then pure false"),
    ("translate_no_cache", "translate looks every ASCII character up",
     f"{SEM}/Library/StrTranslate.lean",
     "        | some (some e) => pure (some e)\n        | _ => fastEntry table c",
     "        | _ => fastEntry table c"),
    ("setdefault_hashes_twice", "dict.setdefault hashes its key twice",
     f"{SEM}/Library/DictMethods.lean",
     "  PyWrites.dictSet self k dflt (some h) (keyEq k)\n  return dflt",
     "  PyWrites.dictSet self k dflt (some (← hash k)) (keyEq k)\n  return dflt"),
]

# The variables that switch the drivers from comparing to updating their goldens, or to a
# generated run of their own; the runner clears them.
UPDATE_VARS = {"SEM_UPDATE", "DYN_UPDATE", "PYSCOPE_UPDATE", "GEN_SEED", "GEN_COUNT"}

# The drivers that compare the semantics with CPython, in the order the runner tries them.
DRIVERS = [
    "StrataPythonTestExtra/SemDiffTest.lean",
    "StrataPythonTestExtra/PylateDiffTest.lean",
    "StrataPythonTestExtra/GeneratedDiffTest.lean",
]


def results() -> dict[str, str]:
    """The recorded result of each mutant, by name."""
    if not RESULTS.exists():
        return {}
    return {l.split(" | ")[0]: l for l in RESULTS.read_text().splitlines() if l}


def blob(root: Path, path: str | None) -> str:
    """The git blob of the file `path` under `root` as it is on disk (`git hash-object`, which
    needs no repository), or `-` for no path, a missing file, or no git."""
    if path is None or not (root / path).is_file():
        return "-"
    try:
        r = subprocess.run(["git", "hash-object", "--", path], cwd=root, capture_output=True,
                           text=True)
    except OSError:
        return "-"
    return r.stdout.strip()[:12] if r.returncode == 0 else "-"


def program_path(root: Path, caught: str) -> str | None:
    """The source file of the program that a result names (`lib_sum (SemDiffTest)`), if one file
    under `StrataPythonTest/` has that name."""
    name = caught.split(" (")[0]
    paths = sorted((root / "StrataPythonTest").rglob(f"{name}.py"))
    return str(paths[0].relative_to(root)) if len(paths) == 1 else None


def stamp(root: Path, file: str, caught: str) -> str:
    """The blobs of the mutated file and of the catching program, as a result records them."""
    return f"{blob(root, file)} {blob(root, program_path(root, caught))}"


def text_problems(root: Path = ROOT) -> list[str]:
    """The mutants whose old text doesn't occur exactly once in its file under `root`."""
    bad = []
    for name, _, file, old, _new in MUTANTS:
        n = (root / file).read_text().count(old)
        if n != 1:
            bad.append(f"{name}: its text occurs {n} times in {file}")
    return bad


def check() -> int:
    """Each mutant's old text occurs exactly once, and the recorded results name every mutant,
    with its description, as caught."""
    bad = text_problems()
    recorded = results()
    for name, what, *_ in MUTANTS:
        line = recorded.get(name)
        if line is None:
            bad.append(f"{name}: no recorded result in {RESULTS.name}")
        elif not line.startswith(f"{name} | {what} | ") or "NOT CAUGHT" in line or "BROKEN" in line:
            bad.append(f"{name}: its recorded result is not a catch: {line}")
        elif len(line.split(" | ")) != 4:
            bad.append(f"{name}: its recorded result has no blobs; run --run {name} again")
    for name in recorded.keys() - {m[0] for m in MUTANTS}:
        bad.append(f"{name}: a recorded result of no mutant")
    for b in bad:
        print(b, file=sys.stderr)
    # A result measured on other versions of its files: reported, not a failure.
    for name, _, file, *_ in MUTANTS:
        parts = recorded.get(name, "").split(" | ")
        if len(parts) == 4 and parts[3] != stamp(ROOT, file, parts[2]):
            print(f"stale: {name} was measured on other versions of {file} or of its catching "
                  f"program; run --run {name} again")
    return 1 if bad else 0


def first_disagreement(output: str) -> str | None:
    """The first program whose trace or verdict changes, in a driver's output."""
    for line in output.splitlines():
        m = re.match(r"^(\S+): (the traces differ|pinned .*)$", line)
        if m:
            return m.group(1)
    return None


def on_signal(signum, _frame):
    raise SystemExit(f"stopped by signal {signum}")


def run(names) -> int:
    known = {m[0] for m in MUTANTS}
    unknown = [n for n in names if n not in known]
    if unknown:
        print(f"no such mutant: {', '.join(unknown)}", file=sys.stderr)
        return 1
    todo = [m for m in MUTANTS if not names or m[0] in names]
    files = sorted({m[2] for m in todo})
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *files], cwd=ROOT).returncode != 0:
        print("the mutated files have uncommitted changes; commit or stash them first",
              file=sys.stderr)
        return 1
    signal.signal(signal.SIGTERM, on_signal)
    signal.signal(signal.SIGHUP, on_signal)
    # The drivers in their compare mode, whatever the caller's environment says.
    env = {k: v for k, v in os.environ.items() if k not in UPDATE_VARS}
    work = Path(tempfile.mkdtemp(prefix="mutants-"))
    tree = work / "tree"
    subprocess.run(["git", "worktree", "add", "--detach", str(tree), "HEAD"], cwd=ROOT,
                   check=True, capture_output=True)
    try:
        (tree / ".lake").mkdir(exist_ok=True)
        overrides = ROOT / ".lake" / "package-overrides.json"
        if overrides.exists():
            shutil.copy(overrides, tree / ".lake" / overrides.name)
        bad = text_problems(tree)
        if bad:
            print("\n".join(bad), file=sys.stderr)
            return 1

        def sh(args):
            return subprocess.run(args, cwd=tree, capture_output=True, text=True, env=env)

        last_output = [""]

        def disagreement() -> str | None:
            for driver in DRIVERS:
                r = sh(["lake", "env", "lean", driver])
                last_output[0] = r.stdout + r.stderr
                caught = first_disagreement(last_output[0])
                if caught:
                    return f"{caught} ({Path(driver).stem})"
                if r.returncode != 0:
                    return f"a failure of {Path(driver).stem}"
            return None

        # The unmutated tree must pass, so that a catch comes from the mutant.
        # `pydyn`, and the test library that the drivers import.
        if sh(["lake", "build", "pydyn", "StrataPythonTest"]).returncode != 0:
            print("the unmutated tree doesn't build", file=sys.stderr)
            return 1
        base = disagreement()
        if base:
            print(f"the unmutated tree already disagrees: {base}", file=sys.stderr)
            print("\n".join(last_output[0].splitlines()[-20:]), file=sys.stderr)
            return 1
        lines = {}
        for name, what, file, old, new in todo:
            path = tree / file
            text = path.read_text()
            path.write_text(text.replace(old, new, 1))
            try:
                if sh(["lake", "build", "pydyn"]).returncode != 0:
                    caught = "BROKEN: the mutant doesn't compile"
                else:
                    caught = disagreement()
                    if caught and caught.startswith("a failure of"):
                        caught = None
            finally:
                path.write_text(text)
            lines[name] = f"{name} | {what} | {caught or 'NOT CAUGHT'} | " \
                f"{stamp(tree, file, caught or '')}"
            print(lines[name], flush=True)
    finally:
        subprocess.run(["git", "worktree", "remove", "--force", str(tree)], cwd=ROOT,
                       capture_output=True)
        shutil.rmtree(work, ignore_errors=True)
    recorded = results() | lines
    RESULTS.write_text("".join(f"{recorded[m[0]]}\n" for m in MUTANTS if m[0] in recorded))
    return 0 if all(not ("NOT CAUGHT" in l or "BROKEN" in l) for l in lines.values()) else 1


if __name__ == "__main__":
    if "--check" in sys.argv:
        sys.exit(check())
    if "--run" in sys.argv:
        sys.exit(run(sys.argv[sys.argv.index("--run") + 1:]))
    print(__doc__)
