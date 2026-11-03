#!/usr/bin/env python3
"""Write `expected.txt` beside this script: for each sample of user-made values (`SAMPLES`, made by
`prelude.py`) and each name of the union of all samples' `dir`s, CPython 3.12's `hasattr`.

Run it with CPython 3.12: `python3.12 StrataPythonTest/Dyn/hasattr/gen_hasattr_user.py`.
`StrataPythonTestExtra/HasattrUserTest.lean` runs the same attribute reads with the rules.
"""

import keyword
import sys
from pathlib import Path

if sys.version_info[:2] != (3, 12):
    sys.exit(f"gen_hasattr_user.py needs CPython 3.12, not {sys.version.split()[0]}")

HERE = Path(__file__).resolve().parent
SAMPLES = ['e', 'E', 'd', 'D', 'c', 'C', 'f', 'c.m', 'C.cm', 'K', 'K()', 'pr', 'st', 'cl', 'sp',
           'object()', '(1).__add__', '[].append']

ns = {}
exec((HERE / "prelude.py").read_text(), ns)
names = set()
for s in SAMPLES:
    v = eval(s, ns)
    names |= set(dir(v)) | set(dir(type(v)))
names = sorted(n for n in names if n.isidentifier() and not keyword.iskeyword(n))
lines = []
for s in SAMPLES:
    # Each sample gets a fresh prelude, as each test run does: a read such as a class's
    # `__annotations__` writes to the class.
    ns = {}
    exec((HERE / "prelude.py").read_text(), ns)
    v = eval(s, ns)
    for n in names:
        lines.append(f"{s} | {n} | {'true' if hasattr(v, n) else 'false'}")
(HERE / "expected.txt").write_text("\n".join(lines) + "\n")
print(f"wrote {len(lines)} lines")
