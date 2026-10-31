"""Write `SortCases.lean`: CPython 3.12's list sort on test lists, with every comparison it makes.

    python3.12 StrataDynTest/Util/gen_sort_cases.py > StrataDynTest/Util/SortCases.lean

Each case is a list of values, each with its index. The sort compares items by a `__lt__` that
logs the two indices and answers by the case's mode:
- `values`: the values' `<`;
- `chaos`: `(7 * i + 13 * j + c) % 3 == 0`, where `i` and `j` are the indices and `c` counts the
  comparisons before it;
- `flipped`: the values' `<`, flipped when `(7 * i + 13 * j + c) % 11 == 0`.
The last two are orders that are not consistent, so that the sort takes the paths that CPython
keeps for such orders. A case records the log and the order of the indices after the sort. Its
failures make the `f`-th comparison raise, for some `f`; each records the order after the
failure. (Until the failure, the log is the first `f` pairs of the case's log.)
"""
import random
import sys

assert sys.version_info[:2] == (3, 12), "run with CPython 3.12"

MODES = {"values": 0, "chaos": 1, "flipped": 2}


class Fail(Exception):
    pass


def run(values, mode, fail=None):
    log = []

    class K:
        __slots__ = ("i", "v")

        def __init__(self, i, v):
            self.i, self.v = i, v

        def __lt__(self, other):
            c = len(log)
            if fail is not None and c == fail:
                raise Fail
            log.append((self.i, other.i))
            if mode == "chaos":
                return (7 * self.i + 13 * other.i + c) % 3 == 0
            lt = self.v < other.v
            if mode == "flipped" and (7 * self.i + 13 * other.i + c) % 11 == 0:
                return not lt
            return lt

    xs = [K(i, v) for i, v in enumerate(values)]
    try:
        xs.sort()
    except Fail:
        pass
    return log, [x.i for x in xs]


def with_runs(rng, n, lo, hi, desc=0.5):
    v = []
    while len(v) < n:
        k = rng.randrange(lo, hi)
        start = rng.randrange(5000)
        r = list(range(start, start + k))
        v += r[::-1] if rng.random() < desc else r
    return v[:n]


def interleaved(rng, na, nb):
    """Two ascending runs whose values interleave in blocks of 8 to 50. The first run ends with a
    value above all others and the second starts with one below all others, so that `merge_at`
    keeps every item, and the runs' lengths alone choose the merge."""
    a, b, x = [], [], 0
    while len(a) < na or len(b) < nb:
        for side in (a, b):
            k = rng.randrange(8, 51)
            side.extend(range(x, x + k))
            x += k
    return a[:na - 1] + [10 ** 6] + [-1] + b[:nb - 1]


def spread(lo, hi, k):
    """`k` failure points spread over the comparisons `[lo, hi)`."""
    return sorted({lo + (hi - lo) * i // k for i in range(k)})


def cases():
    # Each list draws from its own random stream, so that adding or removing a case changes no
    # other case.
    def rng(k):
        return random.Random(20261027 + k)

    def randoms(k, n, hi):
        """`n` random values below `hi`, from the stream `k`."""
        r = rng(k)
        return [r.randrange(hi) for _ in range(n)]

    out = []
    for n in range(0, 9):
        out.append((f"random {n}", randoms(n, n, 4), "values", []))
    for n in (63, 64, 65, 130):
        out.append((f"random {n}", randoms(1000 + n, n, n // 2 + 1), "values", []))
    out.append(("runs 100", with_runs(rng(1100), 100, 1, 40, 0.4), "values", []))
    out.append(("runs 300", with_runs(rng(1300), 300, 1, 40, 0.4), "values", []))
    out.append(("descending 200", list(range(200, 0, -1)), "values", []))
    out.append(("ascending then one 150", list(range(149)) + [-1], "values", []))
    out.append(("few values 256", randoms(2256, 256, 3), "values", []))
    base = randoms(3120, 120, 1000)
    out.append(("random 120", base, "values", [0, 1, 30, 400, 600]))
    # Two runs that merge_lo merges (the longer second) and merge_hi merges (the longer first);
    # the failures fall after count_run's `na + nb - 1` comparisons, inside the merges.
    for name, na, nb in (("merge_lo", 200, 300), ("merge_hi", 300, 200)):
        v = interleaved(random.Random(na), na, nb)
        total = len(run(v, "values")[0])
        out.append((f"interleaved {name}", v, "values", spread(na + nb - 1, total, 12)))
    # Runs of 145, 32, 39, 34 and 6 items, each starting below the end of the one before: the
    # stack merges at its third run from the top.
    v, start = [], 10 ** 5
    for k in (145, 32, 39, 34, 6):
        start -= 1000
        v += list(range(start, start + k))
    total = len(run(v, "values")[0])
    out.append(("third from the top 256", v, "values", spread(250, total, 8)))
    # Two blocks shorter than minrun, the first all below the second: merge_at finds the runs in
    # order.
    rng2 = random.Random(3)
    v = [rng2.randrange(100) for _ in range(32)] + [rng2.randrange(100, 200) for _ in range(32)]
    out.append(("blocks in order 64", v, "values", []))
    # merge_lo with one item left in each run.
    out.append(("one item each 64", list(range(31)) + [100, 50] + list(range(101, 132)), "values",
                [40, 60]))
    # Lists that reach single paths of the merges: merge_lo's CopyB on entry, after its first
    # gallop and after its second; merge_hi's CopyA after its first gallop and after its second;
    # merge_hi galloping with min_gallop at 1.
    out.append(("merge_lo copy on entry 64",
                list(range(31)) + [100, 50, 60] + list(range(101, 131)), "values", []))
    out.append(("merge_lo copy after a gallop 139",
                list(range(100, 159)) + [1000] + list(range(7)) + list(range(159, 221))
                + list(range(1001, 1011)), "values", []))
    out.append(("merge_lo copy after the second gallop 135",
                list(range(1000, 1053)) + [5000, 10 ** 6] + [-1] + list(range(7)) + [2000]
                + list(range(2001, 2061)) + list(range(6000, 6011)), "values", []))
    out.append(("merge_hi copy after the first gallop 70",
                list(range(10, 70)) + list(range(200, 208)) + [5, 150], "values", []))
    # merge_hi's galloping round ends with no item left in the first run.
    out.append(("merge_hi gallop empties the first run 71",
                [50] + list(range(100, 167)) + [1, 2, 70], "values", []))
    out.append(("merge_hi copy after a gallop 89",
                list(range(10, 69)) + list(range(200, 208)) + [5] + list(range(100, 121)),
                "values", []))
    out.append(("merge_hi gallop at its floor 160",
                [16 * b + i for b in range(12) for i in range(8)]
                + [16 * b + 8 + i for b in range(8) for i in range(8)], "values", []))
    # Paths that only an inconsistent order reaches: merge_at's gallop_left finds nothing, and
    # merge_lo's galloping ends with no item left in the first run.
    out.append(("flipped halves 512",
                [(i // 8) * 16 + 8 + i % 8 for i in range(256)]
                + [(i // 8) * 16 + i % 8 for i in range(256)], "flipped", []))
    out.append(("flipped 66", [int(x) for x in
                "0 0 2 0 0 3 1 2 3 3 1 2 2 1 2 0 0 0 3 0 2 1 3 1 2 1 3 1 0 0 1 2 0 3 0 1 0 0 1 3 2 "
                "0 1 2 1 1 3 2 2 1 1 0 0 1 1 3 2 2 0 1 0 3 2 3 1 0".split()], "flipped", []))
    for n in (2, 5, 40, 64, 65, 200, 400):
        out.append((f"chaos {n}", list(range(n)), "chaos", []))
    for n in (500, 700):
        out.append((f"flipped runs {n}", with_runs(rng(4000 + n), n, 20, 120), "flipped", []))
    return out


def text(xs):
    return '"' + " ".join(str(x) for x in xs) + '"'


print("""/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! Generated by `gen_sort_cases.py` from CPython 3.12; do not edit. Each case: its name, the
values, the mode of its comparison (0 compares the values, 1 is `chaos`, 2 is `flipped`; see the
generator), every comparison CPython made (as the pairs of indices it compared, flattened), the
indices in their order after the sort, and its failures: the comparison that raises, and the
indices in their order after it. The numbers are kept as space-separated text, which `nats` and
`ints` read: large array literals exceed the elaborator's recursion depth. -/

namespace Strata.Dyn.Util.SortCases

public section

structure Case where
  name : String
  values : String
  mode : Nat
  log : String
  final : String
  fails : Array (Nat × String)

/-- The numbers of a space-separated text. -/
def ints (s : String) : Array Int :=
  ((s.splitOn " ").filter (· ≠ "")).toArray.map String.toInt!

/-- The natural numbers of a space-separated text. -/
def nats (s : String) : Array Nat := (ints s).map Int.toNat

def cases : Array Case := #[""")
items = []
for name, values, mode, fails in cases():
    log, final = run(values, mode)
    flat = [x for p in log for x in p]
    fs = []
    for f in fails:
        flog, ffinal = run(values, mode, f)
        assert flog == log[:f] and f < len(log), name
        fs.append(f"({f}, {text(ffinal)})")
    items.append(f"  {{ name := \"{name}\", values := {text(values)}, mode := {MODES[mode]},\n"
                 f"    log := {text(flat)},\n    final := {text(final)},\n"
                 f"    fails := #[{', '.join(fs)}] }}")
print(",\n".join(items))
print("""]

end

end Strata.Dyn.Util.SortCases""")
