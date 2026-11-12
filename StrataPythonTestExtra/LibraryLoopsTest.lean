/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Loops

/-! # The library's loops cost linear time

Runs five loops of the built-in library through `StrataPythonTest.Util.Loops`, at 100,000 and at
1,000,000 iterations: `sum` and `list` over a user iterator (the resumable path), `reversed` of a
dict followed by `popitem` until it is empty, `enumerate` of a list, and `set.update` with one
member at a time. It runs only when `SEM_LOOPS` is set.
-/

namespace StrataPython.LibraryLoopsTest

/-- A user iterator class whose instance `UserIter(n)` gives `1` to `n`, for the loops that take
the resumable path. -/
private meta def userIter : String :=
  "\n".intercalate ["class UserIter:", "    def __init__(self, n):", "        self.i = 0",
    "        self.n = n", "    def __iter__(self):", "        return self", "    def __next__(self):",
    "        if self.i == self.n:", "            raise StopIteration", "        self.i += 1",
    "        return self.i", ""]

/-- Each loop's program for `n` iterations. The list of `enumerate` is built one `append` per
step, since `list(range(n))` walks its range inside one step, which exhausts `pydyn`'s native
stack at 1,000,000. -/
private meta def loops (n : Nat) : List (String × String) := [
  ("sum of a user iterator", userIter ++ s!"print(sum(UserIter({n})))\n"),
  ("list of a user iterator", userIter ++ s!"print(len(list(UserIter({n}))))\n"),
  ("dict reversed and popitem", s!"d = \{}\nfor i in range({n}):\n    d[i] = i\nfor k in reversed(d):\n    pass\nwhile d:\n    d.popitem()\n"),
  ("enumerate", s!"l = []\nfor i in range({n}):\n    l.append(i)\nfor i, x in enumerate(l):\n    pass\n"),
  ("set update", s!"s = set()\nfor i in range({n}):\n    s.update(\{i})\n")]

#eval StrataPython.Loops.run "LibraryLoopsTest" loops

end StrataPython.LibraryLoopsTest
