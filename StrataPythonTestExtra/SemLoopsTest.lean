/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.Loops

/-! # Eight loops cost linear time

Runs eight loops through `StrataPythonTest.Util.Loops`, at 100,000 and at 1,000,000 iterations:
`print`, a `try` whose `except` catches, a list append (`l += [i]`), `d[i] = i`, `del d[i]` (after
the writes), an attribute write, a call of a Python function, and a list comprehension. It runs
only when `SEM_LOOPS` is set.
-/

namespace StrataPython.SemLoopsTest

/-- Each loop's program for `n` iterations. -/
private meta def loops (n : Nat) : List (String × String) := [
  ("print", s!"for i in range({n}):\n    print(i)\n"),
  ("try and except", s!"for i in range({n}):\n    try:\n        raise ValueError\n    except ValueError:\n        pass\n"),
  ("list append", s!"l = []\nfor i in range({n}):\n    l += [i]\n"),
  ("dict write", s!"d = \{}\nfor i in range({n}):\n    d[i] = i\n"),
  ("dict deletion", s!"d = \{}\nfor i in range({n}):\n    d[i] = i\nfor i in range({n}):\n    del d[i]\n"),
  ("attribute write", s!"class A:\n    pass\no = A()\nfor i in range({n}):\n    o.x = i\n"),
  ("call", s!"def f(x):\n    return x\nfor i in range({n}):\n    f(i)\n"),
  ("comprehension", s!"l = [i + 1 for i in range({n})]\n")]

#eval StrataPython.Loops.run "SemLoopsTest" loops

end StrataPython.SemLoopsTest
