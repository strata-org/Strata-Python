/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPythonTest.Util.TraceSource

/-! # The traces file of a differential source

A traces file reads back as it was written, also when a program's text holds a line that looks
like a record's header, and a malformed file is reported. CPython's text names the interpreter's
directories as `<python>`. -/

namespace StrataPython.TraceSourceTest

open StrataPython.TraceSource

private meta def records : Array Record :=
  #[⟨scriptId, "print('trace')\n", ""⟩,
    ⟨"a", "=== b 1 1\nx = 'é'\n", "--- stdout 0\n\n--- outcome\nok\n"⟩,
    ⟨"empty", "", ""⟩]

/-- Results compared by their contents. -/
private meta instance {α : Type} [BEq α] : BEq (Except String α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

#guard parseTraces (renderTraces records) == .ok records
#guard parseTraces "" == .ok #[]
#guard parseTraces "=== a x 1\n" == .error "malformed header: === a x 1"
#guard parseTraces "x\n" == .error "malformed header: x"
#guard parseTraces "=== a 5 0\nabc" == .error "a: the file ends inside its record"

-- CPython's text names the interpreter's directories as `<python>` where they start a path, the
-- longer ones first, and a trace's header gives the masked output's length.
#guard maskInterpreter ["/py", "/py/lib"]
    "--- stdout 12\n/py/lib/a.py\n--- outcome\nraised ImportError: (/py/lib/b.py)\n" ==
  .ok "--- stdout 13\n<python>/a.py\n--- outcome\nraised ImportError: (<python>/b.py)\n"
-- A link's target that ends with the link's own path is masked whole.
#guard maskInterpreter ["/home/u/py", "/local/home/u/py"]
    "--- stdout 0\n\n--- outcome\nraised ImportError: (/local/home/u/py/lib/t.py)\n" ==
  .ok "--- stdout 0\n\n--- outcome\nraised ImportError: (<python>/lib/t.py)\n"
#guard maskInterpreter ["/py"] "--- stdout 2\nab\n--- outcome\nok\n" ==
  .ok "--- stdout 2\nab\n--- outcome\nok\n"
-- A directory named other than at a path's start, a `<python>` in CPython's own text, and two
-- differing runs that name a directory are errors.
#guard maskInterpreter ["/py"] "--- stdout 4\n/py\n\n--- outcome\nok\n" ==
  .error "CPython's text names the interpreter's directory other than at the start of a path"
#guard maskInterpreter ["/py"] "--- stdout 6\n/py2/x\n--- outcome\nok\n" ==
  .error "CPython's text names the interpreter's directory other than at the start of a path"
#guard maskInterpreter ["/py"] "--- stdout 8\n<python>\n--- outcome\nok\n" ==
  .error "CPython's text already holds <python>"
#guard maskInterpreter ["/py"]
    "--- PYTHONHASHSEED=0\n--- stdout 4\n/py/\n--- outcome\nok\n\
      --- PYTHONHASHSEED=1\n--- stdout 4\n/py/\n--- outcome\nok\n" ==
  .error "CPython's two runs differ and name the interpreter's directory"
-- An empty directory names nothing, and a text without a trace's header is masked whole.
#guard maskInterpreter ["", "/py"] "--- stdout 0\n\n--- outcome\nraised E: /py/a /b/\n" ==
  .ok "--- stdout 0\n\n--- outcome\nraised E: <python>/a /b/\n"
#guard maskInterpreter ["/py"] "x /py/a\n" == .ok "x <python>/a\n"
-- Before the comparison, `<python>` is the interpreter's directory again.
#guard unmaskInterpreter "/r" "--- stdout 13\n<python>/a.py\n--- outcome\nok\n" ==
  .ok "--- stdout 7\n/r/a.py\n--- outcome\nok\n"
#guard unmaskInterpreter "/r" "--- stdout 2\nab\n--- outcome\nok\n" ==
  .ok "--- stdout 2\nab\n--- outcome\nok\n"
#guard unmaskInterpreter "/r" "x <python>/a\n" == .ok "x /r/a\n"
#guard unmaskInterpreter "/r"
    "--- PYTHONHASHSEED=0\n--- stdout 9\n<python>/\n--- outcome\nok\n\
      --- PYTHONHASHSEED=1\n--- stdout 0\n\n--- outcome\nok\n" ==
  .error "a recorded text of two runs holds <python>"
-- A round trip gives CPython's text back.
#guard (maskInterpreter ["/py"] "--- stdout 7\n/py/a.b\n--- outcome\nok\n" >>=
    unmaskInterpreter "/py") == .ok "--- stdout 7\n/py/a.b\n--- outcome\nok\n"

-- The oracle's driver joins CPython's two runs with `SemDiff.joinRuns`: each run masked, the header
-- of its output rewritten with the masked length.
#guard SemDiff.joinRuns "--- stdout 2\nab\n" "--- stdout 2\nab\n" == "--- stdout 2\nab\n"
#guard SemDiff.joinRuns "--- stdout 6\n0x7f3a\n--- outcome\nok\n"
    "--- stdout 6\n0x1b2c\n--- outcome\nok\n" ==
  "--- PYTHONHASHSEED=0\n--- stdout 3\n0x?\n--- outcome\nok\n\
    --- PYTHONHASHSEED=1\n--- stdout 3\n0x?\n--- outcome\nok\n"

/-- info: (0, #["a: a known verdict needs a pinned trace of the semantics' run, which this source doesn't keep"]) -/
#guard_msgs in
#eval show IO Unit from do
  let (now, failures) ← judgeAll 1 #[⟨"a", .known "documented"⟩]
    #[("a", "/nonexistent/a.py", "--- stdout 0\n\n--- outcome\nok\n")]
  IO.println (repr (now.size, failures))

end StrataPython.TraceSourceTest
