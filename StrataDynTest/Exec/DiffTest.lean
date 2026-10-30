/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Diff
-- `#guard` runs the parser and the renderer as compiled code.
meta import StrataDyn.Exec.Diff

set_option autoImplicit false

/-!
# Verdict files

Rendering and parsing verdict files, their malformed inputs, the changes between two runs, and the
classification of two traces.
-/

namespace Strata.Dyn.Exec.DiffTest

open Strata.Dyn.Exec.Diff

/-- The entries, or the error message, of a parse. -/
def parsed (text : String) : Sum String (Array Entry) :=
  match parse text with
  | .ok es => .inr es
  | .error e => .inl e

/-- One entry of each verdict, out of order; the gap's message contains the separator. -/
def entries : Array Entry :=
  #[⟨"b.py", .gap "py.call | unknown"⟩, ⟨"a.py", .agree⟩, ⟨"d.py", .syntax⟩,
    ⟨"c.py", .known "dict order"⟩]

-- The file is sorted by path, one line per entry.
#guard render entries ==
  "a.py | agree\nb.py | gap | py.call | unknown\nc.py | known | dict order\nd.py | syntax\n"

-- Reading the file back gives the entries in path order, the gap's message whole.
#guard parsed (render entries) ==
  .inr #[⟨"a.py", .agree⟩, ⟨"b.py", .gap "py.call | unknown"⟩, ⟨"c.py", .known "dict order"⟩,
    ⟨"d.py", .syntax⟩]

-- A message with a newline and a backslash stays on one line, and reads back whole.
#guard render #[⟨"a.py", .gap "line 1\nline 2 \\n"⟩] == "a.py | gap | line 1\\nline 2 \\\\n\n"
#guard parsed (render #[⟨"a.py", .gap "line 1\nline 2 \\n"⟩]) ==
  .inr #[⟨"a.py", .gap "line 1\nline 2 \\n"⟩]

-- An empty file has no entries, and empty lines are ignored.
#guard parsed "" == .inr #[]
#guard parsed "\na.py | agree\n\n" == .inr #[⟨"a.py", .agree⟩]

-- Malformed lines: an unknown verdict, a gap without a message, and an extra field.
#guard parsed "a.py | maybe\n" == .inl "malformed verdict line: a.py | maybe"
#guard parsed "a.py | gap\n" == .inl "malformed verdict line: a.py | gap"
#guard parsed "a.py | agree | x\n" == .inl "malformed verdict line: a.py | agree | x"

-- Two verdicts for one path, and lines out of order.
#guard parsed "a.py | agree\na.py | syntax\n" == .inl "two verdicts for a.py"
#guard parsed "b.py | agree\na.py | agree\n" == .inl "verdicts out of order at a.py"

-- The changes: one verdict changed, one program gone, one new; an unchanged one is not listed.
#guard changes #[⟨"a.py", .agree⟩, ⟨"b.py", .agree⟩, ⟨"c.py", .syntax⟩]
    #[⟨"a.py", .agree⟩, ⟨"b.py", .gap "g"⟩, ⟨"e.py", .agree⟩] ==
  #[.changed "b.py" .agree (.gap "g"), .removed ⟨"c.py", .syntax⟩, .added ⟨"e.py", .agree⟩]
#guard changes entries entries == #[]

#guard (Change.changed "b.py" .agree (.gap "g")).render ==
  "b.py: pinned b.py | agree, now b.py | gap | g"

-- `checkOrUpdate`: with no pinned file every entry is new; update mode writes the file, and then
-- a check finds no change, and one changed verdict.
/--
info: [new: a.py | agree]
[]
[]
[a.py: pinned a.py | agree, now a.py | syntax]
-/
#guard_msgs in
#eval show IO Unit from do
  let dir ← IO.FS.createTempDir
  let path := dir / "verdicts.txt"
  IO.println ((← checkOrUpdate path #[⟨"a.py", .agree⟩] false).toList.map (·.render))
  IO.println ((← checkOrUpdate path #[⟨"a.py", .agree⟩] true).toList.map (·.render))
  IO.println ((← checkOrUpdate path #[⟨"a.py", .agree⟩] false).toList.map (·.render))
  IO.println ((← checkOrUpdate path #[⟨"a.py", .syntax⟩] false).toList.map (·.render))
  IO.FS.removeDirAll dir

-- A malformed pinned file makes the check throw, naming the file.
/-- info: malformed verdict line: a.py | maybe -/
#guard_msgs in
#eval show IO Unit from do
  let dir ← IO.FS.createTempDir
  let path := dir / "verdicts.txt"
  IO.FS.writeFile path "a.py | maybe\n"
  try discard <| checkOrUpdate path #[] false
  catch e => IO.println ((toString e).replace (toString path ++ ": ") "")
  IO.FS.removeDirAll dir

-- Equal traces agree, even when a reason is documented.
#guard classify "1\n" "1\n" (some ⟨"r", some "3\n"⟩) matches .ok .agree
-- A documented difference is known only with its pinned trace; an undocumented one fails.
#guard classify "1\n" "2\n" (some ⟨"r", some "1\n"⟩) matches .ok (.known "r")
#guard classify "1\n" "2\n" (some ⟨"r", some "3\n"⟩) matches .error "the run's trace differs from its pinned trace"
#guard classify "1\n" "2\n" none matches .error "the traces differ"
-- While the pin is written, any trace is accepted.
#guard classify "1\n" "2\n" (some ⟨"r", none⟩) matches .ok (.known "r")

end Strata.Dyn.Exec.DiffTest
