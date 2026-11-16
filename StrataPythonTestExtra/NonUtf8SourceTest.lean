/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPythonTest.Util.SemDiff
meta import StrataPythonTest.Util.Python

/-! # A program whose coding line makes non-UTF-8 bytes valid

CPython runs `# coding: latin-1` then `x = "caf\xe9"` and prints `café 4`, but `pydyn run` reads
the file as UTF-8 for its diagnostics' source text, and stops with exit code 1 and the message
"Tried to read file ... containing non UTF-8 data". This test pins the current behaviour, a limitation
that §13.1 of docs/PythonToDyn.md lists, and that fails visibly: when the readers decode the bytes
as CPython does, this test fails, and the program should become a corpus program that agrees.
-/

namespace StrataPython.NonUtf8SourceTest

-- `pydyn run` parses the program with Python, so the test needs it, as the other tests do.
#eval StrataPython.withPython fun _ => do
  IO.FS.withTempDir fun dir => do
    let file := dir / "latin.py"
    IO.FS.writeBinFile file ("# coding: latin-1\nx = \"caf".toUTF8 ++ ByteArray.mk #[0xe9] ++
      "\"\nprint(x, len(x))\n".toUTF8)
    let r ← IO.Process.output { cmd := SemDiff.pydynPath.toString, args := #["run", file.toString] }
    let said := r.stdout ++ r.stderr
    unless r.exitCode == 1 && (said.splitOn "containing non UTF-8 data").length > 1 do
      throw <| .userError s!"NonUtf8SourceTest: pydyn run on a latin-1 program now gives \
        exit code {r.exitCode}:\n{said}"
    IO.println "NonUtf8SourceTest: pydyn run refuses the latin-1 program, as pinned"

end StrataPython.NonUtf8SourceTest
