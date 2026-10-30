/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Dyn.PySpec.Module
meta import StrataPython.Specs
meta import StrataPythonTest.Util.Python

/-! # The standard-library bases that a model may name, checked against CPython 3.12

CPython 3.12 runs `class X(B): pass` for each class `B` of `PySpec.subclassableStd`, and each
must succeed. It also runs it for some classes that refuse subclasses, which must fail and must
not be in the list. `PySpec.builtinClasses` must be exactly the classes of `builtins`, and
`Specs.builtinNames` its public names. The test needs Python 3.12, as `findPython3` finds it;
`SKIP_PYTHON_TESTS=1` skips it.
-/

namespace StrataPython.StdBasesTest

open StrataPython.Dyn.PySpec

/-- Classes that refuse subclasses in CPython 3.12. -/
private meta def refused : List String :=
  ["builtins.bool", "builtins.range", "builtins.slice", "builtins.memoryview", "typing.Union",
   "typing.Optional", "typing.Literal", "typing.Final", "typing.Generic"]

private meta def script (accepted refused classes names : List String) : String :=
  let lst (xs : List String) := "[" ++ ", ".intercalate (xs.map (s!"'{·}'")) ++ "]"
  s!"import importlib, warnings
warnings.simplefilter('ignore')
def accepts(name):
    mod, _, attr = name.rpartition('.')
    try:
        exec('class X(B): pass', \{'B': getattr(importlib.import_module(mod), attr)})
        return True
    except Exception:
        return False
for n in {lst accepted}:
    if not accepts(n): print('refused: ' + n)
for n in {lst refused}:
    if accepts(n): print('accepted: ' + n)
import builtins
real = sorted(n for n in dir(builtins) if not n.startswith('_') and isinstance(getattr(builtins, n), type))
if real != {lst classes}: print('builtin classes differ: ' + str(sorted(set(real) ^ set({lst classes}))))
names = sorted(n for n in dir(builtins) if not n.startswith('_'))
if names != sorted({lst names}): print('builtin names differ: ' + str(sorted(set(names) ^ set({lst names}))))
"

private meta def runAll : IO Unit := do
  if let some skip ← IO.getEnv "SKIP_PYTHON_TESTS" then
    if !skip.isEmpty then return
  let python ← findPython3 (minVersion := 12) (maxVersion := 12)
  let out ← IO.Process.output
    { cmd := python.toString, args := #["-I", "-c", script subclassableStd.toList refused builtinClasses
      Specs.builtinNames.toList] }
  unless out.exitCode == 0 do throw <| IO.userError s!"the script failed: {out.stderr}"
  let listed := refused.filter subclassableStd.contains
  unless out.stdout.isEmpty && listed.isEmpty do
    throw <| IO.userError s!"{out.stdout}listed but refused by CPython: {listed}"

#guard_msgs in
#eval runAll

end StrataPython.StdBasesTest
