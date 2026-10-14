/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataPython.Mantle.Translate
import StrataMantle.Env.WF
-- The translator and the checker both run as compiled code below.
meta import StrataMantle.WF
meta import StrataPython.Mantle.Translate
meta import StrataPythonTest.Mantle.TestUtil

set_option autoImplicit false

/-!
# The translator's output is well formed

Python ASTs written by hand, so these run without Python.  `StrataPythonTestExtra/
MantleTranslateTest.lean` checks the corpus.

    x = 1
    def f(a):
        while a < x:
            a = a + 1
        return a
    f(2)
    g = 1j
-/

namespace StrataPython.Mantle.PyTranslateTest

open Strata.Mantle
open StrataPython.Mantle.PyTranslate
open StrataPython (stmt expr)
open StrataDDM (SourceRange)

private def none' : SourceRange := .none

private def load (s : String) : expr SourceRange := .Name none' ⟨none', s⟩ (.Load none')

private def store (s : String) : expr SourceRange := .Name none' ⟨none', s⟩ (.Store none')

private def int (n : Nat) : expr SourceRange :=
  .Constant none' (.ConPos none' ⟨none', n⟩) ⟨none', none⟩

private def assign (x : String) (e : expr SourceRange) : stmt SourceRange :=
  .Assign none' ⟨none', #[store x]⟩ e ⟨none', none⟩

private def fDef : stmt SourceRange :=
  let a : StrataPython.arg SourceRange := .mk_arg none' ⟨none', "a"⟩ ⟨none', none⟩ ⟨none', none⟩
  let args : StrataPython.arguments SourceRange :=
    .mk_arguments none' ⟨none', #[]⟩ ⟨none', #[a]⟩ ⟨none', none⟩ ⟨none', #[]⟩ ⟨none', #[]⟩
      ⟨none', none⟩ ⟨none', #[]⟩
  let test := .Compare none' (load "a") ⟨none', #[.Lt none']⟩ ⟨none', #[load "x"]⟩
  let loop := .While none' test ⟨none', #[assign "a" (.BinOp none' (load "a") (.Add none')
    (int 1))]⟩ ⟨none', #[]⟩
  .FunctionDef none' ⟨none', "f"⟩ args ⟨none', #[loop, .Return none' ⟨none', some (load "a")⟩]⟩
    ⟨none', #[]⟩ ⟨none', none⟩ ⟨none', none⟩ ⟨none', #[]⟩

private def call : stmt SourceRange :=
  .Expr none' (.Call none' (load "f") ⟨none', #[int 2]⟩ ⟨none', #[]⟩)

private def complexLit : stmt SourceRange :=
  assign "g" (.Constant none' (.ConComplex none' ⟨none', "0.0"⟩ ⟨none', "1.0"⟩) ⟨none', none⟩)

private def supported : Result := translate "m" #[assign "x" (int 1), fDef, call]

private def withComplex : Result := translate "m" #[assign "x" (int 1), fDef, call, complexLit]

-- The translator does not reduce in the kernel: the checker runs as compiled code.
#guard Module.Raw.WF supported.module
#guard (StrataPython.Mantle.TestUtil.dottedNames supported.module).isEmpty

#guard supported.ok

-- The module body, then `f`.
#guard supported.module.funcs.map (nameText ·.name) = #["m.<module>", "m.f"]

-- A rejected complex literal is a diagnostic, and the module stays well formed.
#guard Module.Raw.WF withComplex.module
#guard withComplex.diagnostics.map (·.message) = #["complex literal is not supported"]

/-- `a, b += 1`, which CPython's parser rejects, built by hand: the translator reports an
internal error rather than dropping the statement. -/
private def augTuple : Result := translate "m" #[.AugAssign none'
  (.Tuple none' ⟨none', #[store "a", store "b"]⟩ (.Store none')) (.Add none') (int 1)]

#guard augTuple.diagnostics.map (·.message) = #["a target CPython rejects"]

#guard augTuple.diagnostics.all (·.kind == .internal)

end StrataPython.Mantle.PyTranslateTest
