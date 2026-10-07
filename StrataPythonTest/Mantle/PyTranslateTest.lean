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
meta import StrataMantle.Env.WF

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
    g = lambda: 0
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

private def lam : stmt SourceRange :=
  let args : StrataPython.arguments SourceRange :=
    .mk_arguments none' ⟨none', #[]⟩ ⟨none', #[]⟩ ⟨none', none⟩ ⟨none', #[]⟩ ⟨none', #[]⟩
      ⟨none', none⟩ ⟨none', #[]⟩
  assign "g" (.Lambda none' args (int 0))

private def supported : Result := translate "m" #[assign "x" (int 1), fDef, call]

private def withLambda : Result := translate "m" #[assign "x" (int 1), fDef, call, lam]

-- The translator does not reduce in the kernel: the checker runs as compiled code.
#guard decide (Module.WF supported.module)

example : supported.ok = true := by native_decide

/-- The module body, then `f`. -/
example : supported.module.funcs.map (nameText ·.name) = #["m.<module>", "m.f"] := by
  native_decide

-- A rejected `lambda` is a diagnostic, and the module stays well formed.
#guard decide (Module.WF withLambda.module)

example : withLambda.diagnostics.map (·.message) = #["lambda is not supported"] := by
  native_decide

end StrataPython.Mantle.PyTranslateTest
