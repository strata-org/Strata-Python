/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
public import StrataDyn.Env.Handle
import StrataDyn.Env.WF
import StrataDyn.DSL
public import StrataDyn.Exec
public import StrataDyn.Exec.Base

set_option autoImplicit false

/-!
# A datatype's rule checked against a type rule that its table may not see

`RecheckDataGen` generates the Lean types of `hdata.Box` and `hdata.RCell` where `hdata.Num`
is `Int`, by a private import of `RecheckDataInt`.  So `Box`'s field is an `Int`, and
`RCell`'s a ref to an `Int`; `RCell`'s Lean type takes the run token, since it holds a ref.
`RecheckDataTest` imports `RecheckDataGen` but not `RecheckDataInt`, and makes `hdata.Num` a
`Nat`.  `RecheckDataFitTest` imports both, and its table passes.
-/

namespace Strata.Dyn.ExecTest

/-- A language with datatypes. -/
public environment HData extends Base where
  namespace hdata
  open base
  type Num
  data Box where
    | box (n : Num)
  data RCell where
    | rcell (r : Ref Num)
  end hdata

end Strata.Dyn.ExecTest
