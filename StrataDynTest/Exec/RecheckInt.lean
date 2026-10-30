/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.RecheckEnv

/-! # `hid.Num` as an integer, and `hid.Flag` as a Boolean -/

attribute [dyn_type Strata.Dyn.ExecTest.Hid.Num] Int
attribute [dyn_type Strata.Dyn.ExecTest.Hid.Flag] Bool
