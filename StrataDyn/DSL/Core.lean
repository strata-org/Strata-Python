/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.DSL.Syntax
public import StrataDyn.DSL.Elab

/-!
# The `environment` command, without the typed builder

The `environment` command of `StrataDyn.DSL`, for the modules the typed builder imports and
for blocks that are not built into functions.  A module that imports this one and not
`StrataDyn.Build.Typed` gets no emitters, and `o` names no constant.  `Base` and the builder's
own modules import it, since the typed builder is built over `Base`, and so do the scale tests,
which measure the command alone.  Every other module imports `StrataDyn.DSL`.
-/
