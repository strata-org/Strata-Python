/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.SourceRange

/-!
# Diagnostic interface for PySpec

`PySpecMClass` abstracts the error/warning reporting shared across the PySpec
monads (parsing and assertion processing alike). It is kept in this low-level
module — rather than in `Specs.lean` — so recognizers like
`Specs/Decorators.lean` can be written generically over `[PySpecMClass m]`
without an import cycle on the full spec pipeline. Concrete instances for
`PySpecM` and `SpecAssertionM` live in `Specs.lean`.
-/

namespace StrataPython.Specs

open StrataDDM (SourceRange)

/-- Monads that support PySpec error and warning reporting. -/
public class PySpecMClass (m : Type → Type) where
  /-- Report an error at a source location. -/
  specError (loc : SourceRange) (message : String) : m Unit
  /-- Report a warning at a source location. -/
  specWarning (loc : SourceRange) (message : String) : m Unit
  /-- Run an action; the `Bool` is `true` when it reported no new errors. -/
  runChecked {α} (act : m α) : m (Bool × α)
  /-- Run an action; the `Bool` is `true` when it reported no new errors or
      warnings. -/
  runNoWarn {α} (act : m α) : m (Bool × α)

end StrataPython.Specs
