/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.FileRange

/-!
# The Python front-end's missing-source-location sentinel

Every Laurel AST node carries a `FileRange`, so a translator that has not yet
threaded a real location through has to supply *something*. This module holds
the one sentinel the Python front-end uses for that, deliberately owned here
rather than in `Strata`: the debt is the Python front-end's, so downstream
languages and the Laurel compiler passes cannot reach for it.

Each remaining use is a place where the Python source position is available but
not yet plumbed to the point of construction. Prefer passing the real range
(most builders in `PythonToLaurel` have a `…WithLoc` variant that takes one).
-/

public section
namespace StrataPython

/-- Placeholder for a Laurel AST node's `source` when the Python front-end has
not yet threaded the real Python source range to the point of construction.

Do not add new uses: pass the actual range instead. Formatting treats an empty
`SourceRange` as "no location", so a diagnostic reported at this range simply
prints without a position rather than pointing somewhere wrong. -/
def unknownSource : Strata.FileRange :=
  { file := .file "<unknown>", range := Strata.SourceRange.none }

end StrataPython
end -- public section
