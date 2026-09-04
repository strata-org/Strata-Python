/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PySpecPipeline

meta section

/-! ## Test: cross-file PySpec declaration dedup

Verifies `dedupPySpecDecls`, the first-wins collision check `buildPySpecLaurelM` applies
to PySpec types, procedures, and static fields.
-/

namespace StrataPython.PySpecDedupTest

open Strata

private def mkField (n : String) : Laurel.Field :=
  { name := { text := n }
    isMutable := true
    type := ⟨.UserDefined { text := "int" }, .unknown⟩ }

private def dedupFields (items : Array (Laurel.Field × String)) :=
  dedupPySpecDecls items (·.name)

private def keptNames (items : Array (Laurel.Field × String)) (expected : List String) : Bool :=
  match dedupFields items with
  | .ok kept => kept.toList.map (fun (f, _) => f.name.text) == expected
  | .error _ => false

private def collidesAs (items : Array (Laurel.Field × String))
    (name prevFile srcFile : String) : Bool :=
  match dedupFields items with
  | .error (ident, p, s) => ident.text == name && p == prevFile && s == srcFile
  | .ok _ => false

-- Distinct names across files are all kept, in order.
#guard keptNames #[(mkField "g", "a.ion"), (mkField "h", "b.ion")] ["g", "h"]

-- Singleton boundary: a single field passes through unchanged.
#guard keptNames #[(mkField "solo", "x.ion")] ["solo"]

-- A same-name static field in a second file reports (name, first file, colliding file).
#guard collidesAs #[(mkField "g", "a.ion"), (mkField "g", "b.ion")] "g" "a.ion" "b.ion"

-- A distinct first item does not mask a later collision, reported for the right pair.
#guard collidesAs #[(mkField "a", "x.ion"), (mkField "b", "y.ion"), (mkField "b", "z.ion")]
  "b" "y.ion" "z.ion"

-- Collision detection is cross-file by NAME, so it also fires within one file.
#guard collidesAs #[(mkField "g", "a.ion"), (mkField "g", "a.ion")] "g" "a.ion" "a.ion"

-- Empty input stays empty.
#guard keptNames #[] []

end StrataPython.PySpecDedupTest

end -- meta section
