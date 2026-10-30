/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Unicode
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Unicode

set_option autoImplicit false

/-!
# Unicode properties
-/

namespace StrataPython.Dyn.Sem.UnicodeTest

open StrataPython.Dyn.Sem.Unicode

-- The ASCII shortcut agrees with the table.
#guard (List.range 128).all fun cp => (0x20 ≤ cp && cp < 0x7f) == inPrintableRanges cp

-- Code points with CPython 3.12.15's str.isprintable().
#guard isPrintable (Char.ofNat 0x0) == false
#guard isPrintable (Char.ofNat 0x9) == false
#guard isPrintable (Char.ofNat 0x20) == true
#guard isPrintable (Char.ofNat 0x7e) == true
#guard isPrintable (Char.ofNat 0x7f) == false
#guard isPrintable (Char.ofNat 0x80) == false
#guard isPrintable (Char.ofNat 0xa0) == false
#guard isPrintable (Char.ofNat 0xad) == false
#guard isPrintable (Char.ofNat 0x300) == true
#guard isPrintable (Char.ofNat 0x378) == false
#guard isPrintable (Char.ofNat 0x2028) == false
#guard isPrintable (Char.ofNat 0x3000) == false
#guard isPrintable (Char.ofNat 0xe000) == false
#guard isPrintable (Char.ofNat 0xfeff) == false
#guard isPrintable (Char.ofNat 0xffff) == false
#guard isPrintable (Char.ofNat 0x1f600) == true
#guard isPrintable (Char.ofNat 0xe0001) == false
#guard isPrintable (Char.ofNat 0x10ffff) == false
#guard isPrintable (Char.ofNat 0x79d67) == false
#guard isPrintable (Char.ofNat 0x42c6c) == false
#guard isPrintable (Char.ofNat 0xbd6ac) == false
#guard isPrintable (Char.ofNat 0xf2b72) == false
#guard isPrintable (Char.ofNat 0x218cf) == true
#guard isPrintable (Char.ofNat 0x6bdf) == true
#guard isPrintable (Char.ofNat 0xf03f3) == false
#guard isPrintable (Char.ofNat 0x84ca0) == false
#guard isPrintable (Char.ofNat 0x77fa3) == false
#guard isPrintable (Char.ofNat 0x622c4) == false
#guard isPrintable (Char.ofNat 0xf0c66) == false
#guard isPrintable (Char.ofNat 0xf3e49) == false
#guard isPrintable (Char.ofNat 0xcb553) == false
#guard isPrintable (Char.ofNat 0x4d1d9) == false
#guard isPrintable (Char.ofNat 0x76be7) == false
#guard isPrintable (Char.ofNat 0x4da17) == false
#guard isPrintable (Char.ofNat 0x10bde6) == false
#guard isPrintable (Char.ofNat 0xc7a5c) == false
#guard isPrintable (Char.ofNat 0x7c15) == true
#guard isPrintable (Char.ofNat 0x20c8b) == true
#guard isPrintable (Char.ofNat 0x519cd) == false
#guard isPrintable (Char.ofNat 0x15e87) == false
#guard isPrintable (Char.ofNat 0x9a3fc) == false
#guard isPrintable (Char.ofNat 0xfe0c) == true
#guard isPrintable (Char.ofNat 0x89f2f) == false
#guard isPrintable (Char.ofNat 0xf20c2) == false
#guard isPrintable (Char.ofNat 0xc674a) == false
#guard isPrintable (Char.ofNat 0xda973) == false
#guard isPrintable (Char.ofNat 0xca38a) == false
#guard isPrintable (Char.ofNat 0xe3a55) == false
#guard isPrintable (Char.ofNat 0x44af3) == false
#guard isPrintable (Char.ofNat 0xbb256) == false
#guard isPrintable (Char.ofNat 0x31e58) == true
#guard isPrintable (Char.ofNat 0x125fb) == false
#guard isPrintable (Char.ofNat 0x459db) == false
#guard isPrintable (Char.ofNat 0xfd615) == false
#guard isPrintable (Char.ofNat 0x6f18e) == false
#guard isPrintable (Char.ofNat 0x84161) == false
#guard isPrintable (Char.ofNat 0xdf509) == false
#guard isPrintable (Char.ofNat 0x9a201) == false
#guard isPrintable (Char.ofNat 0xd7a0c) == false
#guard isPrintable (Char.ofNat 0x103b55) == false
#guard isPrintable (Char.ofNat 0xc5904) == false
#guard isPrintable (Char.ofNat 0xb3aa8) == false
#guard isPrintable (Char.ofNat 0xd0adc) == false
#guard isPrintable (Char.ofNat 0x76fb5) == false
#guard isPrintable (Char.ofNat 0xac6c7) == false
#guard isPrintable (Char.ofNat 0xeac9) == false
#guard isPrintable (Char.ofNat 0x8f32f) == false
#guard isPrintable (Char.ofNat 0x5381c) == false
#guard isPrintable (Char.ofNat 0xa71ca) == false
#guard isPrintable (Char.ofNat 0x35496) == false
#guard isPrintable (Char.ofNat 0x6c189) == false
#guard isPrintable (Char.ofNat 0x88bf5) == false
#guard isPrintable (Char.ofNat 0x91e5f) == false
#guard isPrintable (Char.ofNat 0x3fb5e) == false
#guard isPrintable (Char.ofNat 0x207de) == true
#guard isPrintable (Char.ofNat 0xf6c8e) == false
#guard isPrintable (Char.ofNat 0xf78e7) == false
#guard isPrintable (Char.ofNat 0x2d523) == true

end StrataPython.Dyn.Sem.UnicodeTest
