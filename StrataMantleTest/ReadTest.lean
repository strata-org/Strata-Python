/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DDMRead
public import StrataMantle.FloatText
public import StrataMantleTest.RegionTest
import StrataMantle.Env.WF
-- The reader and the printer run as compiled code below.
meta import StrataMantle.DDMRead
meta import StrataMantle.Env.WF
meta import StrataMantleTest.RegionTest
-- `decide +kernel` unfolds the float conversions.
import all StrataMantle.FloatText

set_option autoImplicit false

/-!
# Reading printed modules back

A module with every literal form, a region, a function reference and constants passed to
successors is read in full and folded, and printed again both ways.  Then names that need
quoting, the diagnostics, one mistake each, and the float conversions both ways.
-/

namespace Strata.Mantle.ReadTest

open Strata.Mantle.RegionTest

/-- Read `text` in `Reg.env`, and print the module in full and folded, or the diagnostics. -/
private def roundTrip (text : String) : IO Unit := do
  match ← Module.read Reg.env text "t.mantle" with
  | .error e => IO.println e
  | .ok m =>
    IO.println (m.format .full)
    IO.println (toString m)

/-! ## Both forms -/

/-- The folded form reads back with a fresh `const` before each use, named `%c.0`, `%c.1`, …
in each function. -/
private def folded : String := "module m {
  func @m.counter(%v.0 : base.Bool) -> base.Int {
    entry.0(%v.0 : base.Bool):
      %v.2 : base.Bool = const true
      %v.3 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %v.4 : base.Unit = base.refSet[base.Int](%v.3, 0)
      branch(%v.0) ^done.0(-1) ^done.0(0)
    done.0(%v.6 : base.Int):
      %v.7 : base.Int = base.refGet[base.Int](%v.3)
      ret(%v.7)
  }
  func @|m.<code>|() -> base.Code {
    entry.0():
      ret(@m.counter)
  }
  func @m.pick(%v.0 : base.Bool) -> base.Int {
    entry.0(%v.0 : base.Bool):
      %v.3 : base.Int = reg.if[base.Int](%v.0) {
        then.0():
          ret(1)
      } {
        else.0():
          %v.9 : base.Float64 = const -2.5e-3
          ret(2)
      }
      ret(%v.3)
  }
}
"

/-- info: module m {
  func @m.counter(%v.0 : base.Bool) -> base.Int {
    entry.0(%v.0 : base.Bool):
      %v.2 : base.Bool = const true
      %c.0 : base.Int = const 0
      %v.3 : base.Ref(base.Int) = base.refNew[base.Int](%c.0)
      %c.1 : base.Int = const 0
      %v.4 : base.Unit = base.refSet[base.Int](%v.3, %c.1)
      %c.2 : base.Int = const -1
      %c.3 : base.Int = const 0
      branch(%v.0) ^done.0(%c.2) ^done.0(%c.3)
    done.0(%v.6 : base.Int):
      %v.7 : base.Int = base.refGet[base.Int](%v.3)
      ret(%v.7)
  }
  func @|m.<code>|() -> base.Code {
    entry.0():
      %c.0 : base.Code = const @m.counter
      ret(%c.0)
  }
  func @m.pick(%v.0 : base.Bool) -> base.Int {
    entry.0(%v.0 : base.Bool):
      %v.3 : base.Int = reg.if[base.Int](%v.0) {
        then.0():
          %c.0 : base.Int = const 1
          ret(%c.0)
      } {
        else.0():
          %v.9 : base.Float64 = const -0.0025
          %c.1 : base.Int = const 2
          ret(%c.1)
      }
      ret(%v.3)
  }
}

module m {
  func @m.counter(%v.0 : base.Bool) -> base.Int {
    entry.0(%v.0 : base.Bool):
      %v.2 : base.Bool = const true
      %v.3 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %v.4 : base.Unit = base.refSet[base.Int](%v.3, 0)
      branch(%v.0) ^done.0(-1) ^done.0(0)
    done.0(%v.6 : base.Int):
      %v.7 : base.Int = base.refGet[base.Int](%v.3)
      ret(%v.7)
  }
  func @|m.<code>|() -> base.Code {
    entry.0():
      ret(@m.counter)
  }
  func @m.pick(%v.0 : base.Bool) -> base.Int {
    entry.0(%v.0 : base.Bool):
      %v.3 : base.Int = reg.if[base.Int](%v.0) {
        then.0():
          ret(1)
      } {
        else.0():
          %v.9 : base.Float64 = const -0.0025
          ret(2)
      }
      ret(%v.3)
  }
} -/
#guard_msgs in
#eval roundTrip folded

/-! ## Names that need quoting

A function named `f`, as printed, returns a pointer to itself, so its name is read both where
it is defined and as an operand.  Each test prints the segments read, then the module
printed again. -/

/-- A name's segments, root first. -/
private def segments : Name → List String
  | .base => []
  | .str n s => segments n ++ [s.quote]
  | .num n i => segments n ++ [toString i]

/-- Read a module whose one function is `@f`, and print its name's segments and the module. -/
private def nameTrip (f : String) : IO Unit := do
  let text := s!"module m \{\n  func @{f}() -> base.Code \{\n    entry.0():\n      ret(@{f})\n  }\n}\n"
  match ← Module.read Reg.env text "t.mantle" with
  | .error e => IO.println e
  | .ok m =>
    IO.println (m.raw.funcs.map fun fn => segments fn.name).toList
    IO.print (toString m)

/-- info: [["m", "café"]]
module m {
  func @|m.café|() -> base.Code {
    entry.0():
      ret(@|m.café|)
  }
}
-/
#guard_msgs in
#eval nameTrip "|m.café|"

/-- info: [["m", "f", "<lambda>"]]
module m {
  func @|m.f.<lambda>|() -> base.Code {
    entry.0():
      ret(@|m.f.<lambda>|)
  }
}
-/
#guard_msgs in
#eval nameTrip "|m.f.<lambda>|"

-- The quote character is escaped inside the quotes.
/-- info: [["m", "a|b"]]
module m {
  func @|m.a\|b|() -> base.Code {
    entry.0():
      ret(@|m.a\|b|)
  }
}
-/
#guard_msgs in
#eval nameTrip "|m.a\\|b|"

-- `_` is the root only alone; after `m.` it is a string segment.
/-- info: [["m", "_"]]
module m {
  func @m._() -> base.Code {
    entry.0():
      ret(@m._)
  }
}
-/
#guard_msgs in
#eval nameTrip "m._"

-- The reader splits at every `.`, quoted or not, so no name it reads has a `.` in a segment.
/-- info: [["m", "a", "b"]]
module m {
  func @m.a.b() -> base.Code {
    entry.0():
      ret(@m.a.b)
  }
}
-/
#guard_msgs in
#eval nameTrip "|m.a.b|"

/-! ## Value names

A value is named in the text, and gets its id where it is defined, so the function read is
canonical.  A name may be quoted and may be used before its definition.  A folded constant is
named `c.k`, skipping names the text uses: here `%c.0`. -/

/-- A function `@m.f` of signature `() -> base.Int` whose entry block runs `body`. -/
private def withBody' (body : String) : String :=
  s!"module m \{\n  func @m.f() -> base.Int \{\n    entry.0():\n{body}\n  }\n}\n"

/-- Read `text`, say for each function whether it is canonical and what its values are
named, and print the module in full. -/
private def namesTrip (text : String) : IO Unit := do
  match ← Module.read Reg.env text "t.mantle" with
  | .error e => IO.println e
  | .ok m =>
    for f in m.raw.funcs do
      IO.println s!"{ToDDM.nameText f.name}: canonical {decide f.Canonical}, \
        {f.names.toList.map ToDDM.valNameText}"
    IO.print (m.format .full)

/-- info: m.f: canonical true, [%c.0, %x, %r.0, %café.0, %c.1, %y.0]
module m {
  func @m.f(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      branch(%c.0) ^a.0() ^b.0()
    b.0():
      ret(%|café.0|)
    a.0():
      %x : base.Int = const 1
      %r.0 : base.Ref(base.Int) = base.refNew[base.Int](%x)
      %|café.0| : base.Int = base.refGet[base.Int](%r.0)
      %c.1 : base.Int = const 2
      %y.0 : base.Unit = base.refSet[base.Int](%r.0, %c.1)
      ret(%|café.0|)
  }
} -/
#guard_msgs in
#eval namesTrip "module m {
  func @m.f(%c.0 : base.Bool) -> base.Int {
    entry.0(%c.0 : base.Bool):
      branch(%c.0) ^a.0() ^b.0()
    b.0():
      ret(%|café.0|)
    a.0():
      %x : base.Int = const 1
      %r.0 : base.Ref(base.Int) = base.refNew[base.Int](%x)
      %|café.0| : base.Int = base.refGet[base.Int](%r.0)
      %y.0 : base.Unit = base.refSet[base.Int](%r.0, 2)
      ret(%|café.0|)
  }
}
"

/-- info: t.mantle:5:6: %x.0 is defined twice -/
#guard_msgs in
#eval roundTrip (withBody' "      %x.0 : base.Int = const 1\n      %x.0 : base.Int = const 2\n      ret(%x.0)")

/-- info: t.mantle:4:10: %y.0 is not defined -/
#guard_msgs in
#eval roundTrip (withBody' "      ret(%y.0)")

-- A one-segment name that is a keyword does not parse, nor does a bare number.
/-- info: t.mantle:4:7: unexpected token 'ret'; expected Mantle.MName -/
#guard_msgs in
#eval roundTrip (withBody' "      %ret : base.Int = const 1\n      ret(%ret)")

/-- info: t.mantle:4:7: unexpected token; expected Mantle.MName -/
#guard_msgs in
#eval roundTrip (withBody' "      %3 : base.Int = const 1\n      ret(%3)")

/-! ## Literals

Every literal form, in full.  A float is read as the nearest binary64 value and printed as the
shortest decimal that reads back as it, so `0.1000` prints as `0.1`, and `1e400` overflows to
`inf`. -/

/-- info: module lits {
  func @lits.f() -> base.Unit {
    entry.0():
      %v.0 : base.Unit = const unit
      %v.1 : base.Bool = const false
      %v.2 : base.Int = const -12345678901234567890
      %v.3 : base.Float64 = const 0.1
      %v.4 : base.Float64 = const -0.0
      %v.5 : base.Float64 = const 1e22
      %v.6 : base.Float64 = const 5e-324
      %v.7 : base.Float64 = const inf
      %v.8 : base.Float64 = const -inf
      %v.9 : base.Float64 = const nan
      %v.10 : base.String = const "tab\tquote\"é"
      ret(%v.0)
  }
}

module lits {
  func @lits.f() -> base.Unit {
    entry.0():
      %v.1 : base.Bool = const false
      %v.2 : base.Int = const -12345678901234567890
      %v.3 : base.Float64 = const 0.1
      %v.4 : base.Float64 = const -0.0
      %v.5 : base.Float64 = const 1e22
      %v.6 : base.Float64 = const 5e-324
      %v.7 : base.Float64 = const inf
      %v.8 : base.Float64 = const -inf
      %v.9 : base.Float64 = const nan
      %v.10 : base.String = const "tab\tquote\"é"
      ret(unit)
  }
}
-/
#guard_msgs in
#eval roundTrip "module lits {
  func @lits.f() -> base.Unit {
    entry.0():
      %v.0 : base.Unit = const unit
      %v.1 : base.Bool = const false
      %v.2 : base.Int = const -12345678901234567890
      %v.3 : base.Float64 = const 0.1000
      %v.4 : base.Float64 = const -0.0
      %v.5 : base.Float64 = const 1e22
      %v.6 : base.Float64 = const 4.9406564584124654e-324
      %v.7 : base.Float64 = const 1e400
      %v.8 : base.Float64 = const -inf
      %v.9 : base.Float64 = const nan
      %v.10 : base.String = const \"tab\\tquote\\\"é\"
      ret(%v.0)
  }
}
"

/-! ## Large numbers in names

Ids are dense and assigned by the reader, so a large number in a name costs nothing per number
below it: reading allocates nothing by a number taken from the text. -/

/-- info: module m {
  func @m.f() -> base.Int {
    entry.0():
      jump ^b.100000000000()
    b.100000000000():
      %x.100000000000 : base.Int = const 1
      ret(%x.100000000000)
  }
}

module m {
  func @m.f() -> base.Int {
    entry.0():
      jump ^b.100000000000()
    b.100000000000():
      ret(1)
  }
}
-/
#guard_msgs in
#eval roundTrip "module m {
  func @m.f() -> base.Int {
    entry.0():
      jump ^b.100000000000()
    b.100000000000():
      %x.100000000000 : base.Int = const 1
      ret(%x.100000000000)
  }
}
"

/-! ## Diagnostics

Each names the mistake and where it is, as `file:line:column`. -/

/-- A function `@m.f` of signature `() -> base.Int` whose entry block runs `body`. -/
private def withBody (body : String) : String :=
  s!"module m \{\n  func @m.f() -> base.Int \{\n    entry.0():\n{body}\n  }\n}\n"

/-- info: t.mantle:4:13: unknown type base.Nat -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Nat = const 1\n      ret(%v.1)")

/-- info: t.mantle:4:6: unknown operation base.refNow -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Int = base.refNow(1)\n      ret(%v.1)")

/-- info: t.mantle:4:6: base.refNew takes 1 type argument(s), given 0 -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Ref(base.Int) = base.refNew(1)\n      ret(0)")

/-- info: t.mantle:4:6: base.refNew takes 1 operand(s), given 2 -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Ref(base.Int) = base.refNew[base.Int](1, 2)\n      ret(0)")

/-- info: t.mantle:4:56: a base.String literal where base.Int is expected -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Ref(base.Int) = base.refNew[base.Int](\"one\")\n      ret(0)")

/-- info: t.mantle:5:6: base.refGet returns base.Int, but %v.2 is declared base.Bool -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Ref(base.Int) = base.refNew[base.Int](1)
      %v.2 : base.Bool = base.refGet[base.Int](%v.1)\n      ret(0)")

/-- info: t.mantle:5:48: %v.1 has type base.Ref(base.Int), but base.refGet, operand 1 takes base.Ref(base.Bool) -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Ref(base.Int) = base.refNew[base.Int](1)
      %v.2 : base.Bool = base.refGet[base.Bool](%v.1)\n      ret(0)")

/-- info: t.mantle:4:10: %v.7 is not defined -/
#guard_msgs in
#eval roundTrip (withBody "      ret(%v.7)")

/-- info: t.mantle:5:6: %v.1 is defined twice -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Int = const 1\n      %v.1 : base.Int = const 2\n      ret(%v.1)")

/-- info: t.mantle:4:11: no block nowhere.0 to transfer to here -/
#guard_msgs in
#eval roundTrip (withBody "      jump ^nowhere.0()")

/-- info: t.mantle:4:11: block done.0 takes 1 argument(s), given 0 here and 0 by base.jump -/
#guard_msgs in
#eval roundTrip (withBody "      jump ^done.0()\n    done.0(%v.1 : base.Int):\n      ret(%v.1)")

/-- info: t.mantle:4:6: base.refGet returns a value, so it cannot end a block -/
#guard_msgs in
#eval roundTrip (withBody "      base.refGet[base.Int](0)")

/-- info: t.mantle:4:6: base.branch ends a block, so it defines no value -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Int = branch(true) ^a.0() ^b.0()\n      ret(0)")

/-- info: t.mantle:4:6: reg.if takes 2 region(s), given 1 -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Int = reg.if[base.Int](true) {
        then.0():
          ret(1)
      }\n      ret(%v.1)")

/-- info: t.mantle:4:10: no function @m.g in this module -/
#guard_msgs in
#eval roundTrip (withBody "      ret(@m.g)")

/-- info: t.mantle:4:10: a base.Code literal where base.Int is expected -/
#guard_msgs in
#eval roundTrip (withBody "      ret(@m.f)")

/-- info: t.mantle:4:10: a base.Int literal where base.Unit is expected -/
#guard_msgs in
#eval roundTrip "module m {\n  func @m.f() -> base.Unit {\n    entry.0():\n      ret(5)\n  }\n}\n"

/-! A literal's form fixes its type, and nothing widens: an integer is not a float, nor a
float an integer. -/

/-- info: t.mantle:4:34: a base.Int literal where base.Float64 is expected -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Float64 = const 1\n      ret(0)")

/-- info: t.mantle:4:10: a base.Float64 literal where base.Int is expected -/
#guard_msgs in
#eval roundTrip (withBody "      ret(1.0)")

/-- info: t.mantle:5:4: block entry.0 is defined twice -/
#guard_msgs in
#eval roundTrip (withBody "      jump ^entry.0()\n    entry.0():\n      ret(0)")

/-- info: t.mantle:6:2: function @m.f is defined twice -/
#guard_msgs in
#eval roundTrip "module m {
  func @m.f() -> base.Int {\n    entry.0():\n      ret(0)\n  }
  func @m.f() -> base.Int {\n    entry.0():\n      ret(0)\n  }\n}\n"

/-- info: t.mantle:2:2: the parameters of @m.f differ from its entry block's -/
#guard_msgs in
#eval roundTrip "module m {
  func @m.f(%v.0 : base.Int) -> base.Int {\n    entry.0(%v.1 : base.Int):\n      ret(%v.1)\n  }\n}\n"

/-- info: t.mantle:4:40: unexpected token 'ret'; expected ':' -/
#guard_msgs in
#eval roundTrip (withBody "      %v.1 : base.Int = base.refGet %v.0\n      ret(%v.1)")

-- One-letter names keep each message at the column it had with `%1`.
/-- info: t.mantle:4:6: base.Int is a type, not an operation -/
#guard_msgs in
#eval roundTrip (withBody "      %a : base.Int = base.Int(1)\n      ret(%a)")

/-- info: t.mantle:4:11: base.refGet is an operation, not a type -/
#guard_msgs in
#eval roundTrip (withBody "      %a : base.refGet = const 1\n      ret(0)")

/-- info: t.mantle:4:11: type variable #0 outside a signature -/
#guard_msgs in
#eval roundTrip (withBody "      %a : #0 = const 1\n      ret(0)")

/-- info: t.mantle:2:2: a body needs an entry block -/
#guard_msgs in
#eval roundTrip "module m {\n  func @m.f() -> base.Int {\n  }\n}\n"

/-- info: t.mantle:4:45: the region's entry block takes (base.Int), but () is expected -/
#guard_msgs in
#eval roundTrip (withBody "      %a : base.Int = reg.if[base.Int](true) {
        then.0(%b : base.Int):
          ret(%b)
      } {
        else.0():
          ret(1)
      }\n      ret(%a)")

/-- info: t.mantle:4:6: base.branch takes 2 successor(s), given 1 -/
#guard_msgs in
#eval roundTrip (withBody "      branch(true) ^a.0()\n    a.0():\n      ret(1)")

/-- info: t.mantle:4:6: ret takes 1 operand(s), given 0 -/
#guard_msgs in
#eval roundTrip (withBody "      ret")

-- `_` is the exit, so a block of that name is reported at its header, not at the `ret`.
/-- info: t.mantle:5:4: no block may be named _ -/
#guard_msgs in
#eval roundTrip (withBody "      ret(0)\n    _():\n      ret(0)")

-- A repeated label is reported at the second header, not at the jump to it.
/-- info: t.mantle:7:4: block a.0 is defined twice -/
#guard_msgs in
#eval roundTrip (withBody "      jump ^a.0(1)
    a.0(%a : base.Int):
      ret(%a)
    a.0():
      ret(2)")

/-- info: t.mantle: expected one module, found 2 -/
#guard_msgs in
#eval roundTrip "module a {\n}\nmodule b {\n}\n"

/-! ## Floats, in the kernel -/

/-- `0.1` reads as the binary64 value nearest it. -/
example : FloatText.magnitudeBits 1 (-1) = 0x3FB999999999999A := by decide +kernel

/-- A tie rounds to even: `2 ^ 53 + 1` reads as `2 ^ 53`. -/
example : FloatText.magnitudeBits 9007199254740993 0 = 0x4340000000000000 := by decide +kernel

/-- The largest finite value, and the smallest subnormal; past them, an infinity and zero. -/
example : FloatText.magnitudeBits 17976931348623157 292 = 0x7FEFFFFFFFFFFFFF ∧
    FloatText.magnitudeBits 5 (-324) = 1 ∧
    FloatText.magnitudeBits 18 307 = 0x7FF0000000000000 ∧
    FloatText.magnitudeBits 2 (-324) = 0 := by decide +kernel

/-- A long mantissa: `10 ^ 1000 * 10 ^ -1000` is one, and out of range an infinity and zero. -/
example : FloatText.magnitudeBits (10 ^ 1000) (-1000) = 0x3FF0000000000000 ∧
    FloatText.magnitudeBits (10 ^ 1000) (-690) = 0x7FF0000000000000 ∧
    FloatText.magnitudeBits (10 ^ 1000) (-1400) = 0 := by decide +kernel

end Strata.Mantle.ReadTest
