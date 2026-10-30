/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.DDMRead
public import StrataDynTest.RegionTest
import StrataDyn.Env.WF
-- The builder, the reader and the printer run as compiled code below.
meta import StrataDyn.Build
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF
meta import StrataDynTest.RegionTest

set_option autoImplicit false

/-!
# Function attributes

A function given attributes after it is built prints them below its signature.  A module whose functions
carry every form of attribute value reads back with them, and both printed forms show the same
attribute lines; a function without attributes prints none.  Then the mistakes the reader rejects, and a key
that is a keyword, which does not read back.
-/

namespace Strata.Dyn.AttrTest

open Strata.Dyn.RegionTest

private def key (s : String) : Name := (Name.base.str "t").str s

/-- `@m.f`, returning `0`, given the attributes `attrs` after it is built. -/
private def built (attrs : Array Attr) : String :=
  match Build.build (env := Reg.env) (.str (.str .base "m") "f") Base.Int ({} : Info) do
    let _ ← Build.startFreshBlock #[] "entry"
    let c ← Build.emitConst (.str .base "c") (.int 0)
    Build.finishBlock (.ret {} c) with
  | .ok fn => Func.format .full (Func.setInfo fn { attrs }).val
  | .error e => toString e

/-- info: module m.f {
  func @m.f() -> base.Int {
    #[t.kind = "point"]
    #[t.fields = [{name = "x", type = "int"}, {name = "y", type = "int"}]]

    entry.0():
      %c.0 : base.Int = const 0
      ret(%c.0)
  }
}
-/
#guard_msgs in
#eval IO.print (built #[(key "kind", .const (.str "point")),
  (key "fields", .list #[
    .record #[(.str .base "name", .const (.str "x")), (.str .base "type", .const (.str "int"))],
    .record #[(.str .base "name", .const (.str "y")), (.str .base "type", .const (.str "int"))]])])

/-- Read `text` in `Reg.env`, print each function's attributes as read, then the module in
full and folded; or the diagnostics. -/
private def roundTrip (text : String) : IO Unit := do
  match ← Module.read Reg.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    for f in m.raw.funcs do
      IO.println s!"{ToDDM.nameText f.name}: {repr f.info.attrs}"
    IO.print (m.format .full)
    IO.print (toString m)

/-- Every literal form, a function reference, nested lists and records, and empty ones; and a
function without attributes. -/
private def every : String := "module m {
  func @m.f() -> base.Int {
    #[t.lits = [unit, true, -3, 2.5, \"s\", @m.g]]
    #[t.nested = {a = [[], {}], b = {c = [1, {d = false}]}}]

    entry.0():
      ret(1)
  }
  func @m.g() -> base.Int {
    entry.0():
      ret(2)
  }
}
"

/-- info: m.f: #[(Strata.Dyn.Name.str (Strata.Dyn.Name.str (Strata.Dyn.Name.base) "t") "lits",
   Strata.Dyn.AttrValue.list
     #[Strata.Dyn.AttrValue.const (Strata.Dyn.Const.unit), Strata.Dyn.AttrValue.const (Strata.Dyn.Const.bool true),
       Strata.Dyn.AttrValue.const (Strata.Dyn.Const.int (-3)),
       Strata.Dyn.AttrValue.const (Strata.Dyn.Const.float 2.500000),
       Strata.Dyn.AttrValue.const (Strata.Dyn.Const.str "s"),
       Strata.Dyn.AttrValue.const
         (Strata.Dyn.Const.func (Strata.Dyn.Name.str (Strata.Dyn.Name.str (Strata.Dyn.Name.base) "m") "g"))]),
  (Strata.Dyn.Name.str (Strata.Dyn.Name.str (Strata.Dyn.Name.base) "t") "nested",
   Strata.Dyn.AttrValue.record
     #[(Strata.Dyn.Name.str (Strata.Dyn.Name.base) "a",
        Strata.Dyn.AttrValue.list #[Strata.Dyn.AttrValue.list #[], Strata.Dyn.AttrValue.record #[]]),
       (Strata.Dyn.Name.str (Strata.Dyn.Name.base) "b",
        Strata.Dyn.AttrValue.record
          #[(Strata.Dyn.Name.str (Strata.Dyn.Name.base) "c",
             Strata.Dyn.AttrValue.list
               #[Strata.Dyn.AttrValue.const (Strata.Dyn.Const.int 1),
                 Strata.Dyn.AttrValue.record
                   #[(Strata.Dyn.Name.str (Strata.Dyn.Name.base) "d",
                      Strata.Dyn.AttrValue.const (Strata.Dyn.Const.bool false))]])])])]
m.g: #[]
module m {
  func @m.f() -> base.Int {
    #[t.lits = [unit, true, -3, 2.5, "s", @m.g]]
    #[t.nested = {a = [[], {}], b = {c = [1, {d = false}]}}]

    entry.0():
      %c.0 : base.Int = const 1
      ret(%c.0)
  }
  func @m.g() -> base.Int {
    entry.0():
      %c.0 : base.Int = const 2
      ret(%c.0)
  }
}
module m {
  func @m.f() -> base.Int {
    #[t.lits = [unit, true, -3, 2.5, "s", @m.g]]
    #[t.nested = {a = [[], {}], b = {c = [1, {d = false}]}}]

    entry.0():
      ret(1)
  }
  func @m.g() -> base.Int {
    entry.0():
      ret(2)
  }
}
-/
#guard_msgs in
#eval roundTrip every

/-! ## What reads back

Each attribute text that the reader rejects stands beside an accepted twin that differs only
in the rejected part. -/

/-- `@m.f` with the attribute lines `attrs`. -/
private def withAttrs (attrs : String) : String :=
  s!"module m \{\n  func @m.f() -> base.Int \{\n{attrs}\n\n    entry.0():\n      ret(1)\n  }\n}\n"

/-- Read `@m.f` with the attribute lines `attrs`, and print its attribute lines as printed
back, or the diagnostic. -/
private def readAttrs (attrs : String) : IO Unit := do
  match ← Module.read Reg.env (withAttrs attrs) "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    for l in (toString m).splitOn "\n" do
      let l := l.trimAsciiStart.toString
      if l.startsWith "#[" then IO.println l

-- A function reference names a function of the module.
/-- info: #[t.ref = @m.f] -/
#guard_msgs in
#eval readAttrs "    #[t.ref = @m.f]"

/-- info: t.dyn:3:14: no function @m.h in this module -/
#guard_msgs in
#eval readAttrs "    #[t.ref = @m.h]"

-- The keys of a function's attributes are distinct.
/--
info: #[t.a = 1]
#[t.b = 2]
-/
#guard_msgs in
#eval readAttrs "    #[t.a = 1]\n    #[t.b = 2]"

/-- info: t.dyn:4:4: attribute t.a is given twice -/
#guard_msgs in
#eval readAttrs "    #[t.a = 1]\n    #[t.a = 2]"

-- The fields of a record are distinct.
/-- info: #[t.a = {x = 1, y = 2}] -/
#guard_msgs in
#eval readAttrs "    #[t.a = {x = 1, y = 2}]"

/-- info: t.dyn:3:20: field x is given twice -/
#guard_msgs in
#eval readAttrs "    #[t.a = {x = 1, x = 2}]"

-- A key that is a keyword of the dialect does not read back; a source name belongs in a
-- string value.
/-- info: #[t.a = {units = 1}] -/
#guard_msgs in
#eval readAttrs "    #[t.a = {units = 1}]"

/-- info: t.dyn:3:13: unexpected token 'unit'; expected '}' -/
#guard_msgs in
#eval readAttrs "    #[t.a = {unit = 1}]"

end Strata.Dyn.AttrTest
