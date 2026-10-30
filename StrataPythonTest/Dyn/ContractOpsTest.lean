/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Env
public import StrataDyn.ContractRegion
public import StrataDyn.DDM
public import StrataDyn.DDMRead
import StrataDyn.Env.WF
-- The reader, the checker and the printer run as compiled code below.
meta import StrataPython.Dyn.Env
meta import StrataDyn.ContractRegion
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The Python operations that contracts use

`Py.env` declares operations for the contracts of Python functions: the arguments that a call
binds to a parameter (`argOf`, `extraKwargs`, `bindsTo`), predicates (`stdClass`, `isInstance`,
`typeIsSubclass`, `len`, `reSearch`, `strIsOneOf`, `intIsOneOf`, `isImmutableScalar`,
`dictKeysWithin`), bounded
quantifiers (`allIn`, `anyIn`, `allItems`, `anyItems`), and locations for frames (`attrLoc`,
`itemLoc`, `objLoc`, `reachLoc`, `instanceState`).  `PyEffectTest` pins their effects.  The tests:

* which operations are total (no `err` successor), and that each quantifier's region may pass a
  failure on (`InsnSig.mayPropagate`);
* an extern whose clauses and frame use every new operation, which the reader checks and which
  prints back unchanged;
* contracts that the checker rejects: a `writes` operation in a clause and in a quantifier's body,
  a quantifier's body that turns a failure into `true`, and a variadic operand of the wrong type.
-/

namespace StrataPython.Dyn.ContractOpsTest

open Strata.Dyn

private abbrev E := Py.env

/-- Read `text` in `Py.env`, and print the diagnostics, or the module if it prints otherwise. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-! ## Failures

A total operation declares no successor.  Every other new operation declares one `err` successor,
and each quantifier's region may pass a failure on to it, so a failure in the body reaches the
clause's failure value. -/

#guard [(Py.argOf.sig (e := E)).succs.size, (Py.extraKwargs.sig (e := E)).succs.size,
  (Py.bindsTo.sig (e := E)).succs.size, (Py.stdClass.sig (e := E)).succs.size,
  (Py.strIsOneOf.sig (e := E)).succs.size, (Py.intIsOneOf.sig (e := E)).succs.size,
  (Py.isImmutableScalar.sig (e := E)).succs.size, (Py.dictKeysWithin.sig (e := E)).succs.size,
  (Py.attrLoc.sig (e := E)).succs.size, (Py.itemLoc.sig (e := E)).succs.size,
  (Py.objLoc.sig (e := E)).succs.size, (Py.reachLoc.sig (e := E)).succs.size,
  (Py.instanceState.sig (e := E)).succs.size] == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

#guard [(Py.isInstance.sig (e := E)).succs.map (·.name),
  (Py.typeIsSubclass.sig (e := E)).succs.map (·.name),
  (Py.len.sig (e := E)).succs.map (·.name), (Py.reSearch.sig (e := E)).succs.map (·.name),
  (Py.allIn.sig (e := E)).succs.map (·.name), (Py.anyIn.sig (e := E)).succs.map (·.name),
  (Py.allItems.sig (e := E)).succs.map (·.name), (Py.anyItems.sig (e := E)).succs.map (·.name)] ==
  [#["err"], #["err"], #["err"], #["err"], #["err"], #["err"], #["err"], #["err"]]

#guard [(Py.allIn.sig (e := E)).mayPropagate, (Py.anyIn.sig (e := E)).mayPropagate,
  (Py.allItems.sig (e := E)).mayPropagate, (Py.anyItems.sig (e := E)).mayPropagate] ==
  [[true], [true], [true], [true]]

/-! ## A model that uses every new operation

`f(x, *, mode=None, **kw) -> int`: its `requires` clauses check the binding, `x`'s presence and
type, `mode`'s values, the closed keywords, `len(x)`, and quantifiers over `x` and `kw`.  Its
`free ensures` clauses read `x` with `base.old`, test the type of the result, and compare the
result with `len(x)` at the call, which the `old` region gives only if it is an immutable scalar,
and otherwise fails.  Its frame names the attributes of instances, an attribute and every location
of `x`, an entry of the dict of keyword arguments, and every location that `x` reaches. -/

private def model : String := "module m {
  extern func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value)
    requires \"arguments bind to 'f'\" {
      pre.0():
        %ok.0 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 1, true, \"x\", \"mode\")
        ret(%ok.0)
    }
    requires \"'x' is required\" {
      pre.1():
        %undef.0 : py.Value = py.undef(\"x\")
        %x.0 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.0)
        %ok.1 : base.Bool = py.isDefined(%x.0)
        ret(%ok.1)
    }
    requires \"declared type of parameter 'x'\" {
      pre.2():
        %undef.1 : py.Value = py.undef(\"x\")
        %x.1 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.1)
        %cls.0 : py.Value = py.stdClass(\"builtins\", \"list\")
        %sub.0 : base.Bool = py.typeIsSubclass(%x.1, %cls.0) ^fail.0()
        branch(%sub.0) ^isSub.0() ^notSub.0()
      isSub.0():
        %ok.2 : base.Bool = py.isInstance(%x.1, %cls.0) ^fail.0()
        ret(%ok.2)
      notSub.0():
        ret(false)
      fail.0(%e.0 : py.Value):
        ret(false)
    }
    requires \"declared type of parameter 'mode'\" {
      pre.3():
        %none.0 : py.Value = py.noneLit
        %mode.0 : py.Value = py.argOf(%args.0, %kwargs.0, -1, \"mode\", %none.0)
        %ok.3 : base.Bool = py.strIsOneOf(%mode.0, \"r\", \"w\")
        ret(%ok.3)
    }
    requires \"keywords of 'f'\" {
      pre.4():
        %ok.4 : base.Bool = py.dictKeysWithin(%kwargs.0, \"x\", \"mode\", \"a\")
        ret(%ok.4)
    }
    requires \"len(x) > 0\" {
      pre.5():
        %undef.2 : py.Value = py.undef(\"x\")
        %x.2 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.2)
        %len.0 : py.Value = py.len(%x.2) ^fail.1()
        %int.0 : py.Value = py.intLit(0)
        %gt.0 : py.Value = py.gt(%len.0, %int.0) ^fail.1()
        %ok.5 : base.Bool = py.truthy(%gt.0) ^fail.1()
        ret(%ok.5)
      fail.1(%e.1 : py.Value):
        ret(false)
    }
    requires \"all(re.search('^a+$', s) for s in x)\" {
      pre.6():
        %undef.3 : py.Value = py.undef(\"x\")
        %x.3 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.3)
        %ok.6 : base.Bool = py.allIn(%x.3) ^fail.2() {
          body.0(%item.0 : py.Value):
            %found.0 : base.Bool = py.reSearch(\"^a+$\", %item.0) ^propagate.0()
            %res.0 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](%found.0)
            ret(%res.0)
          propagate.0(%exc.0 : py.Value):
            %err.0 : base.Except(py.Value, base.Bool) = base.error[py.Value, base.Bool](%exc.0)
            ret(%err.0)
        }
        ret(%ok.6)
      fail.2(%e.2 : py.Value):
        ret(false)
    }
    requires \"any(n in (1, -2) for n in x)\" {
      pre.7():
        %undef.4 : py.Value = py.undef(\"x\")
        %x.4 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.4)
        %ok.7 : base.Bool = py.anyIn(%x.4) ^fail.3() {
          body.1(%item.1 : py.Value):
            %found.1 : base.Bool = py.intIsOneOf(%item.1, 1, -2)
            %res.1 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](%found.1)
            ret(%res.1)
        }
        ret(%ok.7)
      fail.3(%e.3 : py.Value):
        ret(false)
    }
    requires \"all(k == 'a' for k, v in kw.items())\" {
      pre.8():
        %kw.0 : py.Value = py.extraKwargs(%kwargs.0, \"x\", \"mode\")
        %ok.8 : base.Bool = py.allItems(%kw.0) ^fail.4() {
          body.2(%k.0 : py.Value, %v.0 : py.Value):
            %found.2 : base.Bool = py.strIsOneOf(%k.0, \"a\")
            %res.2 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](%found.2)
            ret(%res.2)
        }
        ret(%ok.8)
      fail.4(%e.4 : py.Value):
        ret(false)
    }
    requires \"any(v for k, v in kw.items())\" {
      pre.9():
        %kw.1 : py.Value = py.extraKwargs(%kwargs.0, \"x\", \"mode\")
        %ok.9 : base.Bool = py.anyItems(%kw.1) ^fail.5() {
          body.3(%k.1 : py.Value, %v.1 : py.Value):
            %found.3 : base.Bool = py.truthy(%v.1) ^propagate.1()
            %res.3 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](%found.3)
            ret(%res.3)
          propagate.1(%exc.1 : py.Value):
            %err.1 : base.Except(py.Value, base.Bool) = base.error[py.Value, base.Bool](%exc.1)
            ret(%err.1)
        }
        ret(%ok.9)
      fail.5(%e.5 : py.Value):
        ret(false)
    }
    free ensures \"admitted postcondition of 'f'\" {
      post.0(%r.0 : base.Except(py.Value, py.Value)):
        base.Except.case[py.Value, py.Value](%r.0) ^ok.0() ^raised.0()
      ok.0(%val.0 : py.Value):
        %x.5 : py.Value = base.old[py.Value, py.Value] ^fail.6() {
          old.0():
            %undef.5 : py.Value = py.undef(\"x\")
            %x.6 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.5)
            %res.4 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%x.6)
            ret(%res.4)
        }
        %is.0 : py.Value = py.is(%val.0, %x.5)
        %ok.10 : base.Bool = py.truthy(%is.0) ^fail.6()
        ret(%ok.10)
      raised.0(%e.6 : py.Value):
        ret(true)
      fail.6(%e.7 : py.Value):
        ret(true)
    }
    free ensures \"return type of 'f'\" {
      post.1(%r.1 : base.Except(py.Value, py.Value)):
        base.Except.case[py.Value, py.Value](%r.1) ^ok.1() ^raised.1()
      ok.1(%val.1 : py.Value):
        %cls.1 : py.Value = py.stdClass(\"builtins\", \"int\")
        %ok.11 : base.Bool = py.isInstance(%val.1, %cls.1) ^fail.7()
        ret(%ok.11)
      raised.1(%e.8 : py.Value):
        ret(true)
      fail.7(%e.9 : py.Value):
        ret(true)
    }
    free ensures \"result == OLD(len(x))\" {
      post.2(%r.2 : base.Except(py.Value, py.Value)):
        base.Except.case[py.Value, py.Value](%r.2) ^ok.2() ^raised.2()
      ok.2(%val.2 : py.Value):
        %len.1 : py.Value = base.old[py.Value, py.Value] ^fail.8() {
          old.1():
            %undef.6 : py.Value = py.undef(\"x\")
            %x.7 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.6)
            %len.2 : py.Value = py.len(%x.7) ^propagate.2()
            %scalar.0 : base.Bool = py.isImmutableScalar(%len.2)
            branch(%scalar.0) ^scalar.0() ^mutable.0()
          scalar.0():
            %res.5 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%len.2)
            ret(%res.5)
          mutable.0():
            %res.6 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%len.2)
            ret(%res.6)
          propagate.2(%exc.2 : py.Value):
            %err.2 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.2)
            ret(%err.2)
        }
        %eq.0 : py.Value = py.eq(%val.2, %len.1) ^fail.8()
        %ok.12 : base.Bool = py.truthy(%eq.0) ^fail.8()
        ret(%ok.12)
      raised.2(%e.10 : py.Value):
        ret(true)
      fail.8(%e.11 : py.Value):
        ret(true)
    }
    writes({
      loc.0():
        %l.0 : base.Loc = py.instanceState
        ret(%l.0)
    }, {
      loc.1():
        %undef.7 : py.Value = py.undef(\"x\")
        %x.8 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.7)
        %l.1 : base.Loc = py.attrLoc(%x.8, \"count\")
        ret(%l.1)
    }, {
      loc.2():
        %undef.8 : py.Value = py.undef(\"x\")
        %x.9 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.8)
        %l.2 : base.Loc = py.objLoc(%x.9)
        ret(%l.2)
    }, {
      loc.3():
        %l.3 : base.Loc = py.itemLoc(%kwargs.0, \"a\")
        ret(%l.3)
    }, {
      loc.4():
        %undef.9 : py.Value = py.undef(\"x\")
        %x.10 : py.Value = py.argOf(%args.0, %kwargs.0, 0, \"x\", %undef.9)
        %l.4 : base.Loc = py.reachLoc(%x.10)
        ret(%l.4)
    })
}
"

#guard_msgs in
#eval readBack model

/-! ## One clause at a time

Each test is the extern `@m.f(args, kwargs)` with one `requires` clause.  The first two are
accepted.  Each of the others breaks one rule, and the reader names the problem. -/

/-- The extern `@m.f(args, kwargs)` with the contract `clauses`. -/
private def withClauses (clauses : String) : String := s!"module m \{
  extern func @m.f(%args.0 : py.Value, %kwargs.0 : py.Value) -> base.Except(py.Value, py.Value)
{clauses}
}
"

-- A variadic operation applied to no variadic operand.
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = py.strIsOneOf(%args.0)
        %ok.1 : base.Bool = py.intIsOneOf(%args.0)
        %ok.2 : base.Bool = py.dictKeysWithin(%kwargs.0)
        %ok.3 : base.Bool = py.bindsTo(%args.0, %kwargs.0, 0, false)
        %kw.0 : py.Value = py.extraKwargs(%kwargs.0)
        branch(%ok.0) ^no.0() ^yes.0()
      no.0():
        ret(%ok.3)
      yes.0():
        ret(%ok.2)
    }")

-- A quantifier whose body passes the failure of `reSearch` on with `base.error`: the clause that
-- the rejections below change.
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = py.allIn(%args.0) ^fail.0() {
          body.0(%item.0 : py.Value):
            %found.0 : base.Bool = py.reSearch(\"a\", %item.0) ^propagate.0()
            %res.0 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](%found.0)
            ret(%res.0)
          propagate.0(%exc.0 : py.Value):
            %err.0 : base.Except(py.Value, base.Bool) = base.error[py.Value, base.Bool](%exc.0)
            ret(%err.0)
        }
        ret(%ok.0)
      fail.0(%e.0 : py.Value):
        ret(false)
    }")

-- `py.setAttr` changes state, so a clause may not apply it (E1).
/-- info: t.dyn:6:8: a contract region of @m.f may not change state, but py.setAttr is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %none.0 : py.Value = py.noneLit
        %set.0 : base.Unit = py.setAttr(%args.0, \"x\", %none.0) ^fail.0()
        ret(true)
      fail.0(%e.0 : py.Value):
        ret(false)
    }")

-- Nor may a quantifier's body, a region nested in the clause (E1 at depth).
/-- info: t.dyn:8:12: a contract region of @m.f may not change state, but py.setAttr is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = py.allIn(%args.0) ^fail.0() {
          body.0(%item.0 : py.Value):
            %none.0 : py.Value = py.noneLit
            %set.0 : base.Unit = py.setAttr(%item.0, \"x\", %none.0) ^propagate.0()
            %res.0 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](true)
            ret(%res.0)
          propagate.0(%exc.0 : py.Value):
            %err.0 : base.Except(py.Value, base.Bool) = base.error[py.Value, base.Bool](%exc.0)
            ret(%err.0)
        }
        ret(%ok.0)
      fail.0(%e.0 : py.Value):
        ret(false)
    }")

-- A quantifier's body that returns `ok(true)` when `reSearch` fails would make the clause hold on
-- a failure.  Its failure must go to a block that passes it on with `base.error` (C3).
/-- info: t.dyn:7:12: in a region nested in a contract of @m.f, the failure successor of %found.0 goes to recover.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = py.allIn(%args.0) ^fail.0() {
          body.0(%item.0 : py.Value):
            %found.0 : base.Bool = py.reSearch(\"a\", %item.0) ^recover.0()
            %res.0 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](%found.0)
            ret(%res.0)
          recover.0(%exc.0 : py.Value):
            %res.1 : base.Except(py.Value, base.Bool) = base.ok[py.Value, base.Bool](true)
            ret(%res.1)
        }
        ret(%ok.0)
      fail.0(%e.0 : py.Value):
        ret(false)
    }")

-- The literals of `strIsOneOf` are `base.String`s, so an integer is rejected.
/-- info: t.dyn:5:56: a base.Int literal where base.String is expected -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = py.strIsOneOf(%args.0, \"a\", 1)
        ret(%ok.0)
    }")

end StrataPython.Dyn.ContractOpsTest
