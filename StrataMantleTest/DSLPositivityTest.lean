/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Base
import StrataMantle.Env.WF
import StrataMantle.DSL
-- The test reads the environments' declarations directly.
import all StrataMantle.Env
-- The `#guard`s below run the core's check as compiled code.
meta import StrataMantle.Base
meta import StrataMantle.Env
meta import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# The `environment` command's positivity check agrees with the core's

The command checks a datatype's positivity itself, to report it at the payload's syntax
(`checkPositive`), and the core decides it again (`DataGroup.checkWith`). For each group the
command rejects for positivity in `DSLErrorTest`, the core rejects the same group, written raw.
A group that comes close, which the command declares, the core accepts, and its raw form is the
one the command declares.
-/

namespace Strata.Mantle.DSLPositivityTest

open Env.Raw

/-- The types the groups use: `Map`'s key and `F`'s arguments are non-positive. -/
public environment PosTypes extends Base where
  open base
  type Map (k) (+v)
  type F (args : list) (+r)
  type Tup (+ts : list)

/-- Close to the rejections: `a` and `Ok` itself sit in a positive list of a positive argument,
beside a non-positive argument. -/
public environment PosOk extends PosTypes where
  open base
  data Ok (+a) where
    | ok (m : Map Int (Tup [a, Ok a]))

/-- `DataGroup.checkWith` on `g`, appended to `outside` at the positions it occupies, with the
resolvers `checkGroup` gives it. -/
private def positive (outside : Array (Decl.Raw Unit)) (g : DataGroup Unit TypeExpr.Raw) : Bool :=
  let ds := outside ++ g.decls
  if p : DistinctDecls ds then
    let env := ofAscArray ds p
    let i := outside.size
    g.checkWith (env.paramsBefore (i + g.members.size))
      (RefBefore.check env (i + g.members.size)) (RefBefore.check env i)
  else false

/-- The declarations of `PosTypes`. -/
private def outside : Array (Decl.Raw Unit) := PosTypes.env.raw.decls.vals

private def int : TypeExpr.Raw := .app Base.Int.name #[]

/-- The one-member group `T` with parameters `params` and one constructor, `c`, of one field
`x : ty`. -/
private def group (T c : String) (params : Array (Param TyParam)) (ty : TypeExpr.Raw) :
    DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base T, params,
                   ctors := #[{ ann := (), name := .str .base c, args := #[⟨"x", ty⟩] }] }]
    nonEmpty := Nat.one_pos }

/-! ## What the command rejects, the core rejects -/

/- `Expr` recurses through non-positive parameter 1 of `Map` (`ErrPos`). -/
#guard !positive outside
  { members := #[{ ann := (), name := .str .base "Expr",
                   ctors := #[{ ann := (), name := .str .base "leaf", args := #[] },
                              { ann := (), name := .str .base "node",
                                args := #[⟨"kids", .app PosTypes.Map.name
                                  #[.app (.str .base "Expr") #[], int]⟩] }] }]
    nonEmpty := by decide }

/- Positive parameter `a` occurs under non-positive parameter 1 of `Map` (`ErrPos`). -/
#guard !positive outside
  (group "Wrap" "wrap" #[⟨"a", .pos⟩] (.app PosTypes.Map.name #[.var 0, int]))

/- Positive list parameter `as` occurs under non-positive parameter 1 of `F`, whole and spliced
(`ErrListData`).  Raw, a list parameter passed whole is the literal splicing it, `[*as]`. -/
#guard !positive outside
  (group "P" "mkP" #[⟨"as", ⟨.pos, .list⟩⟩] (.app PosTypes.F.name #[.list #[.var 0], int]))
#guard !positive outside
  (group "Q" "mkQ" #[⟨"as", ⟨.pos, .list⟩⟩] (.app PosTypes.F.name #[.list #[.var 0, int], int]))

/- `Bad` recurses through non-positive parameter 1 of `F`, and positive parameter `a` occurs
under it, each in a literal (`ErrListPos`). -/
#guard !positive outside
  (group "Bad" "mk" #[] (.app PosTypes.F.name #[.list #[.app (.str .base "Bad") #[]], int]))
#guard !positive outside
  (group "U" "mkU" #[⟨"a", .pos⟩] (.app PosTypes.F.name #[.list #[.var 0], int]))

/- Each, with its parameter declared non-positive or its recursion moved to `F`'s result, is
accepted: the rejections are for positivity. -/
#guard positive outside
  (group "Wrap" "wrap" #[⟨"a", .non⟩] (.app PosTypes.Map.name #[.var 0, int]))
#guard positive outside
  (group "P" "mkP" #[⟨"as", ⟨.non, .list⟩⟩] (.app PosTypes.F.name #[.list #[.var 0], int]))
#guard positive outside
  (group "Q" "mkQ" #[⟨"as", ⟨.non, .list⟩⟩] (.app PosTypes.F.name #[.list #[.var 0, int], int]))
#guard positive outside
  (group "Bad" "mk" #[] (.app PosTypes.F.name #[.list #[], .app (.str .base "Bad") #[]]))
#guard positive outside
  (group "U" "mkU" #[⟨"a", .non⟩] (.app PosTypes.F.name #[.list #[.var 0], int]))

/-! ## What the command declares, the core accepts -/

/-- `Ok`, written raw. -/
private def okRaw : DataGroup Unit TypeExpr.Raw :=
  { members := #[{ ann := (), name := .str .base "Ok", params := #[⟨"a", .pos⟩],
                   ctors := #[{ ann := (), name := .str .base "ok",
                                args := #[⟨"m", .app PosTypes.Map.name
                                  #[int, .app PosTypes.Tup.name
                                    #[.list #[.var 0, .app (.str .base "Ok") #[.var 0]]]]⟩] }] }]
    nonEmpty := by decide }

-- The command declares `okRaw`'s members, and the core accepts them.
#guard ((PosOk.env.raw.decls[PosOk.Ok.name]?).bind Decl.Raw.asGroup).map (·.members) ==
  some okRaw.members
#guard positive outside okRaw

end Strata.Mantle.DSLPositivityTest
