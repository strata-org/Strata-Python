/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataDyn.Base
import StrataDyn.DSL.Core
meta import StrataDyn.Base

set_option autoImplicit false

/-! # `Env.entries`

The declarations of an environment in declaration order, each checked: a primitive as a
`TypeRef`, a mutual group once with its members' fields as `TypeExpr`s, an instruction as an
`InsnRef`.  Member aliases are not listed separately.
-/

namespace Strata.Dyn.EntriesTest

private def names (s : Env Unit) : List Name := (s.entries.map (·.name)).toList

-- Declaration order, one entry per group: `Unit` and `Except` are groups, whose constructors and
-- case instructions follow them as instructions.
#guard names base == [bn "Unit", bn "unit", (bn "Unit").caseName,
  bn "Bool", bn "Int", bn "Float64", bn "String", bn "Sequence", bn "Ref",
  bn "Except", bn "ok", bn "error", (bn "Except").caseName,
  bn "refNew", bn "refGet", bn "refSet", bn "old", bn "Loc", bn "cellLoc",
  bn "jump", bn "branch", bn "unreachable",
  bn "Fn", bn "callCode"]

private environment Pairs extends Base where
  namespace pairs
  open base
  mutual
    data Tree (+a) where
      | tree (value : a) (children : Forest a)
    data Forest (+element) where
      | nil
      | cons (head : Tree element) (tail : Forest element)
  end
  end pairs

private def pn (s : String) : Name := .str (.str .base "pairs") s

-- A group lists every member, with its constructors and the fields' raw forms, in order.
#guard match (Pairs.env.entries[base.entries.size]? : Option (Env.Entry Pairs.env)) with
  | some (.data g) =>
    g.members.toList.map (·.decl.name) == [pn "Tree", pn "Forest"] &&
    g.members.toList.map (fun m => m.ctors.toList.map fun c =>
        (c.name, c.args.toList.map fun p => (p.name, p.type.toRaw))) ==
      [[(pn "tree", [("value", .var 0), ("children", .app (pn "Forest") #[.var 0])])],
       [(pn "nil", []),
        (pn "cons", [("head", .app (pn "Tree") #[.var 0]), ("tail", .app (pn "Forest") #[.var 0])])]]
  | _ => false

-- The entries past the base's are exactly the group and its constructors and cases.
#guard (names Pairs.env).drop (names base).length ==
  [pn "Tree", pn "tree", pn "nil", pn "cons", (pn "Tree").caseName, (pn "Forest").caseName]

-- An entry's name is declared, and a primitive's reference carries its declaration.
#guard base.entries.all fun e => e.name ∈ base
#guard match (base.entries[3]? : Option (Env.Entry base)) with
  | some (.type r) => r.name == bn "Bool" && r.decl.params.size == 0
  | _ => false
#guard match (base.entries[8]? : Option (Env.Entry base)) with
  | some (.type (arity := 1) r) => r.name == bn "Ref" && r.decl.paramNames == ["a"]
  | _ => false

end Strata.Dyn.EntriesTest
