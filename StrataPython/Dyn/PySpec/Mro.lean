/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Resolve
public import Std.Data.HashMap

set_option autoImplicit false

/-! # The MRO of model classes

CPython's C3 order of the bases of a class (its MRO), for classes of a model set and of the
standard library. A standard-library class other than `object` stands for
its MRO up to `object`, as `ClassNode.basesIn` says, so the order is CPython's only up to the
first standard-library class.
-/

namespace StrataPython.Dyn.PySpec

open StrataPython.Specs

public section

/-- A class of an MRO. -/
inductive ClassNode where
  /-- A class of the model set, by its module and its path in the module. -/
  | model (module : String) (path : Array String)
  /-- A class that the model set doesn't give, such as `builtins.Exception`, by its full name. -/
  | std (name : String)
deriving Inhabited, BEq, Hashable, Repr

/-- The class `object`. -/
def objectNode : ClassNode := .std "builtins.object"

/-- The node of a base that the table `t` resolves. -/
def Table.baseNode (t : Table) (b : PythonIdent) : ClassNode :=
  match t.classOf? b with
  | some c => .model c.module c.path
  | none => .std (toString b)

/-- The bases of a class, given the bases that its declaration lists (`none` for a class that
is not known): `object` for a class that lists none. A standard-library class other than
`object` has the base `object` alone. Up to the first standard-library class of an MRO, this
gives CPython's MRO: a standard-library class's own bases are standard-library classes, which
come after it. -/
def ClassNode.basesIn (listed : ClassNode → Option (Array ClassNode)) : ClassNode → Option (Array ClassNode)
  | .std n => some (if n == "builtins.object" then #[] else #[objectNode])
  | n => (listed n).map fun bs => if bs.isEmpty then #[objectNode] else bs

/-- CPython's C3 merge of the lists `ls`, or `none` where it fails. Each step removes the chosen
class from every list that holds it, so the total length shrinks by at least one, and `fuel` at
least that length is enough. -/
def c3Merge : Nat → List (List ClassNode) → Option (List ClassNode)
  | 0, _ => none
  | fuel + 1, ls =>
    let ls := ls.filter (!·.isEmpty)
    if ls.isEmpty then some [] else
    let good (l : List ClassNode) : Option ClassNode := match l with
      | h :: _ => if ls.any (·.tail.contains h) then none else some h
      | [] => none
    match ls.findSome? good with
    | none => none
    | some h => (h :: ·) <$> c3Merge fuel (ls.map (·.filter (· != h)))

/-- The MROs computed so far. -/
abbrev MroCache := Std.HashMap ClassNode (Option (List ClassNode))

/-- The MRO of `n`, with the bases that `bases` gives, or `none` where CPython's computation
fails or `fuel`, a bound on the depth of the class hierarchy, runs out. -/
def linearize (bases : ClassNode → Option (Array ClassNode)) :
    Nat → ClassNode → StateM MroCache (Option (List ClassNode))
  | 0, _ => pure none
  | fuel + 1, n => do
    if let some r := (← get)[n]? then return r
    let r ← match bases n with
      | none => pure none
      | some bs => do
        let mros ← bs.toList.mapM (linearize bases fuel)
        match mros.mapM id with
        | none => pure none
        | some ls =>
          let lists := ls ++ [bs.toList]
          pure ((n :: ·) <$> c3Merge (lists.foldl (· + ·.length) 1) lists)
    modify (·.insert n r)
    return r

/-- The model classes of the table `t`: the top-level ones, then the nested ones. -/
def Table.classes (t : Table) : Array ModelClass :=
  let top := t.modules.foldl (init := #[]) fun acc (_, names) =>
    names.foldl (init := acc) fun acc (_, e) => match e with
      | .cls c => acc.push c
      | _ => acc
  top ++ t.nested.map (·.2)

end -- public section

end StrataPython.Dyn.PySpec
