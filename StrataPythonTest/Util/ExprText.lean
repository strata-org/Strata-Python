/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Shape

/-! # Python expressions as text, for tests and tools

`exprText src e` prints a Python expression from its syntax tree, fully parenthesized, so that
CPython's `ast.parse(…, mode="eval")` reads it back as the same tree, positions aside. It prints
the constructs that a loop invariant's `P` may contain (`docs/PythonToDyn.md` §6.11), and `OLD(…)`
as a call; a literal is its source text, from `src`. Any other construct prints as `<expr>`. -/

namespace StrataPython.Dyn.ExprText

open StrataPython (expr cmpop)
open StrataDDM (SourceRange)

public section

/-- The symbol of a comparison operator. -/
def cmpSymbol : cmpop SourceRange → String
  | .Eq _ => "==" | .NotEq _ => "!=" | .Lt _ => "<" | .LtE _ => "<=" | .Gt _ => ">"
  | .GtE _ => ">=" | .Is _ => "is" | .IsNot _ => "is not" | .In _ => "in" | .NotIn _ => "not in"

/-- `e` printed from its syntax tree, fully parenthesized; a literal is its source text in `src`,
and a construct that a loop invariant can't contain prints as `<expr>`. -/
partial def exprText (src : String) (e : expr SourceRange) : String :=
  match e with
  | .Name _ ⟨_, n⟩ _ => n
  | .Constant sr .. => String.Pos.Raw.extract src sr.start sr.stop
  | .Call _ f args kws =>
    if !kws.val.isEmpty then "<expr>"
    else r f ++ "(" ++ ", ".intercalate (args.val.toList.map r) ++ ")"
  | .GeneratorExp _ elt gens => match gens.val.toList with
    | [.mk_comprehension _ t it ifs isAsync] =>
      if isAsync.value != 0 then "<expr>" else
      "(" ++ r elt ++ " for " ++ target t ++ " in " ++ r it ++
        String.join (ifs.val.toList.map fun x => " if " ++ r x) ++ ")"
    | _ => "<expr>"
  | .Subscript _ v i _ => r v ++ "[" ++ r i ++ "]"
  | .Slice _ lo hi st => (lo.val.map r).getD "" ++ ":" ++ (hi.val.map r).getD "" ++
      (match st.val with | some x => ":" ++ r x | none => "")
  -- The value in parentheses, so that `(1).real` doesn't read as the float `1.`.
  | .Attribute _ v ⟨_, n⟩ _ => "(" ++ r v ++ ")." ++ n
  | .BinOp _ l op rr => "(" ++ r l ++ " " ++ Shape.binarySymbol op ++ " " ++ r rr ++ ")"
  | .UnaryOp _ op x => "(" ++ Shape.unarySymbol op ++ " " ++ r x ++ ")"
  | .BoolOp _ op vs => "(" ++ (if op matches .And _ then " and " else " or ").intercalate
      (vs.val.toList.map r) ++ ")"
  | .Compare _ l ops rs => "(" ++ r l ++ String.join ((ops.val.toList.zip rs.val.toList).map
      fun (o, x) => " " ++ cmpSymbol o ++ " " ++ r x) ++ ")"
  | .IfExp _ c a b => "(" ++ r a ++ " if " ++ r c ++ " else " ++ r b ++ ")"
  | _ => "<expr>"
where
  r (e : expr SourceRange) : String := exprText src e
  target : expr SourceRange → String
    | .Name _ ⟨_, n⟩ _ => n
    | .Tuple _ ⟨_, ts⟩ _ => "(" ++ ", ".intercalate (ts.toList.map target) ++ ")"
    | _ => "<target>"

end

end StrataPython.Dyn.ExprText
