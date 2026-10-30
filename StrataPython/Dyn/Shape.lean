/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Scope
public import StrataDyn.Attr
public import StrataDyn.FloatText

set_option autoImplicit false

/-!
# Declared shapes

The facts the translator states about each class, all as attributes of the class body's
function, so that a class's shape is in one place (`docs/PythonToDyn.md` §6.7).  They are
what the source declares, written as it is written: a name is not resolved, so a consumer
such as Pylate must decide what `TypedDict`, `ClassVar` or `int` denote, from the bindings it
follows.  A private name is mangled, as the compiler does.

An expression `E`, an annotation, a base, a decorator, a default or an assigned value, is
stated as:

* `"typing.Optional"`: a name or attribute chain; a plain string is always one;
* `{name = E, args = [E, …]}`: a subscript `E[…]`;
* `{union = [E, …]}`: `A | B | …`, the `|` operator, also in a value;
* `[E, …]` and `{tuple = [E, …]}`: a list and a tuple display;
* `{call = E, args = [E, …], keywords = [{name = "k", value = E}, …]}`: a call;
* `{op = "*", args = [E, E]}` and `{op = "-", args = [E]}`: another binary operator, and a
  unary one;
* a constant: a boolean, an integer, a float, `unit` for `None`, `{str = "s"}` for a string,
  `{ellipsis = unit}` for `...`;
* `{expr = "Lambda"}`: any other expression, by its `ast` class name.
-/

/-! ## Helpers that the translator shares

The translator's literal and parameter helpers, defined here because the declared shapes use
them too. -/

namespace StrataPython.Dyn.PyTranslate

open Strata.Dyn
open StrataPython (arguments arg expr)
open StrataDDM (SourceRange)

public section

/-- The decimal literal `s` as `(m, neg, x)`, which denotes `m * 10^-x` if `neg`, else
`m * 10^x`: for example, `1.5e-3` gives `(15, true, 4)`.  It recurses on the characters, and
it is meant to read what Lean's `Syntax.decodeScientificLitVal?` reads: the tests compare the
two on every string of up to 5 characters.  It needs a `.` or an exponent, so `15` gives
`none`.  It is looser than Python: `_` may appear anywhere after the first digit, and `1.` and
`1e+` are read too. -/
@[expose] def decodeScientific (s : String) : Option (Nat × Bool × Nat) :=
  match s.toList with
  | c :: cs => if c.isDigit then intPart (c :: cs) 0 else none
  | [] => none
where
  /-- The value of a digit. -/
  digit? (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none
  /-- The digits before the `.` or the `e`, read into `val`. -/
  intPart : List Char → Nat → Option (Nat × Bool × Nat)
    | [], _ => none
    | c :: cs, val =>
      match digit? c with
      | some d => intPart cs (10 * val + d)
      | none =>
        if c == '_' then intPart cs val
        else if c == '.' then fracPart cs val 0
        else if c == 'e' || c == 'E' then expSign cs val 0
        else none
  /-- The digits after the `.`, read into `val`; `e` counts them. -/
  fracPart : List Char → Nat → Nat → Option (Nat × Bool × Nat)
    | [], val, e => some (val, true, e)
    | c :: cs, val, e =>
      match digit? c with
      | some d => fracPart cs (10 * val + d) (e + 1)
      | none =>
        if c == '_' then fracPart cs val e
        else if c == 'e' || c == 'E' then expSign cs val e
        else none
  /-- The sign of the exponent, if there is one. -/
  expSign : List Char → Nat → Nat → Option (Nat × Bool × Nat)
    | [], _, _ => none
    | c :: cs, val, e =>
      if c == '-' then expDigits cs val e true 0
      else if c == '+' then expDigits cs val e false 0
      else expDigits (c :: cs) val e false 0
  /-- The digits of the exponent, read into `exp`.  The result's exponent is `±exp - e`,
  because `val` also holds the `e` digits after the `.`. -/
  expDigits : List Char → Nat → Nat → Bool → Nat → Option (Nat × Bool × Nat)
    | [], val, e, neg, exp =>
      if neg then some (val, neg, exp + e)
      else if exp ≥ e then some (val, neg, exp - e)
      else some (val, true, e - exp)
    | c :: cs, val, e, neg, exp =>
      match digit? c with
      | some d => expDigits cs val e neg (10 * exp + d)
      | none => if c == '_' then expDigits cs val e neg exp else none

/-- The `Float` a Python float literal denotes: the nearest binary64 value, ties to even. -/
@[expose] def parseFloat? (s : String) : Option Float :=
  (decodeScientific s).map fun (m, neg, x) =>
    FloatText.ofDecimal ⟨false, m, if neg then -(x : Int) else x⟩

/-- The annotated parameters of `args`, each name with its annotation, in the order CPython
3.12 evaluates them: positional, positional-only, `*args`, keyword-only, then `**kwargs`. -/
@[expose] def paramAnnotations (args : arguments SourceRange) : Array (String × expr SourceRange) :=
  let .mk_arguments _ posOnly pos varPos kwOnly _ varKw _ := args
  (pos.val ++ posOnly.val ++ varPos.val.toArray ++ kwOnly.val ++ varKw.val.toArray).filterMap
    fun (.mk_arg _ ⟨_, n⟩ a _) => a.val.map (n, ·)

end -- public section

end StrataPython.Dyn.PyTranslate

namespace StrataPython.Dyn.Shape

open Strata.Dyn
open StrataPython.Dyn.PyScope (Table ScopeId mangle)
open StrataPython (stmt expr keyword arguments comprehension withitem excepthandler
  match_case opt_expr)
open StrataDDM (SourceRange)

public section

/-- A key `py.k`. -/
def key (k : String) : Name := (Name.base.str "py").str k

private def str (s : String) : AttrValue := .const (.str s)

private def record (fs : Array (String × AttrValue)) : AttrValue :=
  .record (fs.map fun (k, v) => (Name.base.str k, v))

/-- Proves that a recursive call is on a smaller part of the syntax tree: directly, or
through a member of an array. -/
local macro "shape_smaller" : tactic => `(tactic| first
  | omega
  | (have hlt := Array.sizeOf_lt_of_mem ‹_ ∈ _›
     try simp only [keyword.mk_keyword.sizeOf_spec, StrataDDM.Ann.mk.sizeOf_spec,
       comprehension.mk_comprehension.sizeOf_spec, withitem.mk_withitem.sizeOf_spec,
       excepthandler.ExceptHandler.sizeOf_spec, match_case.mk_match_case.sizeOf_spec,
       opt_expr.some_expr.sizeOf_spec] at hlt
     omega))

/-- `shape_smaller`, for a measure that is a pair. -/
local macro "shape_decreasing" : tactic => `(tactic| first
  | (apply Prod.Lex.right; omega)
  | (apply Prod.Lex.left; shape_smaller)
  | shape_smaller)

/-! ## Statements -/

/-- Proves that a block of a statement is smaller than the statement, after `cases` on the
block. -/
local macro "child_smaller" : tactic => `(tactic|
  (simp only [stmt.If.sizeOf_spec, stmt.While.sizeOf_spec, stmt.For.sizeOf_spec,
      stmt.AsyncFor.sizeOf_spec, stmt.With.sizeOf_spec, stmt.AsyncWith.sizeOf_spec,
      stmt.Try.sizeOf_spec, stmt.TryStar.sizeOf_spec, stmt.Match.sizeOf_spec,
      excepthandler.ExceptHandler.sizeOf_spec, match_case.mk_match_case.sizeOf_spec,
      StrataDDM.Ann.mk.sizeOf_spec] at *
   omega))

/-- The statement blocks nested in `s`, outside nested `def`s and `class`es, each smaller
than `s`. -/
def childBlocks (s : stmt SourceRange) :
    Array {b : Array (stmt SourceRange) // sizeOf b < sizeOf s} :=
  match s with
  | .If _ _ b o | .While _ _ b o => #[⟨b.val, by cases b; child_smaller⟩, ⟨o.val, by cases o; child_smaller⟩]
  | .For _ _ _ b o _ | .AsyncFor _ _ _ b o _ =>
    #[⟨b.val, by cases b; child_smaller⟩, ⟨o.val, by cases o; child_smaller⟩]
  | .With _ _ b _ | .AsyncWith _ _ b _ => #[⟨b.val, by cases b; child_smaller⟩]
  | .Try _ b hs o f | .TryStar _ b hs o f =>
    #[⟨b.val, by cases b; child_smaller⟩] ++
      (match hs with
       | ⟨_, hs⟩ => hs.attach.map fun ⟨h, mem⟩ => match h, mem with
         | .ExceptHandler _ _ _ hb, mem =>
           ⟨hb.val, by have hlt := Array.sizeOf_lt_of_mem mem; cases hb; child_smaller⟩) ++
      #[⟨o.val, by cases o; child_smaller⟩, ⟨f.val, by cases f; child_smaller⟩]
  | .Match _ _ ⟨_, cases⟩ =>
    cases.attach.map fun ⟨c, mem⟩ => match c, mem with
      | .mk_match_case _ _ _ b, mem =>
        ⟨b.val, by have hlt := Array.sizeOf_lt_of_mem mem; cases b; child_smaller⟩
  | _ => #[]

/-! ## Expressions -/

/-- The `ast` class name of `e`. -/
def exprKind : expr SourceRange → String
  | .BoolOp .. => "BoolOp" | .NamedExpr .. => "NamedExpr" | .BinOp .. => "BinOp"
  | .UnaryOp .. => "UnaryOp" | .Lambda .. => "Lambda" | .IfExp .. => "IfExp"
  | .Dict .. => "Dict" | .Set .. => "Set" | .ListComp .. => "ListComp"
  | .SetComp .. => "SetComp" | .DictComp .. => "DictComp"
  | .GeneratorExp .. => "GeneratorExp" | .Await .. => "Await" | .Yield .. => "Yield"
  | .YieldFrom .. => "YieldFrom" | .Compare .. => "Compare" | .Call .. => "Call"
  | .FormattedValue .. => "FormattedValue" | .Interpolation .. => "Interpolation"
  | .JoinedStr .. => "JoinedStr" | .TemplateStr .. => "TemplateStr"
  | .Constant .. => "Constant" | .Attribute .. => "Attribute" | .Subscript .. => "Subscript"
  | .Starred .. => "Starred" | .Name .. => "Name" | .List .. => "List" | .Tuple .. => "Tuple"
  | .Slice .. => "Slice"

/-- The text of a name or attribute chain, `a.b.c`, if `e` is one, each part mangled with
`privateName`. -/
def dotted (privateName : Option String) : expr SourceRange → Option String
  | .Name _ ⟨_, n⟩ _ => some (mangle privateName n)
  | .Attribute _ v ⟨_, a⟩ _ => (dotted privateName v).map (s!"{·}.{mangle privateName a}")
  | _ => none

/-- The symbol of a binary operator, such as `*`. -/
def binarySymbol : StrataPython.operator SourceRange → String
  | .Add _ => "+" | .Sub _ => "-" | .Mult _ => "*" | .MatMult _ => "@" | .Div _ => "/"
  | .FloorDiv _ => "//" | .Mod _ => "%" | .Pow _ => "**" | .LShift _ => "<<"
  | .RShift _ => ">>" | .BitAnd _ => "&" | .BitOr _ => "|" | .BitXor _ => "^"

/-- The symbol of a unary operator, such as `-`. -/
def unarySymbol : StrataPython.unaryop SourceRange → String
  | .Invert _ => "~" | .Not _ => "not" | .UAdd _ => "+" | .USub _ => "-"

/-- A keyword argument `name = value`; `**kw` has the name `unit`. -/
private def keywordFact (name : Option String) (value : AttrValue) : AttrValue :=
  record #[("name", (name.map str).getD (.const .unit)), ("value", value)]

mutual

/-- The expression `e`, stated as written, its private names mangled with `privateName`. -/
def expression (privateName : Option String) (e : expr SourceRange) : AttrValue :=
  match e with
  | .Name .. | .Attribute .. =>
    match dotted privateName e with
    | some d => str d
    | none => record #[("expr", str (exprKind e))]
  | .Constant _ c _ =>
    match c with
    | .ConString _ ⟨_, s⟩ => record #[("str", str s)]
    | .ConTrue _ => .const (.bool true)
    | .ConFalse _ => .const (.bool false)
    | .ConPos _ ⟨_, n⟩ => .const (.int n)
    | .ConNeg _ ⟨_, n⟩ => .const (.int (-(n : Int)))
    | .ConFloat _ ⟨_, f⟩ =>
      match PyTranslate.parseFloat? f with
      | some x => .const (.float x)
      | none => record #[("expr", str "Constant")]
    | .ConNone _ => .const .unit
    | .ConEllipsis _ => record #[("ellipsis", .const .unit)]
    | _ => record #[("expr", str "Constant")]
  | .UnaryOp _ (.USub _) (.Constant _ (.ConPos _ ⟨_, n⟩) _) => .const (.int (-(n : Int)))
  | .UnaryOp _ (.USub _) (.Constant _ (.ConFloat _ ⟨_, f⟩) _) =>
    match PyTranslate.parseFloat? f with
    | some x => .const (.float (-x))
    | none => record #[("expr", str "UnaryOp")]
  | .Subscript _ v (.Tuple _ ⟨_, ts⟩ _) _ =>
    record #[("name", expression privateName v),
      ("args", .list (ts.attach.map fun ⟨t, _⟩ => expression privateName t))]
  | .Subscript _ v k _ =>
    record #[("name", expression privateName v), ("args", .list #[expression privateName k])]
  | .BinOp _ l (.BitOr _) r =>
    record #[("union", .list (unionArms privateName l ++ #[expression privateName r]))]
  | .List _ ⟨_, ts⟩ _ => .list (ts.attach.map fun ⟨t, _⟩ => expression privateName t)
  | .Tuple _ ⟨_, ts⟩ _ =>
    record #[("tuple", .list (ts.attach.map fun ⟨t, _⟩ => expression privateName t))]
  | .Call _ f ⟨_, args⟩ ⟨_, kws⟩ =>
    record #[("call", expression privateName f),
      ("args", .list (args.attach.map fun ⟨a, _⟩ => expression privateName a)),
      ("keywords", .list (kws.attach.map fun ⟨k, h⟩ => match k, h with
        | .mk_keyword _ ⟨_, n⟩ v, _ => keywordFact (n.map (·.val)) (expression privateName v)))]
  | .BinOp _ l op r =>
    record #[("op", str (binarySymbol op)),
      ("args", .list #[expression privateName l, expression privateName r])]
  | .UnaryOp _ op x =>
    record #[("op", str (unarySymbol op)), ("args", .list #[expression privateName x])]
  | e => record #[("expr", str (exprKind e))]
termination_by (sizeOf e, 1)
decreasing_by all_goals (simp_wf; shape_decreasing)

/-- The arms of a union `A | B | C`, which the parser nests to the left, as `(A | B) | C`. -/
def unionArms (privateName : Option String) (e : expr SourceRange) : Array AttrValue :=
  match e with
  | .BinOp _ l (.BitOr _) r => unionArms privateName l ++ #[expression privateName r]
  | e => #[expression privateName e]
termination_by (sizeOf e, 2)
decreasing_by all_goals (simp_wf; shape_decreasing)

end

/-- Keyword arguments, each `{name, value}`. -/
def keywords (privateName : Option String) (kws : Array (keyword SourceRange)) : AttrValue :=
  .list (kws.map fun (.mk_keyword _ ⟨_, n⟩ v) =>
    keywordFact (n.map (·.val)) (expression privateName v))

/-- The expressions a statement of a class body evaluates itself, not those of its nested
blocks or its handlers' exception types, each with whether it may not be evaluated: its
targets and annotations too; for a `def`, its decorators, defaults and annotations; for a
`class`, its decorators, bases and keywords; for a `for`, its target, which may not be; for
an `assert`, its message, which may not be;
for a `match`, its cases' guards, which may not be. -/
def ownExprs (s : stmt SourceRange) : Array (expr SourceRange × Bool) :=
  let always (es : Array (expr SourceRange)) := es.map (·, false)
  match s with
  | .Expr _ e => always #[e]
  | .AugAssign _ t _ e => always #[t, e]
  | .Assign _ ⟨_, ts⟩ e _ => always (#[e] ++ ts)
  | .AnnAssign _ t a ⟨_, v⟩ _ => always (v.toArray ++ #[t, a])
  | .Return _ ⟨_, v⟩ => always v.toArray
  | .If _ t _ _ | .While _ t _ _ => always #[t]
  | .For _ t i _ _ _ | .AsyncFor _ t i _ _ _ => #[(i, false), (t, true)]
  | .Match _ t ⟨_, cases⟩ =>
    #[(t, false)] ++ cases.filterMap fun (.mk_match_case _ _ ⟨_, g⟩ _) => g.map (·, true)
  | .With _ ⟨_, items⟩ _ _ | .AsyncWith _ ⟨_, items⟩ _ _ =>
    always (items.flatMap fun (.mk_withitem _ c ⟨_, v⟩) => #[c] ++ v.toArray)
  | .Raise _ ⟨_, e⟩ ⟨_, c⟩ => always (e.toArray ++ c.toArray)
  | .Assert _ t ⟨_, m⟩ => #[(t, false)] ++ m.toArray.map (·, true)
  | .Delete _ ⟨_, ts⟩ => always ts
  | .FunctionDef _ _ args _ ⟨_, decs⟩ ⟨_, ret⟩ .. | .AsyncFunctionDef _ _ args _ ⟨_, decs⟩ ⟨_, ret⟩ .. =>
    let .mk_arguments _ _ _ _ _ ⟨_, kwDefaults⟩ _ ⟨_, defaults⟩ := args
    always (decs ++ defaults ++ kwDefaults.filterMap (fun | .some_expr _ e => some e | _ => none) ++
      (PyTranslate.paramAnnotations args).map (·.2) ++ ret.toArray)
  | .ClassDef _ _ ⟨_, bases⟩ ⟨_, kws⟩ _ ⟨_, decs⟩ _ =>
    always (decs ++ bases ++ kws.map fun (.mk_keyword _ _ v) => v)
  | _ => #[]

/-- The names the target `t` binds, in order: a name, or the names in a tuple, list or starred
target. -/
def targetNames (t : expr SourceRange) : Array String :=
  match t with
  | .Name _ ⟨_, n⟩ _ => #[n]
  | .Tuple _ ⟨_, ts⟩ _ | .List _ ⟨_, ts⟩ _ => ts.attach.flatMap fun ⟨u, _⟩ => targetNames u
  | .Starred _ u _ => targetNames u
  | _ => #[]
termination_by sizeOf t
decreasing_by all_goals (simp_wf; shape_smaller)

/-- All of `xs` marked as bindings that may not run. -/
private def mayNotRun (xs : Array (String × Bool)) : Array (String × Bool) :=
  xs.map fun (n, _) => (n, true)

/-- The names the assignment expressions `x := v` in `e` bind, in the order they run, outside
`lambda` bodies and comprehensions, which have scopes of their own; each with whether it may
not run: in the operands of `and` and `or` after the first, in the branches of `a if c else b`,
and in the comparisons of a chain after the first. -/
def walrusNames (e : expr SourceRange) : Array (String × Bool) :=
  match e with
  | .NamedExpr _ t v => walrusNames v ++ (targetNames t).map (·, false)
  | .BoolOp _ _ ⟨_, xs⟩ =>
    xs.attach.zipIdx.flatMap fun (⟨x, _⟩, i) =>
      if i == 0 then walrusNames x else mayNotRun (walrusNames x)
  | .Set _ ⟨_, xs⟩ | .JoinedStr _ ⟨_, xs⟩ | .TemplateStr _ ⟨_, xs⟩
  | .List _ ⟨_, xs⟩ _ | .Tuple _ ⟨_, xs⟩ _ => xs.attach.flatMap fun ⟨x, _⟩ => walrusNames x
  | .BinOp _ a _ b | .Subscript _ a b _ => walrusNames a ++ walrusNames b
  | .UnaryOp _ _ a | .Await _ a | .YieldFrom _ a | .Attribute _ a _ _ | .Starred _ a _ =>
    walrusNames a
  | .IfExp _ c a b => walrusNames c ++ mayNotRun (walrusNames a ++ walrusNames b)
  | .Dict _ ⟨_, ks⟩ ⟨_, vs⟩ =>
    -- Each key, then its value.
    vs.attach.zipIdx.flatMap fun (⟨v, _⟩, i) =>
      (match ks.attach[i]? with
       | some ⟨.some_expr _ k, _⟩ => walrusNames k
       | _ => #[]) ++ walrusNames v
  | .Yield _ ⟨_, x⟩ => match x with
    | some x => walrusNames x
    | none => #[]
  | .Compare _ a _ ⟨_, xs⟩ =>
    walrusNames a ++ xs.attach.zipIdx.flatMap fun (⟨x, _⟩, i) =>
      if i == 0 then walrusNames x else mayNotRun (walrusNames x)
  | .Call _ f ⟨_, xs⟩ ⟨_, kws⟩ =>
    walrusNames f ++ xs.attach.flatMap (fun ⟨x, _⟩ => walrusNames x) ++
      kws.attach.flatMap fun ⟨k, mem⟩ => match k, mem with
        | .mk_keyword _ _ v, _ => walrusNames v
  | .FormattedValue _ a _ ⟨_, s⟩ | .Interpolation _ a _ _ ⟨_, s⟩ =>
    walrusNames a ++ match s with
      | some s => walrusNames s
      | none => #[]
  | .Slice _ ⟨_, a⟩ ⟨_, b⟩ ⟨_, c⟩ =>
    (match a with | some a => walrusNames a | none => #[]) ++
    (match b with | some b => walrusNames b | none => #[]) ++
    (match c with | some c => walrusNames c | none => #[])
  | .Lambda _ (.mk_arguments _ _ _ _ _ ⟨_, kws⟩ _ ⟨_, ds⟩) _ =>
    ds.attach.flatMap (fun ⟨d, _⟩ => walrusNames d) ++
      kws.attach.flatMap fun ⟨k, mem⟩ => match k, mem with
        | .some_expr _ k, _ => walrusNames k
        | .missing_expr _, _ => #[]
  | .ListComp .. | .SetComp .. | .DictComp .. | .GeneratorExp .. | .Constant .. | .Name .. => #[]
termination_by sizeOf e
decreasing_by all_goals (simp_wf; shape_smaller)

/-! ## Classes -/

/-- A declared field, as written: an annotated simple name of a class body, or a `self.x: T`
of an `__init__` of it; its name, annotation and default, and whether it is under a compound
statement. -/
structure Field where
  name : String
  annotation : expr SourceRange
  default : Option (expr SourceRange)
  conditional : Bool
  /-- For a `self.name: annotation` of an `__init__`, the range of that `def`. -/
  initDef : Option SourceRange := none

/-- An assignment to `__slots__` in a class body: its value, whether it is an augmented
assignment, whether `__slots__` is one name of a tuple or list target, and whether it is under
a compound statement. -/
structure Slots where
  value : expr SourceRange
  augmented : Bool := false
  unpacked : Bool := false
  conditional : Bool

/-- A binding of a name in a class body that is neither a field nor an assignment to
`__slots__`: the name; the value of an assignment; the kind of any other binding, such as
`def` or `import`; whether it is an augmented assignment, or binds one name of a tuple or list
target; and whether it is under a compound statement. -/
structure Binding where
  name : String
  value : Option (expr SourceRange) := none
  kind : Option String := none
  augmented : Bool := false
  unpacked : Bool := false
  conditional : Bool

/-- Whether the assignment target `t` is the name `__slots__`. -/
private def isSlots (t : expr SourceRange) : Bool :=
  match t with
  | .Name _ ⟨_, "__slots__"⟩ _ => true
  | _ => false

/-- Whether the assignment target `t` binds `__slots__` inside a tuple or list target. -/
private def unpacksSlots (t : expr SourceRange) : Bool :=
  match t with
  | .Tuple _ ⟨_, ts⟩ _ | .List _ ⟨_, ts⟩ _ =>
    ts.attach.any fun ⟨u, _⟩ => isSlots u || unpacksSlots u
  | .Starred _ u _ => isSlots u || unpacksSlots u
  | _ => false
termination_by sizeOf t
decreasing_by all_goals (simp_wf; shape_smaller)

/-- The attributes of `self` that the statements `ss` of an `__init__` annotate, as
`self.x: T` with or without a value, in source order, outside nested `def`s and `class`es. -/
def initAnnotations (def_ : SourceRange) (self : String) (ss : Array (stmt SourceRange))
    (nested : Bool) : Array Field :=
  ss.attach.foldl (init := #[]) fun fs ⟨s, _⟩ =>
    let fs := match s with
      | .AnnAssign _ (.Attribute _ (.Name _ ⟨_, n⟩ _) ⟨_, a⟩ _) t _ _ =>
        if n == self then fs.push { name := a, annotation := t, default := none,
                                    conditional := nested, initDef := some def_ }
        else fs
      | _ => fs
    (childBlocks s).attach.foldl (init := fs) fun f ⟨⟨b, _⟩, _⟩ =>
      f ++ initAnnotations def_ self b true
termination_by sizeOf ss
decreasing_by simp_wf; have hlt := Array.sizeOf_lt_of_mem ‹s ∈ ss›; omega

/-- The name of the first positional parameter of `args`. -/
def firstParam (args : arguments SourceRange) : Option String :=
  let .mk_arguments _ ⟨_, posOnly⟩ ⟨_, pos⟩ .. := args
  (posOnly ++ pos)[0]?.map fun (.mk_arg _ ⟨_, n⟩ _ _) => n

/-- The names an `import` alias binds: `a` for `import a.b`, `c` for `… as c`; none for `*`. -/
private def aliasName (fromImport : Bool) (a : StrataPython.alias SourceRange) : Array String :=
  let .mk_alias _ ⟨_, name⟩ ⟨_, asname⟩ := a
  match asname with
  | some n => #[n.val]
  | none =>
    if name == "*" then #[]
    else if fromImport then #[name] else #[(name.takeWhile (· != '.')).toString]

/-- The bindings the statement `s` of a class body makes itself, not those of its nested blocks
or of its handlers: first those of its assignment expressions, then its own, other than fields
and assignment statements to `__slots__`.  `nested` says that `s` is under a compound
statement; a binding that may not run for another reason is conditional too. -/
def stmtBindings (s : stmt SourceRange) (nested : Bool) : Array Binding :=
  let kinded (k : String) (ns : Array String) : Array Binding :=
    ns.map fun n => { name := n, kind := some k, conditional := nested }
  let walrus : Array Binding := (ownExprs s).flatMap fun (e, maybe) =>
    (walrusNames e).map fun (n, c) =>
      { name := n, kind := some ":=", conditional := nested || maybe || c }
  let notSlots (n : String) := n != "__slots__"
  let own : Array Binding := match s with
    | .Assign _ ⟨_, ts⟩ v _ =>
      ts.flatMap fun t => match t with
        | .Name _ ⟨_, n⟩ _ =>
          if notSlots n then #[{ name := n, value := some v, conditional := nested }] else #[]
        | t => ((targetNames t).filter notSlots).map fun n =>
          { name := n, value := some v, unpacked := true, conditional := nested }
    | .AugAssign _ (.Name _ ⟨_, n⟩ _) _ v =>
      if notSlots n then #[{ name := n, value := some v, augmented := true, conditional := nested }]
      else #[]
    -- `(x): T = v` binds `x` but declares no field.
    | .AnnAssign _ (.Name _ ⟨_, n⟩ _) _ ⟨_, some v⟩ simple =>
      if simple.value == 0 && notSlots n then
        #[{ name := n, value := some v, conditional := nested }]
      else #[]
    | .FunctionDef _ ⟨_, n⟩ .. | .AsyncFunctionDef _ ⟨_, n⟩ .. => kinded "def" #[n]
    | .ClassDef _ ⟨_, n⟩ .. => kinded "class" #[n]
    | .Import _ ⟨_, as⟩ => kinded "import" (as.flatMap (aliasName false))
    | .ImportFrom _ _ ⟨_, as⟩ _ => kinded "import" (as.flatMap (aliasName true))
    -- A loop over an empty iterable binds nothing.
    | .For _ t .. | .AsyncFor _ t .. =>
      (targetNames t).map fun n => { name := n, kind := some "for", conditional := true }
    | .With _ ⟨_, items⟩ _ _ | .AsyncWith _ ⟨_, items⟩ _ _ =>
      kinded "with" (items.flatMap fun (.mk_withitem _ _ ⟨_, v⟩) => (v.map targetNames).getD #[])
    | .Delete _ ⟨_, ts⟩ => kinded "del" (ts.flatMap targetNames)
    | _ => #[]
  walrus ++ own

/-- The bindings a `try` statement `s` makes around its nested block `i`, if that block is the
body of a handler (`childBlocks` lists a `try`'s body, then its handlers): before it, those of
the assignment expressions in the handler's exception type and its `except … as n`; after it,
the unbinding of `n`, as CPython does when the handler ends.  All may not run. -/
private def handlerBindings (s : stmt SourceRange) (i : Nat) :
    Array Binding × Array Binding :=
  match s with
  | .Try _ _ ⟨_, hs⟩ _ _ | .TryStar _ _ ⟨_, hs⟩ _ _ =>
    match i with
    | 0 => (#[], #[])
    | i + 1 => match hs[i]? with
      | some (.ExceptHandler _ ⟨_, t⟩ ⟨_, n⟩ _) =>
        let types : Array Binding := ((t.map walrusNames).getD #[]).map fun (w, _) =>
          { name := w, kind := some ":=", conditional := true }
        match n with
        | some n =>
          (types.push { name := n.val, kind := some "except", conditional := true },
            #[{ name := n.val, kind := some "del", conditional := true }])
        | none => (types, #[])
      | none => (#[], #[])
  | _ => (#[], #[])

/-- What a class body declares, in source order. -/
structure Decls where
  fields : Array Field := #[]
  slots : Array Slots := #[]
  bindings : Array Binding := #[]

/-- The fields, the `__slots__` assignments and the other bindings of a class body, in source
order, outside nested `class`es and the `def`s other than `__init__`. -/
def bodyDecls (ss : Array (stmt SourceRange)) (nested : Bool := false) : Decls :=
  ss.attach.foldl (init := {}) fun d ⟨s, _⟩ =>
    let (fs, sl) := (d.fields, d.slots)
    let (fs, sl) := match s with
      | .AnnAssign _ (.Name _ ⟨_, n⟩ _) a ⟨_, v⟩ simple =>
        let fs := if simple.value != 0 then fs.push { name := n, annotation := a, default := v, conditional := nested } else fs
        match v with
        | some v =>
          if n == "__slots__" then (fs, sl.push { value := v, conditional := nested })
          else (fs, sl)
        | none => (fs, sl)
      | .Assign _ ⟨_, ts⟩ v _ =>
        if ts.any isSlots then (fs, sl.push { value := v, conditional := nested })
        else if ts.any unpacksSlots then
          (fs, sl.push { value := v, unpacked := true, conditional := nested })
        else (fs, sl)
      | .AugAssign _ t _ v =>
        if isSlots t then (fs, sl.push { value := v, augmented := true, conditional := nested })
        else (fs, sl)
      | .FunctionDef sr ⟨_, "__init__"⟩ args body .. =>
        match firstParam args with
        | some self => (fs ++ initAnnotations sr self body.val nested, sl)
        | none => (fs, sl)
      | _ => (fs, sl)
    let d := { fields := fs, slots := sl, bindings := d.bindings ++ stmtBindings s nested }
    (childBlocks s).attach.zipIdx.foldl (init := d) fun acc (⟨⟨b, _⟩, _⟩, i) =>
      let inner := bodyDecls b true
      { fields := acc.fields ++ inner.fields, slots := acc.slots ++ inner.slots,
        bindings :=
          let (before, after) := handlerBindings s i
          acc.bindings ++ before ++ inner.bindings ++ after }
termination_by sizeOf ss
decreasing_by simp_wf; have hlt := Array.sizeOf_lt_of_mem ‹s ∈ ss›; omega

/-- The record field `k = true` if `b` holds, else no field. -/
private def flag (k : String) (b : Bool) : Array (String × AttrValue) :=
  if b then #[(k, .const (.bool true))] else #[]

/-- The attributes of a class body's function.  The class statement has `bases`, `kws` and
`decorators`, which are read where the private name is `outer`.  Its body `body` runs in the
scope `inner`.  `inits` lists the `__init__`s that are not stubs: the range of each `def`, its
function, and whether it keeps its first parameter.  A field declared in an `__init__` points
to that function.  It is left out when that `__init__` is a stub or rebinds its first
parameter.  A name the body declares `global` or `nonlocal` is bound outside the class, so
its bindings, its `__slots__` assignments and its `__init__`'s fields are left out. -/
def classAttrs (table : Table) (outer : Option String) (inner : ScopeId)
    (bases : Array (expr SourceRange)) (kws : Array (keyword SourceRange))
    (decorators : Array (expr SourceRange)) (body : Array (stmt SourceRange))
    (inits : Array (SourceRange × Name × Bool)) : Array Attr := Id.run do
  let mut attrs : Array Attr := #[]
  unless bases.isEmpty do
    attrs := attrs.push (key "bases", .list (bases.map (expression outer)))
  unless kws.isEmpty do attrs := attrs.push (key "keywords", keywords outer kws)
  unless decorators.isEmpty do
    attrs := attrs.push (key "decorators", .list (decorators.map (expression outer)))
  let own := table.scopes[inner]?.bind (·.privateName)
  let decls := bodyDecls body
  let outside (n : String) := (table.symbol? inner n).any fun sym =>
    sym.uses.declaredGlobal || sym.uses.declaredNonlocal
  let fieldFact (f : Field) (in_ : Array (String × AttrValue)) : AttrValue :=
    record (#[("name", str (mangle own f.name)), ("type", expression own f.annotation)] ++
      ((f.default.map fun d => #[("default", expression own d)]).getD #[]) ++ in_ ++
      flag "conditional" f.conditional)
  attrs := attrs.push (key "fields", .list (decls.fields.filterMap fun f =>
    match f.initDef with
    | none => some (fieldFact f #[])
    | some r => match inits.find? (·.1 == r) with
      | some (_, fn, true) =>
        if outside "__init__" then none else some (fieldFact f #[("in", .const (.func fn))])
      | _ => none))
  unless decls.slots.isEmpty || outside "__slots__" do
    attrs := attrs.push (key "slots", .list (decls.slots.map fun s =>
      record (#[("value", expression own s.value)] ++ flag "augmented" s.augmented ++
        flag "unpacked" s.unpacked ++ flag "conditional" s.conditional)))
  let bindings := decls.bindings.filterMap fun b =>
    let n := mangle own b.name
    if outside n then none
    else some (record (#[("name", str n)] ++
      ((b.value.map fun v => #[("value", expression own v)]).getD #[]) ++
      ((b.kind.map fun k => #[("binding", str k)]).getD #[]) ++
      flag "augmented" b.augmented ++ flag "unpacked" b.unpacked ++
      flag "conditional" b.conditional))
  unless bindings.isEmpty do attrs := attrs.push (key "bindings", .list bindings)
  return attrs

/-! ## `__init__` -/

/-- The scopes nested in scope `s`, at any depth.  The scope pass numbers scopes in preorder,
so each child has a larger id than its parent; `none` if a child does not. -/
def descendants (t : Table) (s : ScopeId) : Option (Array ScopeId) :=
  ((t.scopes[s]?.map (·.children)).getD #[]).attach.foldlM (init := #[]) fun acc ⟨c, _⟩ =>
    if _h : s < c ∧ c < t.scopes.size then
      (descendants t c).map fun ds => acc.push c ++ ds
    else none
termination_by t.scopes.size - s
decreasing_by exact Nat.sub_lt_sub_left (Nat.lt_trans _h.1 _h.2) _h.1

/-- Whether a `nonlocal p` in a scope whose parent is `q` reaches the binding of `p` in scope
`s`: no function between them binds `p` itself.  A parent that is missing from the table, or
whose id is not smaller than its child's, which the scope pass never gives, counts as
reaching, so the `__init__`'s fields are left out. -/
private def reaches (t : Table) (s : ScopeId) (p : String) (q : Option ScopeId) : Bool :=
  match q with
  | none => false
  | some q =>
    q == s || (t.scopes[q]?.all fun sc =>
      !(sc.kind != .classBody && (sc.symbol? p).any fun sym =>
          sym.uses.bound && !sym.uses.declaredNonlocal) &&
      match sc.parent with
      | some r => if r < q then reaches t s p (some r) else true
      | none => false)
termination_by q.getD 0
decreasing_by simp_wf; omega

/-- Whether the method `__init__(args)`, whose scope is `scope`, keeps its first parameter
bound to the instance, so that its `self.x: T` declare fields of the instance.  The parameter
is bound again by a binding in the body, such as an assignment or an import, or by a nested
function or class body whose `nonlocal` reaches it.  A bare annotation of the parameter counts
as a binding, as the scope pass marks it.  A scope numbering it cannot follow counts as binding
the parameter again, so the `__init__`'s fields are left out. -/
def keepsSelf (table : Table) (scope : ScopeId) (args : arguments SourceRange) : Bool :=
  let privateName := table.scopes[scope]?.bind (·.privateName)
  match firstParam args with
  | none => true
  | some self =>
    let p := mangle privateName self
    !((table.symbol? scope p).any (fun sym => sym.uses.assigned || sym.uses.imported) ||
      match descendants table scope with
      | none => true
      | some ds => ds.any fun i => (table.scopes[i]?).any fun sc =>
        (sc.symbol? p).any fun sym =>
          sym.uses.declaredNonlocal && sym.uses.bound && reaches table scope p sc.parent)

end -- public section

end StrataPython.Dyn.Shape
