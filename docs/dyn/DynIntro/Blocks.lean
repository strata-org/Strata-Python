/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import VersoManual

/-!
# Custom blocks for "Introduction to Dyn"

Code, printed but not elaborated (the project depends on Verso only, not on the package;
`scripts/export-data.py --check` and the files of `checks/` check some listings against the
package instead, and `README.md`, "Layout", says which):
* ```` ```dyn "label" ````, ```` ```leantext "label" ````, ```` ```whilelang "label" ```` and
  ```` ```plaintext "label" ```` — a listing with an optional label and a Copy button, coloured by the
  same token rules as the interactive panels.

Structure:
* `:::deepDive "Title"` — a collapsible box (`<details>`); backticks in the title become code.
* `:::callout "Title" (kind := "tip" | "note" | "warning")` — an admonition.
* `:::checklist`, `:::sources`, `:::missingFeatures` — the design checklist, Sources lines and
  the list of missing features.
* `:::figure "Caption"` — a figure; without a caption argument, its last paragraph is the caption.
* `:::stages` holding ```` ```stage "N" "Title" "Summary" "lang" ```` blocks — the pipeline figure.
* ```` ```astTree "label" ```` — an indented AST outline: `Cat.ctor` is a category and a
  constructor, `'x` a leaf, `name:` a field name, any other word a constructor.

Code that must not break across lines (the theme gives `code.nowrap` `white-space: nowrap`):
* `::::nowrap` around a `:::table`: all inline code in the table; `::::nowrap 1 3`: only the
  code in columns 1 and 3.
* `{nowrap}` before a code span: that span alone, for a column that also holds long code.

Interactive:
* `:::widget "stepper" | "fold" | "cfg" | "interp" | "env" | "trace"` — one of the six panels.
  Its markup is `widgets/NAME.html`; the block's contents are what readers without JavaScript
  see. The panels' script, styles and data ship as Verso data files.
-/

open Verso Genre Manual
open Verso.Doc.Elab
open Verso.ArgParse
open Lean

namespace DynIntro

open Verso.Output (Html)

/-! ## Token rules (the same as the panels' `RULES` in `widgets/dyn-widgets.js`) -/

inductive Lang where | dyn | whilelang | lean | plain
deriving Repr, BEq, ToJson, FromJson

/-- ASCII word characters, as JavaScript's `\w`. -/
def isW (c : Char) : Bool := (c.isAlphanum && c.toNat < 128) || c == '_'

def isIdStart (c : Char) : Bool := (c.isAlpha && c.toNat < 128) || c == '_'

def litAt (cs : Array Char) (i : Nat) (w : String) : Bool :=
  let wc := w.toList.toArray
  i + wc.size ≤ cs.size && (List.range wc.size).all (fun k => cs[i + k]! == wc[k]!)

/-- `cs` has `w` at `i`, not followed by a word character (`w\b`). -/
def wordAt (cs : Array Char) (i : Nat) (w : String) : Option Nat :=
  if litAt cs i w then
    let j := i + w.length
    if j < cs.size && isW cs[j]! then none else some j
  else none

def firstWord (cs : Array Char) (i : Nat) (ws : List String) : Option Nat :=
  ws.findSome? (wordAt cs i)

partial def skipWhile (cs : Array Char) (p : Char → Bool) (j : Nat) : Nat :=
  if j < cs.size && p cs[j]! then skipWhile cs p (j + 1) else j

/-- `[A-Za-z_][\w.]*` at `i`. -/
def identAt (cs : Array Char) (i : Nat) : Option Nat :=
  if i < cs.size && isIdStart cs[i]! then some (skipWhile cs (fun c => isW c || c == '.') (i + 1))
  else none

/-- A sigil (`%`, `@`, `^`) and an identifier. -/
def sigilAt (cs : Array Char) (i : Nat) (c : Char) : Option Nat :=
  if i < cs.size && cs[i]! == c then identAt cs (i + 1) else none

def numAt (cs : Array Char) (i : Nat) (neg : Bool) : Option Nat :=
  let j := if neg && i < cs.size && cs[i]! == '-' then i + 1 else i
  let k := skipWhile cs Char.isDigit j
  if k > j then some k else none

def toEol (cs : Array Char) (i : Nat) : Nat := skipWhile cs (· != '\n') i

/-- The first index after `close`, searching from `j`. -/
partial def findClose (cs : Array Char) (close : String) (j : Nat) : Option Nat :=
  if j ≥ cs.size then none
  else if litAt cs j close then some (j + close.length)
  else findClose cs close (j + 1)

partial def stringAt (cs : Array Char) (i : Nat) : Option Nat :=
  if i < cs.size && cs[i]! == '"' then go (i + 1) else none
where
  go (j : Nat) : Option Nat :=
    if j ≥ cs.size then none
    else if cs[j]! == '\\' then go (j + 2)
    else if cs[j]! == '"' then some (j + 1)
    else go (j + 1)

def dynKw : List String := ["module", "func", "jump", "branch", "ret", "unreachable", "const"]

def leanKw : List String :=
  ["public", "private", "environment", "extends", "where", "namespace", "open", "end", "data",
   "type", "insn", "terminal", "abbrev", "mutual", "def", "let", "do", "if", "then", "else",
   "match", "with", "return", "fun", "for", "in", "unless", "mut", "structure", "instance",
   "inductive", "deriving", "section", "variable", "theorem", "op", "category", "dialect"]

def leanTy : List String :=
  ["Int", "Bool", "Unit", "Nat", "Array", "List", "Sem", "Label", "Region", "Flow", "IntList",
   "Cell", "Value", "Except", "Ref", "Fn", "Code", "Exp", "Stmt", "Body", "Ident"]

def whileKw : List String :=
  ["fun", "var", "while", "try", "catch", "return", "print", "raise", "region", "if", "else",
   "ref", "case", "of", "wcell"]

def whileTy : List String := ["Int", "Bool", "Unit", "IntList", "Ref", "ListRef", "Cell"]

/-- One rule: a class and a matcher returning the end of the match. -/
abbrev Rule := String × (Array Char → Nat → Option Nat)

def dynOp (cs : Array Char) (i : Nat) : Option Nat := do
  let j ← ["base", "while", "py"].findSome? fun p =>
    if litAt cs i (p ++ ".") then some (i + p.length + 1) else none
  let k ← identAt cs j
  if k ≥ cs.size || cs[k]! == '[' || cs[k]! == '(' || cs[k]!.isWhitespace then some k else none

def leanComment (cs : Array Char) (i : Nat) : Option Nat :=
  if litAt cs i "--" then some (toEol cs i)
  else if litAt cs i "/-" then findClose cs "-/" (i + 2)
  else if litAt cs i "/*" then findClose cs "*/" (i + 2)
  else none

def leanFn (cs : Array Char) (i : Nat) : Option Nat :=
  if litAt cs i "@[" then
    let j := skipWhile cs (· != ']') (i + 2)
    if j < cs.size then some (j + 1) else none
  else if i < cs.size && cs[i]! == '#' then
    let j := skipWhile cs (fun c => (c.isLower && c.toNat < 128) || c == '_') (i + 1)
    if j > i + 1 then some j else none
  else none

def rules : Lang → List Rule
  | .dyn => [
      ("t-com", fun cs i => if litAt cs i "--" then some (toEol cs i) else none),
      ("t-kw", fun cs i => firstWord cs i dynKw),
      ("t-val", fun cs i => sigilAt cs i '%'),
      ("t-fn", fun cs i => sigilAt cs i '@'),
      ("t-label", fun cs i => sigilAt cs i '^'),
      ("t-op", dynOp),
      ("t-num", fun cs i => numAt cs i true)]
  | .lean => [
      ("t-com", leanComment),
      ("t-str", stringAt),
      ("t-kw", fun cs i => firstWord cs i leanKw),
      ("t-fn", leanFn),
      ("t-type", fun cs i => firstWord cs i leanTy),
      ("t-num", fun cs i => numAt cs i false)]
  | .whilelang => [
      ("t-kw", fun cs i => firstWord cs i whileKw),
      ("t-type", fun cs i => firstWord cs i whileTy),
      ("t-num", fun cs i => numAt cs i false)]
  | .plain => []

/-- Tokenize: `(some class, text)` for a token, `(none, text)` for plain text. -/
def tokenize (lang : Lang) (src : String) : Array (Option String × String) := Id.run do
  let cs := src.toList.toArray
  let rs := rules lang
  let mut out : Array (Option String × String) := #[]
  let mut plain := ""
  let mut i := 0
  -- Every iteration consumes at least one character.
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let prev := if i > 0 then cs[i - 1]! else ' '
    let opener := litAt cs i "--" || litAt cs i "/-" || litAt cs i "/*" || cs[i]! == '"'
    -- Inside a word (or right after a sigil) only a comment or a string may start.
    if (isW prev || prev == '.' || prev == '%' || prev == '@' || prev == '^') && !opener then
      plain := plain.push cs[i]!; i := i + 1
    else
      match rs.findSome? (fun (cls, m) => (m cs i).bind fun j => if j > i then some (cls, j) else none) with
      | some (cls, j) =>
        if !plain.isEmpty then out := out.push (none, plain); plain := ""
        out := out.push (some cls, String.ofList (cs.extract i j).toList)
        i := j
      | none => plain := plain.push cs[i]!; i := i + 1
  if !plain.isEmpty then out := out.push (none, plain)
  return out

def tokHtml : Option String × String → Html
  | (none, s) => .text true s
  | (some cls, s) => .tag "span" #[("class", cls)] (.text true s)

/-- Highlighted code, one `span.tk-line` per line; tokens that cross lines are split. -/
def highlight (lang : Lang) (src : String) : Html := Id.run do
  let src := (src.dropEndWhile (· == '\n')).toString
  let mut lines : Array (Array Html) := #[#[]]
  for (cls, s) in tokenize lang src do
    let parts := s.splitOn "\n"
    let mut first := true
    for p in parts do
      if !first then lines := lines.push #[]
      first := false
      if !p.isEmpty then lines := lines.modify (lines.size - 1) (·.push (tokHtml (cls, p)))
  return .seq <| lines.map fun l => Html.tag "span" #[("class", "tk-line")] (.seq l)

def langLabel : Lang → String
  | .dyn => "Dyn"
  | .whilelang => "While"
  | .lean => "Lean"
  | .plain => "Text"

def langClass : Lang → String
  | .dyn => "dyn"
  | .whilelang => "whilelang"
  | .lean => "lean"
  | .plain => "plain"

def span (cls : String) (s : String) : Html :=
  .tag "span" #[("class", cls)] (.text true s)

/-- Backtick spans in a plain string become `<code>`. -/
def codeSpans (s : String) : Html :=
  .seq <| ((s.splitOn "`").toArray.mapIdx fun i part =>
    if i % 2 == 1 then Html.tag "code" #[] (.text true part) else .text true part)

/-! ## Assets -/

def widgetsJs : JsFile :=
  { filename := "dyn-widgets.js", contents := ⟨include_str "../widgets/dyn-widgets.js"⟩,
    sourceMap? := none, after := #["dyn-intro-data.js"] }

def widgetsData : JsFile :=
  { filename := "dyn-intro-data.js", contents := ⟨include_str "../widgets/intro-data.js"⟩,
    sourceMap? := none }

def widgetsCss : CssFile :=
  { filename := "dyn-widgets.css", contents := ⟨include_str "../widgets/dyn-widgets.css"⟩ }

def copyJs : JsFile :=
  { filename := "code-pane.js", sourceMap? := none, contents := ⟨r#"
// Copy buttons on printed code panes.
document.addEventListener('DOMContentLoaded', function () {
  document.querySelectorAll('.copy-btn').forEach(function (btn) {
    btn.addEventListener('click', function () {
      var code = btn.closest('figure').querySelector('pre').innerText;
      var done = function () { btn.textContent = 'Copied'; setTimeout(function () { btn.textContent = 'Copy'; }, 1200); };
      if (navigator.clipboard && window.isSecureContext) navigator.clipboard.writeText(code).then(done, done);
      else {
        var t = document.createElement('textarea'); t.value = code; document.body.appendChild(t); t.select();
        try { document.execCommand('copy'); } catch (e) {} t.remove(); done();
      }
    });
  });
});
"#⟩ }

/-! ## Printed code blocks -/

block_extension Block.printed (lang : Lang) (title : Option String) (src : String) where
  data := toJson (lang, title, src)
  traverse _ _ _ := pure none
  extraJsFiles := {copyJs}
  extraCssFiles := {widgetsCss}
  toHtml := some fun _goI _goB _id data _contents => do
    let .ok ((lang, title, src) : Lang × Option String × String) := fromJson? data
      | pure (.text true "bad printed block")
    pure <| .tag "figure" #[("class", s!"code-pane lang-{langClass lang}")] <| .seq #[
      .tag "figcaption" #[("class", "code-pane-title")] <| .seq #[
        span "code-pane-lang" (langLabel lang),
        match title with
        | some t => .tag "span" #[("class", "code-pane-name")] (.text true t)
        | none => .empty,
        .tag "button" #[("class", "copy-btn"), ("type", "button"), ("aria-label", "Copy code")]
          (.text true "Copy")],
      .tag "pre" #[("class", "code-pane-body")] (.tag "code" #[] (highlight lang src))]
  toTeX := some fun _ _ _ _ _ => pure .empty

structure PrintedCfg where
  title : Option String := none

instance : FromArgs PrintedCfg DocElabM where
  fromArgs := PrintedCfg.mk <$> ((some <$> .positional `title .string) <|> pure none)

@[code_block]
def dyn : CodeBlockExpanderOf PrintedCfg
  | {title}, str => ``(Verso.Doc.Block.other (Block.printed Lang.dyn $(quote title) $(quote str.getString)) #[])

@[code_block]
def whilelang : CodeBlockExpanderOf PrintedCfg
  | {title}, str => ``(Verso.Doc.Block.other (Block.printed Lang.whilelang $(quote title) $(quote str.getString)) #[])

/-- Lean shown as text, not elaborated (it needs StrataDyn). -/
@[code_block]
def leantext : CodeBlockExpanderOf PrintedCfg
  | {title}, str => ``(Verso.Doc.Block.other (Block.printed Lang.lean $(quote title) $(quote str.getString)) #[])

@[code_block]
def plaintext : CodeBlockExpanderOf PrintedCfg
  | {title}, str => ``(Verso.Doc.Block.other (Block.printed Lang.plain $(quote title) $(quote str.getString)) #[])

/-! ## Simple wrappers -/

-- A block that wraps its contents in one element.
block_extension Block.wrap (tag : String) (attrs : Array (String × String)) where
  data := toJson (tag, attrs)
  traverse _ _ _ := pure none
  extraCssFiles := {widgetsCss}
  toHtml := some fun _goI goB _id data contents => do
    let .ok ((tag, attrs) : String × Array (String × String)) := fromJson? data | pure .empty
    pure <| .tag tag attrs (.seq (← contents.mapM goB))
  toTeX := some fun _ goB _ _ contents => do pure (.seq (← contents.mapM goB))

def wrapWith (tag : String) (attrs : Array (String × String)) (stxs : Array (TSyntax `block)) : DocElabM Term := do
  let args ← stxs.mapM elabBlock
  ``(Verso.Doc.Block.other (Block.wrap $(quote tag) $(quote attrs)) #[ $[ $args ],* ])

@[directive]
def checklist : DirectiveExpanderOf Unit
  | (), stxs => wrapWith "aside" #[("class", "checklist"), ("aria-label", "Design checklist")] stxs

@[directive]
def sources : DirectiveExpanderOf Unit
  | (), stxs => wrapWith "div" #[("class", "sources")] stxs

@[directive]
def missingFeatures : DirectiveExpanderOf Unit
  | (), stxs => wrapWith "div" #[("class", "missing-list")] stxs

@[directive]
def stages : DirectiveExpanderOf Unit
  | (), stxs => wrapWith "div" #[("class", "stages")] stxs

/-! ## Code that does not break -/

/-- `attrs` with `cls` added to its `class`. -/
def addClass (cls : String) (attrs : Array (String × String)) : Array (String × String) :=
  if attrs.any (·.1 == "class") then
    attrs.map fun (k, v) => if k == "class" then (k, v ++ " " ++ cls) else (k, v)
  else attrs.push ("class", cls)

/-- `html` with the class `nowrap` on each `<code>` in it. -/
partial def nowrapCode : Html → Html
  | .tag "code" attrs c => .tag "code" (addClass "nowrap" attrs) c
  | .tag t attrs c => .tag t attrs (nowrapCode c)
  | .seq hs => .seq (hs.map nowrapCode)
  | h => h

/-- The cells of a row's contents, flattening sequences. -/
partial def rowParts : Html → Array Html
  | .seq hs => hs.flatMap rowParts
  | h => #[h]

/-- `html` with the class `nowrap` on the `<code>` in the columns `cols` (counted from 1) of each
table row, or in every column if `cols` is empty. -/
partial def nowrapColumns (cols : List Nat) : Html → Html
  | .tag "tr" attrs c => Id.run do
    let mut out := #[]
    let mut col := 0
    for h in rowParts c do
      match h with
      | .tag t _ _ =>
        if t == "td" || t == "th" then
          col := col + 1
          out := out.push (if cols.isEmpty || cols.contains col then nowrapCode h else h)
        else out := out.push h
      | _ => out := out.push h
    return .tag "tr" attrs (.seq out)
  | .tag t attrs c => .tag t attrs (nowrapColumns cols c)
  | .seq hs => .seq (hs.map (nowrapColumns cols))
  | h => h

block_extension Block.nowrap (cols : List Nat) where
  data := toJson cols
  traverse _ _ _ := pure none
  toHtml := some fun _goI goB _id data contents => do
    let cols := (fromJson? data : Except String (List Nat)).toOption.getD []
    pure <| nowrapColumns cols (.seq (← contents.mapM goB))
  toTeX := some fun _ goB _ _ contents => do pure (.seq (← contents.mapM goB))

structure NowrapCfg where
  cols : List Nat

instance : FromArgs NowrapCfg DocElabM where
  fromArgs := NowrapCfg.mk <$> .many (.positional' `column)

inline_extension Inline.nowrap where
  traverse _ _ _ := pure none
  toHtml := some fun goI _id _data contents => do
    pure <| nowrapCode (.seq (← contents.mapM goI))
  toTeX := some fun goI _ _ contents => do pure (.seq (← contents.mapM goI))

/-- A code span that does not break across lines. -/
@[role]
def nowrap : RoleExpanderOf Unit
  | (), inls => do
    let #[inl] := inls | throwError "expected one code span"
    unless inl.raw.isOfKind ``Lean.Doc.Syntax.code do throwErrorAt inl "expected a code span"
    ``(Verso.Doc.Inline.other Inline.nowrap #[$(← elabInline inl)])

/-- The code in a table, or in some of its columns, does not break across lines. -/
@[directive nowrap]
def nowrapTable : DirectiveExpanderOf NowrapCfg
  | {cols}, stxs => do
    let #[stx] := stxs | throwError "expected one table"
    if cols.contains 0 then throwError "columns are counted from 1"
    let arg ← elabBlock stx
    ``(Verso.Doc.Block.other (Block.nowrap $(quote cols)) #[$arg])

/-! ## Deep dive -/

block_extension Block.deepDive (title : String) where
  data := toJson title
  traverse _ _ _ := pure none
  toHtml := some fun _goI goB _id data contents => do
    let title := (fromJson? data : Except String String).toOption.getD "Details"
    pure <| .tag "details" #[("class", "deep-dive")] <| .seq #[
      .tag "summary" #[] <| .seq #[span "dd-kicker" "Deep dive",
        .tag "span" #[("class", "dd-title")] (codeSpans title), span "dd-chevron" ""],
      .tag "div" #[("class", "dd-body")] (.seq (← contents.mapM goB))]
  toTeX := some fun _ goB _ _ contents => do pure (.seq (← contents.mapM goB))

structure TitleCfg where
  title : String

instance : FromArgs TitleCfg DocElabM where
  fromArgs := TitleCfg.mk <$> .positional `title .string

@[directive]
def deepDive : DirectiveExpanderOf TitleCfg
  | {title}, stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.deepDive $(quote title)) #[ $[ $args ],* ])

/-! ## Callout -/

block_extension Block.callout (kind : String) (title : String) where
  data := toJson (kind, title)
  traverse _ _ _ := pure none
  toHtml := some fun _goI goB _id data contents => do
    let .ok ((kind, title) : String × String) := fromJson? data | pure .empty
    pure <| .tag "aside" #[("class", s!"callout callout-{kind}")] <| .seq #[
      .tag "div" #[("class", "callout-title")] (.text true title),
      .tag "div" #[("class", "callout-body")] (.seq (← contents.mapM goB))]
  toTeX := some fun _ goB _ _ contents => do pure (.seq (← contents.mapM goB))

structure CalloutCfg where
  title : String
  kind : String

instance : FromArgs CalloutCfg DocElabM where
  fromArgs := CalloutCfg.mk <$> .positional `title .string <*> .namedD `kind .string "note"

@[directive]
def callout : DirectiveExpanderOf CalloutCfg
  | {title, kind}, stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.callout $(quote kind) $(quote title)) #[ $[ $args ],* ])

/-! ## Figure -/

-- With no caption argument, the last block is the caption (so a caption may hold links).
block_extension Block.figure (caption : Option String) where
  data := toJson caption
  traverse _ _ _ := pure none
  toHtml := some fun goI goB _id data contents => do
    let cap := (fromJson? data : Except String (Option String)).toOption.join
    match cap with
    | some c =>
      pure <| .tag "figure" #[("class", "doc-figure")] <| .seq #[
        .tag "div" #[("class", "doc-figure-body")] (.seq (← contents.mapM goB)),
        .tag "figcaption" #[] (.text true c)]
    | none =>
      let capHtml ← match contents.back? with
        | some (.para inls) => do pure (Html.seq (← inls.mapM goI))
        | some b => goB b
        | none => pure .empty
      pure <| .tag "figure" #[("class", "doc-figure")] <| .seq #[
        .tag "div" #[("class", "doc-figure-body")] (.seq (← contents.pop.mapM goB)),
        .tag "figcaption" #[] capHtml]
  toTeX := some fun _ goB _ _ contents => do pure (.seq (← contents.mapM goB))

structure FigureCfg where
  caption : Option String

instance : FromArgs FigureCfg DocElabM where
  fromArgs := FigureCfg.mk <$> ((some <$> .positional `caption .string) <|> pure none)

@[directive]
def figure : DirectiveExpanderOf FigureCfg
  | {caption}, stxs => do
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.figure $(quote caption)) #[ $[ $args ],* ])

/-! ## Pipeline stages -/

def langOf : String → Lang
  | "dyn" => .dyn
  | "whilelang" => .whilelang
  | "lean" => .lean
  | _ => .plain

block_extension Block.stage (num title summary lang src : String) where
  data := toJson [num, title, summary, lang, src]
  traverse _ _ _ := pure none
  extraCssFiles := {widgetsCss}
  toHtml := some fun _goI _goB _id data _ => do
    let .ok [num, title, summary, lang, src] := (fromJson? data : Except String (List String))
      | pure .empty
    let l := langOf lang
    pure <| .tag "div" #[("class", "stage")] <| .seq #[
      span "num" num,
      .tag "h4" #[] (.text true title),
      .tag "p" #[] (.text true summary),
      .tag "pre" #[("class", langClass l)] (.tag "code" #[] (highlight l src))]
  toTeX := some fun _ _ _ _ _ => pure .empty

structure StageCfg where
  num : String
  title : String
  summary : String
  lang : String

instance : FromArgs StageCfg DocElabM where
  fromArgs := StageCfg.mk <$> .positional `num .string <*> .positional `title .string <*>
    .positional `summary .string <*> .positional `lang .string

@[code_block]
def stage : CodeBlockExpanderOf StageCfg
  | {num, title, summary, lang}, str =>
    ``(Verso.Doc.Block.other (Block.stage $(quote num) $(quote title) $(quote summary) $(quote lang) $(quote str.getString)) #[])

/-! ## AST outline -/

def astLineHtml (line : String) : Html := Id.run do
  let cs := line.toList.toArray
  let mut out : Array Html := #[]
  let mut plain := ""
  let mut i := 0
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '\'' then
      let j := skipWhile cs isW (i + 1)
      if !plain.isEmpty then out := out.push (.text true plain); plain := ""
      out := out.push (span "leaf" (String.ofList (cs.extract (i + 1) j).toList))
      i := j
    else if isIdStart c then
      let j := skipWhile cs isW i
      let w := String.ofList (cs.extract i j).toList
      if j + 1 < cs.size && cs[j]! == '.' && c.isUpper && isIdStart cs[j + 1]! then
        let k := skipWhile cs isW (j + 1)
        if !plain.isEmpty then out := out.push (.text true plain); plain := ""
        out := out.push (span "cat" w)
        out := out.push (.text true ".")
        out := out.push (span "ctor" (String.ofList (cs.extract (j + 1) k).toList))
        i := k
      else if j < cs.size && cs[j]! == ':' then
        plain := plain ++ w; i := j
      else
        if !plain.isEmpty then out := out.push (.text true plain); plain := ""
        out := out.push (span "ctor" w)
        i := j
    else
      plain := plain.push c; i := i + 1
  if !plain.isEmpty then out := out.push (.text true plain)
  return .seq out

/-- Nested `<li>`s from `(depth, line)` pairs. -/
partial def astItems : List (Nat × String) → Array Html
  | [] => #[]
  | (d, l) :: rest =>
    let kids := rest.takeWhile (·.1 > d)
    let later := rest.dropWhile (·.1 > d)
    let kidsHtml := if kids.isEmpty then Html.empty else .tag "ul" #[] (.seq (astItems kids))
    #[Html.tag "li" #[] (.seq #[astLineHtml l, kidsHtml])] ++ astItems later

block_extension Block.astTree (label : String) (src : String) where
  data := toJson (label, src)
  traverse _ _ _ := pure none
  extraCssFiles := {widgetsCss}
  toHtml := some fun _goI _goB _id data _ => do
    let .ok ((label, src) : String × String) := fromJson? data | pure .empty
    let lines := (src.splitOn "\n").filter (!·.trimAscii.isEmpty) |>.map fun l =>
      let ind := (l.takeWhile (· == ' ')).toString.length
      (ind / 2, (l.drop ind).toString)
    pure <| .tag "ul" #[("class", "tree"), ("aria-label", label)] (.seq (astItems lines))
  toTeX := some fun _ _ _ _ _ => pure .empty

@[code_block]
def astTree : CodeBlockExpanderOf TitleCfg
  | {title}, str => ``(Verso.Doc.Block.other (Block.astTree $(quote title) $(quote str.getString)) #[])

/-! ## Interactive panels -/

def widgetMarkup : List (String × String) := [
  ("stepper", include_str "../widgets/stepper.html"),
  ("fold", include_str "../widgets/fold.html"),
  ("cfg", include_str "../widgets/cfg.html"),
  ("interp", include_str "../widgets/interp.html"),
  ("env", include_str "../widgets/env.html"),
  ("trace", include_str "../widgets/trace.html")]

def childrenMark : String := "<!--CHILDREN-->"

block_extension Block.widget (name : String) where
  data := toJson name
  traverse _ _ _ := pure none
  extraJsFiles := {widgetsData, widgetsJs}
  extraCssFiles := {widgetsCss}
  toHtml := some fun _goI goB _id data contents => do
    let .ok (name : String) := fromJson? data | pure .empty
    let some markup := widgetMarkup.lookup name | pure (.text true s!"unknown widget {name}")
    let kids ← contents.mapM goB
    let nojs : Html :=
      if contents.isEmpty then .empty else .tag "div" #[("class", "nojs-note")] (.seq kids)
    match markup.splitOn childrenMark with
    | [before, after] => pure <| .seq #[.text false before, nojs, .text false after]
    | _ => pure <| .seq #[.text false markup, nojs]
  toTeX := some fun _ goB _ _ contents => do pure (.seq (← contents.mapM goB))

structure WidgetCfg where
  name : String

instance : FromArgs WidgetCfg DocElabM where
  fromArgs := WidgetCfg.mk <$> .positional `name .string

@[directive]
def widget : DirectiveExpanderOf WidgetCfg
  | {name}, stxs => do
    unless (widgetMarkup.lookup name).isSome do
      throwError s!"unknown widget {name}; expected one of {widgetMarkup.map (·.1)}"
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.widget $(quote name)) #[ $[ $args ],* ])

end DynIntro
