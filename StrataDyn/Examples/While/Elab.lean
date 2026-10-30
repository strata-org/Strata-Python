/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Dialect
public meta import StrataDDM.TaggedRegions
public meta import Lean.Elab.Term
public meta import StrataDyn.Examples.While.Dialect
public meta import StrataDDM.Integration.Lean.ToExpr
public meta import StrataDDM.Elab
public meta import StrataDDM.Integration.Lean.Env

set_option autoImplicit false

/-!
# `#while … #end`

`#while fun f(…) : T { … } … #end` is the `Program` the text between the tags denotes.  The DDM
parses the text with the `While` dialect, the generated `Command.ofAst` converts each function
to the typed AST, and the term is that AST, annotated with source ranges in the enclosing file.
A parse error is reported at its place in the file.
-/

namespace Strata.Dyn.While.Ast

open Lean Elab Term
open StrataDDM (SourceRange)

public meta section

deriving instance ToExpr for Ty
deriving instance ToExpr for Exp
deriving instance ToExpr for Param
deriving instance ToExpr for Stmt, Body, Else
deriving instance ToExpr for Ast.Command

-- `#while … #end`: a While program.
declare_tagged_region term whileProgram "#while" "#end"

private def shift (base : String.Pos.Raw) (r : SourceRange) : SourceRange :=
  { start := ⟨base.byteIdx + r.start.byteIdx⟩, stop := ⟨base.byteIdx + r.stop.byteIdx⟩ }

/-- Move a message about the snippet at `base` to its place in the enclosing file. -/
private def shiftMessage (full snippet : FileMap) (base : String.Pos.Raw) (m : Message) :
    Message :=
  let move (p : Position) : Position :=
    full.toPosition ⟨base.byteIdx + (snippet.ofPosition p).byteIdx⟩
  { m with pos := move m.pos, endPos := m.endPos.map move }

@[term_elab whileProgram]
def elabWhileProgram : TermElab := fun stx _ => do
  let .atom (.original _ p _ e) _ := stx[1]
    | throwErrorAt stx "#while: expected the program's text"
  let full ← getFileMap
  let snippet := String.Pos.Raw.extract full.source p e
  let snippetMap := FileMap.ofString snippet
  let input : Parser.InputContext :=
    { inputString := snippet, fileName := ← getFileName, fileMap := snippetMap }
  let loaded := (StrataDDM.dialectExt.getState (← getEnv)).loaded
  let dialect : StrataDDM.DialectName := "While"
  if h : dialect ∈ loaded.dialects then
    let leanEnv ← mkEmptyEnvironment 0
    match StrataDDM.Elab.elabProgramRest loaded leanEnv input dialect h 0 input.endPos with
    | .error msgs =>
      for m in msgs do logMessage (shiftMessage full snippetMap p m)
      throwAbortTerm
    | .ok pgm =>
      let funs ← pgm.commands.mapM fun op =>
        match Command.ofAst (op.mapAnn (shift p)) with
        | .ok f => pure f
        | .error msg => throwErrorAt stx "#while: {msg}"
      return toExpr (funs : Program)
  else
    throwErrorAt stx "#while: the While dialect is not loaded"

end

end Strata.Dyn.While.Ast
