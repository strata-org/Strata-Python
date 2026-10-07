/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Mantle.Scope
meta import StrataPython.Mantle.Scope

set_option autoImplicit false

/-!
# The scope pass on hand-built ASTs

Programs written as ASTs, without Python.  `StrataPythonTestExtra/PyScopeTest.lean` runs
the pass on parsed `.py` files and compares it with CPython's `symtable`.
-/

namespace StrataPython.Mantle.PyScopeTest

open StrataDDM (SourceRange Ann)
open StrataPython (stmt expr arguments comprehension)
open StrataPython.Mantle.PyScope

private meta def ann {α : Type} (a : α) : Ann α SourceRange := ⟨.none, a⟩

private meta def load (x : String) : expr SourceRange := .Name .none (ann x) (.Load .none)

private meta def store (x : String) : expr SourceRange := .Name .none (ann x) (.Store .none)

private meta def noArgs : arguments SourceRange :=
  .mk_arguments .none (ann #[]) (ann #[]) (ann none) (ann #[]) (ann #[]) (ann none) (ann #[])

/-- `def name(): body`. -/
private meta def defn (name : String) (body : Array (stmt SourceRange)) : stmt SourceRange :=
  .FunctionDef .none (ann name) noArgs (ann body) (ann #[]) (ann none) (ann none) (ann #[])

/-- `x = e`. -/
private meta def assign (x : String) (e : expr SourceRange) : stmt SourceRange :=
  .Assign .none (ann #[store x]) e (ann none)

/-- `return e`. -/
private meta def ret (e : expr SourceRange) : stmt SourceRange := .Return .none (ann (some e))

/-- `for target in iter`, as a comprehension clause. -/
private meta def clause (target : String) (iter : expr SourceRange) :
    comprehension SourceRange :=
  .mk_comprehension .none (store target) iter (ann #[]) (.IntPos .none (ann 0))

/-- `[elt for target in iter]`. -/
private meta def listComp (elt : expr SourceRange) (target : String)
    (iter : expr SourceRange) : expr SourceRange :=
  .ListComp .none elt (ann #[clause target iter])

/-- `(elt for target in iter)`. -/
private meta def genExp (elt : expr SourceRange) (target : String)
    (iter : expr SourceRange) : expr SourceRange :=
  .GeneratorExp .none elt (ann #[clause target iter])

/-- `lambda: body`. -/
private meta def lam (body : expr SourceRange) : expr SourceRange := .Lambda .none noArgs body

private meta def run (stmts : Array (stmt SourceRange)) : IO Unit :=
  IO.print (analyze stmts).format

-- A closure: `x` is a cell of `f` and free in `g`; `y` is global implicit.
/--
info: module
  f: local (assigned)
  function f
    x: cell (assigned)
    y: global implicit (referenced)
    g: local (assigned, referenced)
    function f.<locals>.g
      x: free (referenced)
-/
#guard_msgs in
#eval run #[defn "f" #[assign "x" (load "y"), defn "g" #[ret (load "x")], ret (load "g")]]

-- `nonlocal x` with no enclosing binding is a compile-time error.
/--
info: module
  f: local (assigned)
  function f
    x: free (assigned, referenced, nonlocal)
diagnostics:
  syntax error at ?: no binding for nonlocal 'x' found
-/
#guard_msgs in
#eval run #[defn "f" #[.Nonlocal .none (ann #[ann "x"]), assign "x" (load "x")]]

-- `global x` makes the write go to the module, which records the declaration.
/--
info: module
  f: local (assigned)
  x: global explicit (declared_global)
  function f
    x: global explicit (assigned, declared_global)
    f: global implicit (referenced)
-/
#guard_msgs in
#eval run #[defn "f" #[.Global .none (ann #[ann "x"]), assign "x" (load "f")]]

-- `import a.b.c` binds `a`; `from a.b import x as y` binds `y` to `a.b.x`.
/--
info: module
  import a: module a (loads a.b.c)
  import y: member x of a.b
  a: local (imported)
  y: local (imported)
-/
#guard_msgs in
#eval run #[.Import .none (ann #[.mk_alias .none (ann "a.b.c") (ann none)]),
            .ImportFrom .none (ann (some (ann "a.b")))
              (ann #[.mk_alias .none (ann "x") (ann (some (ann "y")))]) (ann none)]

-- A list comprehension is inlined: its iteration variable `x` is listed in `f`, apart from
-- `f`'s own `x`; its read of `k` leaves `k` a local, with `f`'s flags.  The generator
-- expression is a scope of its own, and its read of `j` makes `j` a cell.
/--
info: module
  f: local (assigned)
  function f
    x: local (assigned, referenced)
    xs: global implicit (referenced)
    k: local (assigned)
    j: cell (assigned)
    a: local (assigned)
    b: local (assigned)
    inlined comprehension f.<locals>.<listcomp>
      params: .0
      .0: local (parameter)
      x: local (assigned, comp_iter)
      k: free (referenced)
    generator expression f.<locals>.<genexpr>
      params: .0
      .0: local (parameter)
      x: local (assigned, comp_iter)
      j: free (referenced)
-/
#guard_msgs in
#eval run #[defn "f" #[assign "x" (load "xs"), assign "k" (load "x"), assign "j" (load "x"),
  assign "a" (listComp (load "k") "x" (load "xs")),
  assign "b" (genExp (load "j") "x" (load "xs"))]]

-- A lambda capturing the iteration variable makes it a cell of the comprehension, and of
-- `f`, flagged `comp_cell`.
/--
info: module
  f: local (assigned)
  function f
    xs: global implicit (referenced)
    x: cell (assigned, comp_iter, comp_cell)
    inlined comprehension f.<locals>.<listcomp>
      params: .0
      .0: local (parameter)
      x: cell (assigned, comp_iter)
      lambda f.<locals>.<lambda>
        x: free (referenced)
-/
#guard_msgs in
#eval run #[defn "f" #[ret (listComp (lam (load "x")) "x" (load "xs"))]]

-- `regionLocals` lists an inlined comprehension's iteration variables.
#guard
  let t := analyze #[assign "a" (listComp (load "y") "x" (load "xs"))]
  t.scopes.map (·.regionLocals) == #[#[], #["x"]]

-- Mangling applies to `__x` inside a class, except dunder names.
#guard mangle (some "_C") "__x" == "_C__x"
#guard mangle (some "C") "__init__" == "__init__"
#guard mangle (some "__") "__x" == "__x"
#guard mangle none "__x" == "__x"

end StrataPython.Mantle.PyScopeTest
