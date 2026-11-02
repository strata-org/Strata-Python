/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.PyTypes

set_option autoImplicit false

/-!
# Closures

`mkClosure` binds a translated function's code to its cells and makes the function object that
holds the closure, its `__name__` and its `__module__`, which it reads from the module's
`__name__` global, as CPython's `MAKE_FUNCTION` does.  It is the one rule that binds cells into a
closure, so it is written directly in `Sem`, with its own proofs.
-/

namespace StrataPython.Dyn.Sem.Rules

open Strata.Dyn.Exec

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- The function object of the closure `f`, named `name`, whose `__module__` is `modName`; a class
body if its name is `<body>`, which no `def` can have. -/
def funcObj (f : FnRef σ [Value, Value] (Except Value Value)) (name : String) (modName : Value) :
    Obj σ :=
  ⟨.builtin .function, none, #[],
    .func { closure := f, name, «module» := modName, classBody := name == "<body>" }⟩

/-- The value of the global `__name__` of `module`: `None` if it has no cell, or its cell is
unassigned. -/
def moduleName (module : String) : Sem ε E Value := do
  match (← getThe (Modules σ)).cell? module "__name__" with
  | some r =>
    match ← readRef r with
    | .undef _ => pure .none
    | v => pure v
  | none => pure .none

/-- A function whose globals are those of the module `module`; its `__module__` is that module's
`__name__` global. -/
@[dyn_sem Py.mkClosure] def mkClosure {cs : List Type} [TagsOf σ cs]
    (code : FnRef σ (cs ++ [Value, Value]) (Except Value Value)) (name module : String)
    (cells : Payload cs) : Sem ε E Value := do
  let f ← bindAll cs code cells
  let m ← moduleName module
  modifyGetThe (ObjStore σ) fun st => (Value.obj st.size, (st.alloc (funcObj f name m)).1)

end

end StrataPython.Dyn.Sem.Rules
