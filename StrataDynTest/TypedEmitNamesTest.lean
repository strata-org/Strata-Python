/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Build.Typed
public import StrataDyn.DDM
import StrataDyn.Env.WF
import StrataDyn.DSL
-- The builder and the printer run as compiled code below.
meta import StrataDyn.Build.Typed
meta import StrataDyn.DDM
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Typed emitters: binder names

An emitter's own binders, the names it generates and the constants it refers to cannot clash
with the names an instruction's signature binds.  Each instruction here is named to clash with
one of them; its signature is pinned where a name changes, and its function is built and
printed.
-/

namespace Strata.Dyn.TypedEmitNamesTest

open Strata.Dyn.Emit

/-- A child of `Base` whose instructions' names clash with the emitter's. -/
public environment Tn extends Base where
  namespace tn
  open base
  /-- Names the emitter generates for itself: a region's parameters' and its entry block's. -/
  insn clash [d0] (d1 bodyBase : d0) (&body (p : d0) (q : Int) : d0) : d0
  /-- Operands and type parameters named after the emitter's own binders, beside their
  renamings. -/
  insn sub [m m_] (result result_ : m) (y : m_) : m
  /-- Names of the constants the emitter refers to. -/
  insn rooted [Strata] (Bind : Strata) (&body (p : Strata) : Strata) : Strata
  insn rootedSwap [Bind] (Strata : Bind) (^k (v : Bind)) : Bind
  end tn

/-- The name `s`. -/
def n (s : String) : Name := .str .base s

/-- What `Emit.func` gives. -/
abbrev Built :=
  Except (Build.FailedFunc Tn.env Unit Unit) ({fn : Func Tn.env Unit // fn.WF} × Unit)

/-- The module `m` of `f`, printed, or why it was not built. -/
private def showMod (f : Built) : String :=
  match f with
  | .error e => toString e
  | .ok (f, _) => match Module.ofChecked (.str .base "m") #[f] () with
    | .ok m => toString m
    | .error _ => "the module is not well formed"

/-! ## Generated names

The emitter names a region's entry block `rBase` and its parameters' values `d0`, `d1`, ….  A
type parameter or operand of one of these names keeps it, and the generated name takes a `_`
suffix. -/

/--
info: Strata.Dyn.TypedEmitNamesTest.Tn.clash {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Tn.env ≼ env] {d0 : TypeExpr env} (d1 bodyBase : Val env d0)
  (body : Val env d0 → Val env Base.Int → Target env [d0] → m Unit) (result : Option Name := none)
  (info : Option α := none) (bodyBase_ : String := "body") : m (Val env d0)
-/
#guard_msgs in #check Tn.clash

/-- `clash(%x : Int)`, the operands given by name. -/
private def clash : Built :=
  Emit.func (n "clash") [(n "x", Base.Int)] Base.Int () fun (.cons x .nil) exit => do
    let% r ← Tn.clash (d1 := x) (bodyBase := x) (bodyBase_ := "loop")
      (body := fun p q exit => do
        let _ ← Base.refNew (result := n "c") q
        Base.jump (exit.bind p))
    ret exit r

/--
info: module m {
  func @clash(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %r.0 : base.Int = tn.clash[base.Int](%x.0, %x.0) {
        loop.0(%p.0 : base.Int, %q.0 : base.Int):
          %c.0 : base.Ref(base.Int) = base.refNew[base.Int](%q.0)
          ret(%p.0)
      }
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod clash)

/-! ## Renamed binders

An operand or type parameter named after one of the emitter's own binders takes `_` suffixes
until it meets no name of the signature; every other name is kept.  So `result` next to
`result_` becomes `result__`, `m` next to `m_` becomes `m__`, and a named argument keeps its
meaning. -/

/--
info: Strata.Dyn.TypedEmitNamesTest.Tn.sub {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]
  [Tn.env ≼ env] {m__ m_ : TypeExpr env} (result__ result_ : Val env m__) (y : Val env m_)
  (result : Option Name := none) (info : Option α := none) : m (Val env m__)
-/
#guard_msgs in #check Tn.sub

/-- `renamed(%b : Bool)`: `sub` of `1`, `2` and `b`, at two types, the second operand given by
name. -/
private def renamed : Built :=
  Emit.func (n "renamed") [(n "b", Base.Bool)] Base.Int () fun (.cons b .nil) exit => do
    let one ← int (n "one") 1
    let two ← int (n "two") 2
    let% r ← Tn.sub one b (result_ := two)
    ret exit r

/--
info: module m {
  func @renamed(%b.0 : base.Bool) -> base.Int {
    entry.0(%b.0 : base.Bool):
      %r.0 : base.Int = tn.sub[base.Int, base.Bool](1, 2, %b.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod renamed)

/-! ## Constants named by the signature

The emitter names every constant from the root, so a type parameter or operand named `Strata`
or `Bind`, the first components of constants it uses, does not shadow them. -/

/-- `rooted(%x : Int)`: both instructions. -/
private def rooted : Built :=
  Emit.func (n "rooted") [(n "x", Base.Int)] Base.Int () fun (.cons x .nil) exit => do
    let kL ← freshLabel [Base.Int] "k"
    let% r ← Tn.rooted x (fun p exit => Base.jump (exit.bind p))
    let% s ← Tn.rootedSwap r kL.goto
    ret exit s
    ret exit (← startBlock₁ kL (n "v"))

/--
info: module m {
  func @rooted(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %r.0 : base.Int = tn.rooted[base.Int](%x.0) {
        body.0(%p.0 : base.Int):
          ret(%p.0)
      }
      %s.0 : base.Int = tn.rootedSwap[base.Int](%r.0) ^k.0()
      ret(%s.0)
    k.0(%v.0 : base.Int):
      ret(%v.0)
  }
}
-/
#guard_msgs in
#eval IO.println (showMod rooted)

end Strata.Dyn.TypedEmitNamesTest
