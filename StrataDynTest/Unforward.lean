/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonicalize
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Undoing the canonicalization pass

A test oracle for `Canonicalize.canonicalize`: the pass may only add forwarding blocks and send
transfers to them.  `unforward fn g` takes such a result `g` of `fn` back to `fn`: it checks that
every block of `g` that `fn` lacks is a forwarding block, sends each transfer to one of them on to
the block at the end of its chain of forwarding blocks, and drops them.  A test then checks that
the result prints as `fn` does.  So a pass that sent a transfer to the wrong block, or added a
block that does anything but forward, fails the test.
-/

namespace Strata.Dyn.Unforward

public section

variable {env : Env Unit} {α : Type}

/-- Where the block `b` forwards to, if it is a forwarding block: it has no instructions, and
its terminator is the base's `jump`, with no regions, passing exactly `b`'s parameters. -/
def forwardTarget? (b : Block env α) : Option Label :=
  if b.instrs.isEmpty && b.term.name == bn "jump" && b.term.regions.isEmpty then
    match b.term.succs.toList with
    | [s] => if s.args == b.params.map (·.id) then some s.label else none
    | _ => none
  else none

/-- Where a transfer to `l` ends up, following the forwarding blocks `fwd` at most `fuel` times. -/
def finalTarget (fwd : List (Label × Label)) : (fuel : Nat) → Label → Label
  | 0, l => l
  | f + 1, l =>
    match fwd.find? (·.1 == l) with
    | some (_, t) => finalTarget fwd f t
    | none => l

/-- The body without its blocks whose labels are not in `orig`, and each transfer to one of them
sent to the end of its chain of forwarding blocks. -/
def undoBody (orig : List Label) (bs : List (Block env α)) : List (Block env α) :=
  let fwd := (bs.filter fun b => !orig.contains b.label).filterMap fun b =>
    (forwardTarget? b).map (b.label, ·)
  let kept := bs.filter fun b => orig.contains b.label
  fwd.foldl (init := kept) fun bs (l, _) =>
    Canonicalize.redirect bs (fun _ s => s.label == l) (finalTarget fwd (fwd.length + 1) l)

/-- `g` taken back to `fn`, or `none` if a block of `g` that `fn` lacks is not a forwarding
block. -/
def unforward (fn g : Func env α) : Option (Func env α) :=
  let labels := fn.labels
  if g.allBlocks.all fun b => labels.contains b.label || (forwardTarget? b).isSome then
    let (r, _) := Canonicalize.Region.mapBodies (fun st bs => (undoBody labels bs, st))
      ⟨labels, g.names⟩ ⟨g.blocks⟩
    some { g with blocks := r.blocks }
  else none

/-- Whether `g` taken back to `fn` prints as `fn` does. -/
def undoesTo [HasAttrs α] (fn g : Func env α) : Bool :=
  ((unforward fn g).map (·.format .full)) == some (fn.format .full)

/-- The module `g` with each function taken back to the function at its position in `m`, or
`none` if the two have different numbers of functions, or if a function of `g` has an added block
that is not a forwarding block. -/
def undoneModule [base ≼ env] (m g : Module.Raw env α) : Option (Module.Raw env α) :=
  if m.funcs.size == g.funcs.size then
    ((m.funcs.zip g.funcs).mapM fun p => unforward p.1 p.2).map fun fs => { g with funcs := fs }
  else none

/-- Whether `g` taken back to `m` prints as `m` does, `full` being `m` printed in full. -/
def moduleUndoesTo [base ≼ env] [HasAttrs α] (m g : Module.Raw env α) (full : String := m.format .full) :
    Bool :=
  ((undoneModule m g).map (·.format .full)) == some full

end

end Strata.Dyn.Unforward
