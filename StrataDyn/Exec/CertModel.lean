/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Cert
public import StrataDyn.Exec.Link

set_option autoImplicit false

/-!
# Certified models

What the machine needs of a table's rules, at its own token `Run` and its tags, so that a proof
about runs can rely on rules reaching only what they are given:

* `Accounts M`: where the refs of a value of each tag are, and those of the world and of each
  rule's state.  The engine gives refs and closures their meaning, so their accounts are fixed
  (`ref`, `fn`), and the literals that link hold none (linking rejects a ghost's cell).  Every
  other account is the table's: an account that leaves refs out makes the certificates of the
  rules that reach them unprovable, so it fails safe.
* `Accounts.spec`: the machine's answers as a rule's tree sees them, a `Spec` over typings.  A
  request for a region or a call is valid when its arguments and closure are, a cell request
  when its location holds the request's tag, a new cell's ref is valid, and so on.
* `ImplOK`: an operation's wrapper respects every typing under which its operands are valid.
  A pure wrapper's result is valid there; a rule's tree satisfies the machine's spec with a
  valid result, and a looping rule's tree does so again from every valid state.
  `Model.Certified`: every wrapper of the table is `ImplOK`.
* `LModule.RulesOK`: every constant of a linked module holds no ref, and every pure instruction
  and rule tree is `ImplOK`'s; `link_rulesOK` says a certified model's linked modules have it.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-! ## Accounts -/

/-- Where the refs of the machine's values are: of a value of each tag, of the world, and of
the state of each operation's rule, by the operation's key.  A ref's and a closure's are the
engine's; the literals that link hold none (linking rejects a ghost's cell). -/
structure Accounts (M : RunModel) where
  acct : (t : Ty) → M.interp t → List Loc
  world : M.W → List Loc
  st : (key : Nat × Array Ty) → M.St key → List Loc
  ref : ∀ t (x : M.interp t.ref), acct t.ref x = [.cell (M.locOf x) t]
  fn : ∀ ts r (x : M.interp (Ty.fn ts r)),
    acct (Ty.fn ts r) x = if (M.fnOf x).captured = 0 then [] else [.caps (M.fnOf x).captured]
  unit : acct M.unit M.unitVal = []
  bool : ∀ b, acct M.bool (M.ofBool b) = []
  int : ∀ i, acct M.int (M.ofInt i) = []
  float : ∀ x, acct M.float (M.ofFloat x) = []
  str : ∀ s, acct M.str (M.ofStr s) = []

namespace Accounts

variable {M : RunModel} (A : Accounts M)

/-- The value `x` of tag `t` is valid in `S`. -/
def ValOK (S : Typing) (t : Ty) (x : M.interp t) : Prop := S.AllValid (A.acct t x)

/-- A tagged value is valid in `S`. -/
abbrev DynOK (S : Typing) (d : Dyn M.interp) : Prop := A.ValOK S d.1 d.2

/-- Each of a payload's values is valid in `S`. -/
def ArgsOK (S : Typing) : {ts : List Ty} → Args M.interp ts → Prop
  | _, .nil => True
  | _, .cons x xs => A.ValOK S _ x ∧ ArgsOK S xs

/-- An exit's payload is valid in `S`. -/
def ExitOK (S : Typing) : {ps : List (List Ty)} → Exit M.interp ps → Prop
  | _, .here a => A.ArgsOK S a
  | _, .there e => ExitOK S e

/-- An exit of a rule's tree is valid in `S`: its payload, or the state it runs again with,
which `stOK` says of. -/
def OutOK {ps : List (List Ty)} {St : Type} (stOK : Typing → St → Prop) (S : Typing) :
    Out M.interp ps St → Prop
  | .exit e => A.ExitOK S e
  | .again s => stOK S s

/-- A rule's result is valid in `S`; a terminal rule has none. -/
def ResOK (S : Typing) : (o : Option Ty) → Res M.interp o → Prop
  | some r, x => A.ValOK S r x
  | none, _ => True

/-- What a request needs in `S`: its arguments, closure, cell or value are valid. -/
def PreOK {rs : List (List Ty × Ty)} (S : Typing) : MReq M.interp rs → Prop
  | .region _ args => A.ArgsOK S args
  | .call sig _ captured args => S.CapValid captured ∧ A.ArgsOK S (Args.ofPayload sig.1 args)
  | .new t v => A.ValOK S t v
  | .get t l => S.Valid l t
  | .set t l v => S.Valid l t ∧ A.ValOK S t v
  | .modify t l f => S.Valid l t ∧ ∀ x, A.ValOK S t x → A.ValOK S t (f x)
  | .bind t v _ _ captured => S.CapValid captured ∧ A.ValOK S t v

/-- What the machine promises of its answer to a request, in `S`. -/
def PostOK {rs : List (List Ty × Ty)} (S : Typing) : (q : MReq M.interp rs) → q.Out Run → Prop
  | .region slot _, o => A.ValOK S (rs.get slot).2 o
  | .call sig .., o => A.ValOK S sig.2 o
  | .new t _, o => S.Valid o.loc t
  | .get t _, o => A.ValOK S t o
  | .set .., _ => True
  | .modify .., _ => True
  | .bind .., o => S.CapValid o.captured

/-- **The machine, as a rule's tree sees it**, for an operation with regions `rs` and
successors `ps` and a rule whose state is an `St`, which `stOK` says is valid: a spec over
typings, which grow by extension. -/
def spec (rs : List (List Ty × Ty)) (ps : List (List Ty)) {St : Type}
    (stOK : Typing → St → Prop) : Spec Typing (MEff M.interp Run M.W rs) (Out M.interp ps St) where
  Ext := Typing.Extends
  Pre := A.PreOK
  Post := A.PostOK
  World S w := S.AllValid (A.world w)
  Exit := A.OutOK stOK

/-- A tree of a rule with regions `rs`, successors `ps`, state validity `stOK` and result tag
`ret` respects `S`: it satisfies the machine's spec, with a valid result. -/
def TreeOK {rs : List (List Ty × Ty)} {ps : List (List Ty)} {St : Type}
    (stOK : Typing → St → Prop) (S : Typing) (ret : Option Ty)
    (t : Tree M.interp Run M.W rs ps St (Res M.interp ret)) : Prop :=
  (A.spec rs ps stOK).Sat (fun S₁ x => A.ResOK S₁ ret x) S t

section
variable {rs : List (List Ty × Ty)} {ps : List (List Ty)} {St : Type}
  {stOK : Typing → St → Prop} {S : Typing} {ret : Option Ty}

/-- A tree that returns respects the typing when its result is valid. -/
theorem treeOK_ret {a : Res M.interp ret} :
    A.TreeOK (rs := rs) (ps := ps) stOK S ret (.ret a) ↔ A.ResOK S ret a :=
  Spec.sat_ret

/-- A tree that exits respects the typing when its exit is valid. -/
theorem treeOK_jump {e : Out M.interp ps St} :
    A.TreeOK (rs := rs) stOK S ret (.stop (.jump e)) ↔ A.OutOK stOK S e :=
  Spec.sat_jump

/-- A tree that makes a request respects the typing when the request is valid and, from every
extension, the tree continues on every valid answer to one that does. -/
theorem treeOK_vis {q : MReq M.interp rs} {k : q.Out Run → Tree M.interp Run M.W rs ps St (Res M.interp ret)} :
    A.TreeOK stOK S ret (.vis q k) ↔ A.PreOK S q ∧
      ∀ S₁, S.Extends S₁ → ∀ o, A.PostOK S₁ q o → A.TreeOK stOK S₁ ret (k o) :=
  Spec.sat_vis

/-- A tree that chooses respects the typing when it does on every choice. -/
theorem treeOK_choose {k : Nat → Tree M.interp Run M.W rs ps St (Res M.interp ret)} :
    A.TreeOK stOK S ret (.choose k) ↔ ∀ n, A.TreeOK stOK S ret (k n) :=
  Spec.sat_choose

/-- A tree that updates the world respects the typing when, from every valid world, it gives a
valid world and continues to a tree that does. -/
theorem treeOK_update {f : M.W → M.W × Tree M.interp Run M.W rs ps St (Res M.interp ret)} :
    A.TreeOK stOK S ret (.update f) ↔ ∀ w, S.AllValid (A.world w) →
      S.AllValid (A.world (f w).1) ∧ A.TreeOK stOK S ret (f w).2 :=
  Spec.sat_update

end

/-- `P` holds of `f` on every operand list of tags `ts` that is valid in `S`. -/
def FnOK (S : Typing) {R : Type} (P : R → Prop) : (ts : List Ty) → Fn M.interp R ts → Prop
  | [], f => P f
  | t :: ts, f => ∀ x, A.ValOK S t x → FnOK S P ts (f x)

/-- `P` holds of `f` on every variadic array that is valid in `S`. -/
def VarOK (S : Typing) {X : Type} (P : X → Prop) : (v : Option Ty) → VarFn M.interp v X → Prop
  | none, f => P f
  | some v, f => ∀ xs : Array (M.interp v), (∀ x ∈ xs.toList, A.ValOK S v x) → P (f xs)

/-- A pure wrapper's outcome is valid in `S`: its result, or its exit. -/
def PureOK (S : Typing) (succs : List (List Ty)) :
    (ret : Option Ty) → (match ret with | some r => M.interp r | none => Exit M.interp succs) → Prop
  | some r, x => A.ValOK S r x
  | none, e => A.ExitOK S e

/-- **An operation's wrapper respects every typing under which its operands are valid**: a pure
wrapper's outcome is valid there, and a rule's tree satisfies the machine's spec, with a valid
result; a looping rule's tree does so again from every valid state. -/
def ImplOK {St : Type} (stOK : Typing → St → Prop) : (s : Shape) → Impl Run M.interp M.W s St → Prop
  | ⟨args, var, ret, succs, _⟩, .pure f =>
    ∀ S, A.FnOK S (A.VarOK S (A.PureOK S succs ret) var) args f
  | ⟨args, var, ret, _, _⟩, .sem f =>
    ∀ S, A.FnOK S (A.VarOK S (A.TreeOK stOK S ret) var) args f
  | ⟨args, var, ret, _, _⟩, .loop f again =>
    (∀ S, A.FnOK S (A.VarOK S (A.TreeOK stOK S ret) var) args f) ∧
      ∀ S, A.FnOK S (A.VarOK S (fun k => ∀ st, stOK S st → A.TreeOK stOK S ret (k st)) var) args
        again

/-- A rule's state is valid in `S` by its operation's account. -/
def StOK (key : Nat × Array Ty) (S : Typing) (s : M.St key) : Prop := S.AllValid (A.st key s)

end Accounts

/-- Operation `o`, at position `k` of `M`'s table, is certified: its wrapper, at every choice
of its type arguments' tags, respects every typing under which its operands are valid, with its
state's account by its key.  The state's validity holds at every proof that the rule's state
type is the key's, so it names no proof that `o` is at `k`. -/
def Model.OpCertified (M : Model) (A : Accounts M.at) (k : Nat) (o : OpImpl M.interp M.W) : Prop :=
  ∀ targs : Vector Ty o.typeArgc,
    A.ImplOK (fun S s => ∀ h : o.St Run targs = M.at.St (k, targs.toArray),
        A.StOK (k, targs.toArray) S (cast h s))
      (o.shape targs) (o.fn Run targs)

/-- **A certified model**: every operation of its table is certified. -/
def Model.Certified (M : Model) (A : Accounts M.at) : Prop :=
  ∀ (k : Nat) (n : Name) (o : OpImpl M.interp M.W), M.ops[k]? = some (n, o) →
    M.OpCertified A k o

/-- The operations of `ops`, from position `k` on, are certified: one conjunct per operation,
so a proof of a table's certificate is a proof per operation. -/
def Model.OpsCertified (M : Model) (A : Accounts M.at) :
    Nat → List (Name × OpImpl M.interp M.W) → Prop
  | _, [] => True
  | k, (_, o) :: ops => M.OpCertified A k o ∧ M.OpsCertified A (k + 1) ops

/-- A table whose operations are certified one by one is certified. -/
theorem Model.certified_of_ops {M : Model} {A : Accounts M.at}
    (h : M.OpsCertified A 0 M.ops.toList) : M.Certified A := by
  have key : ∀ (ops : List (Name × OpImpl M.interp M.W)) (j : Nat), M.OpsCertified A j ops →
      ∀ k n o, ops[k]? = some (n, o) → M.OpCertified A (j + k) o := by
    intro ops
    induction ops with
    | nil => intro _ _ k _ _ hk; exact nomatch hk
    | cons p ops ih =>
      intro j hj k n o hk
      cases k with
      | zero =>
        obtain rfl := Option.some.inj hk
        exact hj.1
      | succ k =>
        have := ih (j + 1) hj.2 k n o hk
        rwa [Nat.add_assoc, Nat.add_comm 1 k] at this
  intro k n o hk
  have := key _ 0 h k n o (by rw [Array.getElem?_toList]; exact hk)
  rwa [Nat.zero_add] at this

/-! ## Linked modules -/

namespace Accounts

variable {M : RunModel} (A : Accounts M)

/-- A rule's tree and its tree from a state, at the operands of `re`, satisfy the machine's spec
with a valid result, at every typing under which the operands and the state are valid. -/
def RerunOK {rs : List (List Ty × Ty)} {ps : List (List Ty)} {ret : Option Ty}
    (re : Rerun M rs ps (Res M.interp ret))
    (f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) (Res M.interp ret)) re.ts) :
    Prop :=
  (∀ S, A.FnOK S (A.TreeOK (A.StOK re.key) S ret) re.ts f) ∧
    ∀ S, A.FnOK S (fun k => ∀ st, A.StOK re.key S st → A.TreeOK (A.StOK re.key) S ret (k st))
      re.ts re.tree

/-- A linked instruction's rule respects every typing under which its operands are valid: a
constant holds no ref, a pure instruction's result is valid, and a rule's tree, and its tree
from a state, satisfy the machine's spec. -/
def InsnOK : LInsn M → Prop
  | .const _ v => A.acct v.1 v.2 = []
  | .pure _ ts r f _ => ∀ S, A.FnOK S (A.ValOK S r) ts f
  | .sem _ _ _ r _ re f _ _ => A.RerunOK (ret := some r) re f
  | .refNew .. | .refGet .. | .refSet .. | .callCode .. => True

/-- A linked terminator's rule respects every typing under which its operands are valid. -/
def TermOK : LTerm M → Prop
  | .case ts _ f _ _ => ∀ S, A.FnOK S (A.ExitOK S) ts f
  | .sem _ _ _ re f _ _ => A.RerunOK (ret := none) re f

end Accounts

/-- **A linked module's rules are certified**: every instruction and terminator of every
function and region. -/
abbrev LModule.RulesOK {M : RunModel} (A : Accounts M) (m : LModule M) : Prop :=
  m.All A.InsnOK A.TermOK

end

end Strata.Dyn.Exec
