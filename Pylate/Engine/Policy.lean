/-
The abort policy: which machine-raise categories become aborts (an
obligation, no exceptional continuation) versus modeled raises, with
presets strict/eafp/audit and per-category overrides. Explicit user
raises are never subject to the policy.
-/


namespace Pylate

inductive RMode | abort | model
deriving BEq, Repr, Inhabited

structure Policy where
  preset : String := "strict"
  modes  : List (String × RMode) := []
deriving Inhabited

def policyCategories : List String :=
  ["dispatch", "frozen", "key", "index", "arith", "value", "exhaustion",
   "resource"]

/-- The categories a preset may move to `model`. `contract` is deliberately not
    one of them, and not in `policyCategories` either, so it falls to `aborts`'s
    fail-closed branch under every preset including `audit`.

    Modelling it would mean emitting a `TypeError` edge for a violated parameter
    annotation, and CPython does not check annotations at runtime -- the edge
    would be an exception no execution can produce, sitting in `may_raise` and
    catchable by a handler. The abort says the true thing instead: the analysis
    stops here and owes a proof. -/
def uncatchableCategories : List String := ["contract"]


def Policy.ofPreset (preset : String) (modeled : List String) : Policy :=
  ⟨preset, policyCategories.map (fun c =>
    (c, if modeled.contains c then RMode.model else RMode.abort))⟩

def Policy.strict : Policy := Policy.ofPreset "strict" []
def Policy.eafp : Policy :=
  Policy.ofPreset "eafp" ["key", "value", "exhaustion"]
def Policy.audit : Policy := Policy.ofPreset "audit" policyCategories

/-- Provenance, not exception class, decides what the policy may touch: a
    signal a transfer catches itself is raised with `internal` provenance and
    never reaches this function. An exhaustion that genuinely escapes, as from
    `next(it)` with no default, remains abortable. -/
def Policy.aborts (pol : Policy) (cat : String) : Bool :=
  if cat == "user" then false else
  match pol.modes.find? (·.1 == cat) with
  | some (_, m) => m == RMode.abort
  | none => true

def Policy.override (pol : Policy) (cat : String) (m : RMode) : Policy :=
  { pol with modes := pol.modes.map (fun (c, old) =>
      (c, if c == cat then m else old)) }

/-- The category of a machine-raised exception class. Total: anything
    unlisted is treated as user-level and never aborts. -/
def excCategory : String → String
  | "TypeError" | "AttributeError" | "NameError" | "UnboundLocalError" =>
    "dispatch"
  | "FrozenInstanceError" => "frozen"
  | "KeyError" => "key"
  | "IndexError" => "index"
  | "ZeroDivisionError" | "OverflowError" => "arith"
  | "ValueError" => "value"
  | "StopIteration" => "exhaustion"
  | "RecursionError" | "MemoryError" => "resource"
  | _ => "user"

end Pylate
