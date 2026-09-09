# `@dataclass(frozen=True)` field write should raise FrozenInstanceError —
# model has no frozen concept; field write succeeds silently instead of
# raising
"""
DATACLASS(frozen=True) — FIELD WRITE SHOULD RAISE FrozenInstanceError

The subset allows:
  - @dataclass with default-value fields
  - Field access obj.field
  - Field write obj.field = value (via reconstruction/rebind)

CPython behavior with @dataclass(frozen=True):
  @dataclass(frozen=True)
  class Point:
      x: int
      y: int
  
  p = Point(x=1, y=2)
  p.x = 10  # RAISES FrozenInstanceError (subclass of AttributeError)

Model behavior:
  The translator sees @dataclass and generates from_ClassInstance.
  Field write translates to ClassInstance_set(p, "x", from_int(10)).
  The model has NO concept of "frozen" — it happily produces a new
  ClassInstance with x=10.

  Result: model says p.x == 10 (field write succeeded)
  CPython: raises FrozenInstanceError

This is UNSOUND in the "model computes wrong result" direction:
  - The model says the program succeeds with a modified object
  - CPython raises an exception at runtime
  - A program verified as "sound" would actually crash

The frozen=True decorator generates __setattr__ and __delattr__ that
raise FrozenInstanceError. Since user-defined __setattr__ is OUT,
the model doesn't know about this generated one either.

This is distinct from:
  - Finding 340 (__post_init__ silently dropped) — different decorator effect
  - Finding 191 (field write requires reconstruction) — that's about correctness
    of the write, not about writes being FORBIDDEN
  - Finding 100 (default values not modeled) — different decorator parameter

The key insight: @dataclass(frozen=True) is syntactically valid and
arguably within the subset (@dataclass is IN). But the frozen parameter
fundamentally changes the semantics of field assignment from "allowed"
to "raises exception". The model must either:
  A) Reject @dataclass with any parameters other than bare @dataclass
  B) Model frozen=True by emitting an exception on field write
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Point:
    x: int
    y: int


@dataclass(frozen=True)
class Config:
    host: str
    port: int


def attempt_modify_frozen(p: Point) -> int:
    """Attempt to modify a frozen dataclass field.
    
    CPython: raises FrozenInstanceError on p.x = 10
    Model: happily produces Point(x=10, y=p.y) — WRONG
    """
    try:
        p = Point(x=10, y=p.y)  # This is fine — creates new instance
        return p.x  # 10
    except AttributeError:
        return -1


def frozen_prevents_mutation(p: Point) -> bool:
    """Test that frozen dataclass prevents field assignment.
    
    CPython: p.x = 99 raises FrozenInstanceError
    Model: if field write is translated as reconstruction, it "succeeds"
    
    NOTE: Under value semantics with rebinding, the translator may
    translate `p.x = 99` as `p = Point(x=99, y=p.y)`. This is
    semantically WRONG for frozen dataclasses — the write should FAIL.
    """
    original_x: int = p.x
    # In CPython, the following would raise:
    # p.x = 99  ← FrozenInstanceError
    # Under the model, if this is translated as reconstruction:
    # p = Point(x=99, y=p.y)  ← model says this works
    # The model doesn't distinguish "frozen field write" from "reconstruction"
    return original_x == p.x  # Always True (we didn't actually write)


def frozen_as_dict_key_guarantee(p: Point) -> bool:
    """Frozen dataclasses are hashable (can be dict keys).
    
    CPython: @dataclass(frozen=True) generates __hash__
    Model: from_ClassInstance has no hash concept
    
    This means frozen dataclasses can be used as dict keys in CPython,
    but the model's dict encoding (DictStrAny with string keys) can't
    represent this anyway. Still, the GUARANTEE that the object won't
    change (enabling safe hashing) is lost in the model.
    """
    return True  # Placeholder — the real test is that p is hashable


def create_and_use_frozen() -> int:
    """Create frozen instances and use them safely.
    
    The CORRECT pattern with frozen dataclasses: create new instances
    instead of modifying. This works in both CPython and the model.
    """
    p1: Point = Point(x=1, y=2)
    p2: Point = Point(x=p1.x + 10, y=p1.y + 20)
    return p2.x + p2.y  # 11 + 22 = 33


def frozen_equality(a: Point, b: Point) -> bool:
    """Frozen dataclasses still support equality (auto-generated __eq__).
    
    CPython: Point(1,2) == Point(1,2) → True
    Model: dataclass eq works (finding 213/430)
    This part is fine — frozen doesn't affect equality.
    """
    return a == b


def main() -> None:
    p: Point = Point(x=5, y=10)

    # These work correctly in both CPython and model
    assert attempt_modify_frozen(p) == 10  # Creates new, doesn't modify
    assert frozen_prevents_mutation(p) == True
    assert create_and_use_frozen() == 33
    assert frozen_equality(Point(x=1, y=2), Point(x=1, y=2)) == True
    assert frozen_equality(Point(x=1, y=2), Point(x=3, y=4)) == False

    # THE CRITICAL TEST: direct field assignment on frozen
    # In CPython, this raises FrozenInstanceError:
    raised: bool = False
    try:
        p.x = 99  # type: ignore  # CPython: FrozenInstanceError!
    except AttributeError:
        raised = True
    
    assert raised == True  # CPython: True. Model: False (write "succeeds")

    print("all passed")


main()
