# @PROPERTY GETTER THAT RAISES EXCEPTION — EXCEPTION LOST, HOLE RETURNED
"""
@PROPERTY GETTER THAT RAISES EXCEPTION — EXCEPTION LOST, HOLE RETURNED

The subset allows:
  - @property (IN)
  - raise in function bodies (IN)
  - try/except (IN)

The NOVEL gap: a @property getter can raise an exception (e.g., ValueError
for invalid state). When the property is accessed, CPython calls the getter
and propagates the exception. But the model translates property access as
DictStrAny_get (finding 424), which returns Hole — the exception is LOST.

This is WORSE than just returning Hole:
  1. The exception path is invisible — try/except around property access
     is unreachable in the model
  2. The model may PROVE that code after the property access is safe,
     when in reality the exception prevents reaching that code
  3. The verifier cannot detect the error condition

CPython: obj.prop → raises ValueError("invalid state")
Model:   obj.prop → DictStrAny_get(attrs, "prop") → Hole (no exception)

DISTINCT FROM:
  - Finding 038 (property not in instance dict) — covers the Hole result
  - Finding 424 (property computed value) — covers the missing computation
  - Finding 222 (property is dynamic) — covers the dispatch mechanism
  - Finding 246 (property with conditional logic) — covers complex getters

  NONE of these address the case where the getter RAISES. They all focus
  on the getter RETURNING a value that the model can't compute. This
  finding is about the getter FAILING — an error path that's completely
  invisible to the model.
"""
from dataclasses import dataclass


@dataclass
class LazyConfig:
    _host: str
    _port: int
    _initialized: bool

    @property
    def host(self: "LazyConfig") -> str:
        if not self._initialized:
            raise RuntimeError("config not initialized")
        return self._host

    @property
    def port(self: "LazyConfig") -> int:
        if not self._initialized:
            raise RuntimeError("config not initialized")
        return self._port


def access_uninitialized() -> str:
    """Property access on invalid state raises."""
    cfg: LazyConfig = LazyConfig(_host="", _port=0, _initialized=False)
    return cfg.host  # RuntimeError!
    # CPython: raises RuntimeError("config not initialized")
    # Model: DictStrAny_get(attrs, "host") → Hole (no error)


def guarded_access(cfg: LazyConfig) -> str:
    """Try/except around property — handler unreachable in model."""
    try:
        return cfg.host
    except RuntimeError:
        return "default"
    # CPython: returns "default" if not initialized
    # Model: cfg.host → Hole, no exception, except handler unreachable
    #         returns Hole (not "default")


@dataclass
class BoundedValue:
    _value: int
    _min: int
    _max: int

    @property
    def value(self: "BoundedValue") -> int:
        if self._value < self._min or self._value > self._max:
            raise ValueError("value out of bounds")
        return self._value


def validate_via_property(v: int) -> bool:
    """Property getter validates invariant — exception signals violation."""
    bv: BoundedValue = BoundedValue(_value=v, _min=0, _max=100)
    try:
        _ = bv.value  # triggers validation
        return True
    except ValueError:
        return False
    # CPython: returns False for v=-1 or v=101
    # Model: bv.value → Hole, no exception, always returns True (UNSOUND)


def exception_prevents_subsequent_code() -> int:
    """Code after raising property is unreachable — model thinks it runs."""
    cfg: LazyConfig = LazyConfig(_host="", _port=0, _initialized=False)
    h: str = cfg.host  # raises! subsequent code unreachable
    # Model: h = Hole, continues executing
    return len(h)  # CPython: never reached. Model: len(Hole) → Hole


def main() -> None:
    # access_uninitialized raises
    try:
        access_uninitialized()
        assert False, "Should have raised"
    except RuntimeError:
        pass

    # guarded_access returns default
    cfg: LazyConfig = LazyConfig(_host="", _port=0, _initialized=False)
    assert guarded_access(cfg) == "default"

    # validate_via_property
    assert validate_via_property(50) == True
    assert validate_via_property(-1) == False
    assert validate_via_property(101) == False

    print("All passed")


main()
