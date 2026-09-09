# Exception in @dataclass constructor argument — `Config(port=raises())`
# evaluates ALL args; exception embedded in field; zombie object created;
# handler unreachable
"""
EXCEPTION IN DATACLASS CONSTRUCTOR ARGUMENT — PARTIAL EVALUATION LOST

The subset allows:
  - @dataclass construction (IN)
  - Function calls as constructor arguments (IN)
  - Functions that may raise exceptions (IN)
  - try/except around construction (IN)

The NOVEL gap: when a @dataclass constructor has multiple arguments
and one of them raises an exception, CPython evaluates arguments
LEFT-TO-RIGHT and raises at the failing argument. The constructor
is NEVER called. But the model may:

  1. Evaluate all arguments (including ones after the exception)
  2. Call the constructor with an exception-tagged value as a field
  3. Produce a ClassInstance with an exception embedded in its attrs

  @dataclass
  class Config:
      host: str
      port: int
      timeout: int

  def get_port() -> int:
      raise ValueError("no port configured")

  def get_timeout() -> int:
      return 30  # This should NEVER execute

  try:
      c = Config(host="localhost", port=get_port(), timeout=get_timeout())
  except ValueError:
      c = Config(host="localhost", port=8080, timeout=30)

CPython behavior:
  1. Evaluates "localhost" → "localhost"
  2. Evaluates get_port() → raises ValueError
  3. get_timeout() is NEVER called (left-to-right, short-circuit on raise)
  4. Config() is NEVER called
  5. Handler catches ValueError, creates fallback Config

Model behavior (if exception-as-value without propagation):
  1. Evaluates "localhost" → from_str("localhost")
  2. Evaluates get_port() → exception(ValueError)
  3. Evaluates get_timeout() → from_int(30)  ← WRONG: should not execute
  4. Calls Config constructor with exception in port field
  5. Produces from_ClassInstance("Config", {"host": "localhost",
     "port": exception(ValueError), "timeout": from_int(30)})
  6. Exception is EMBEDDED in the object, not propagated

This is a specific instance of finding 386 (exception passed as function
argument) but with the additional problem that:
  - The constructor SUCCEEDS (producing a zombie object)
  - Subsequent field access on the zombie reads exception values
  - The try/except handler may be unreachable (exception never propagates)

This is distinct from:
  - Finding 386 (exception as function arg) — general case
  - Finding 390 (multiple exceptions, first wins) — about which exception
  - Finding 340 (__post_init__ dropped) — about post-construction validation
  - Finding 411 (constructor field value unprovable) — about postconditions
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


@dataclass
class Config:
    host: str
    port: int
    timeout: int


def parse_int(s: str) -> int:
    """Simulates int() which may raise ValueError."""
    if s == "bad":
        raise ValueError("invalid integer")
    if s == "42":
        return 42
    if s == "8080":
        return 8080
    return 0


def expensive_computation(n: int) -> int:
    """Should NOT be called if prior arg raises."""
    # In CPython, this is never reached if a prior argument raises
    return n * n * n


def test_second_arg_raises() -> int:
    """Second argument raises — third should not evaluate.
    
    CPython: get_port raises, Config() never called, handler runs
    Model risk: all args evaluated, zombie Config created
    """
    try:
        c: Config = Config(
            host="localhost",
            port=parse_int("bad"),       # raises ValueError
            timeout=expensive_computation(100)  # should NOT run
        )
        return c.port  # should be unreachable
    except ValueError:
        return -1  # CPython reaches here


def test_first_arg_raises() -> int:
    """First argument raises — nothing else evaluates.
    
    CPython: parse_int raises immediately, Point() never called
    Model risk: both args evaluated, zombie Point created
    """
    try:
        p: Point = Point(
            x=parse_int("bad"),  # raises
            y=parse_int("42")   # should NOT run
        )
        return p.x + p.y  # unreachable
    except ValueError:
        return 0


def test_no_exception_normal_path() -> int:
    """No exception — normal construction works.
    
    Both CPython and model should produce Config with correct values.
    """
    c: Config = Config(
        host="localhost",
        port=parse_int("8080"),
        timeout=expensive_computation(3)
    )
    return c.port  # 8080


def test_exception_in_nested_construction() -> int:
    """Exception in argument to nested constructor.
    
    CPython: inner Point raises, outer Config never constructed
    Model risk: inner exception embedded in outer's field
    """
    try:
        c: Config = Config(
            host="localhost",
            port=parse_int("bad"),  # raises here
            timeout=30
        )
        return c.timeout
    except ValueError:
        return -1


def test_handler_uses_exception_info() -> str:
    """Handler must actually execute to produce correct result.
    
    If exception never propagates (stays embedded in zombie object),
    the handler is unreachable and the function returns wrong value.
    """
    result: str = "unknown"
    try:
        c: Config = Config(
            host="localhost",
            port=parse_int("bad"),
            timeout=30
        )
        result = c.host  # unreachable in CPython
    except ValueError:
        result = "caught"  # CPython reaches here
    return result


def main() -> None:
    assert test_second_arg_raises() == -1
    assert test_first_arg_raises() == 0
    assert test_no_exception_normal_path() == 8080
    assert test_exception_in_nested_construction() == -1
    assert test_handler_uses_exception_info() == "caught"

    print("all passed")


main()
