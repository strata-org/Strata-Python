# Method returning self — identity vs copy; SOUND for @dataclass (structural
# eq makes identity unobservable); UNSOUND for non-@dataclass
# (positive/negative)
"""
DATACLASS METHOD RETURNING SELF-TYPE CREATES IMPLICIT ALIAS IN CALLER

The subset allows:
  - @dataclass methods (IN)
  - Method returning same type as self (IN)
  - Variable assignment (IN)

The NOVEL gap: when a @dataclass method returns a NEW instance of the
same class (functional update pattern), the model correctly handles this.
But when a method returns `self` UNCHANGED (identity return), the model
creates two independent copies where CPython has one object.

  @dataclass
  class Config:
      host: str
      port: int
      
      def validate(self) -> "Config":
          if self.port < 0:
              raise ValueError("bad port")
          return self  # returns SAME object, not a copy

  c: Config = Config(host="localhost", port=8080)
  c2: Config = c.validate()
  # CPython: c2 IS c (same object, id(c) == id(c2))
  # Model: c2 is a COPY of c (independent value)

For value-semantics @dataclass, this is SOUND because:
  - No mutation means the alias is unobservable
  - c == c2 is True in both CPython and model (structural equality)

BUT: if the method does a CONDITIONAL return — sometimes returning self,
sometimes returning a new instance — the model may diverge:

  def with_port(self, port: int) -> "Config":
      if port == self.port:
          return self  # no change needed
      return Config(host=self.host, port=port)  # new instance

  c: Config = Config("localhost", 8080)
  c2: Config = c.with_port(8080)  # returns self (no-op)
  c3: Config = c.with_port(9090)  # returns new instance
  
  # CPython: c2 is c (same object)
  # Model: c2 is a copy of c (different object, but equal)
  # For @dataclass: c == c2 is True in both → SOUND

  # BUT: if we later check identity (is), it diverges
  # c2 is c → True in CPython, meaningless in model

The REAL problem emerges with the BUILDER PATTERN where the method
modifies self and returns self for chaining:

  class Builder:
      def set_x(self, x: int) -> "Builder":
          self.x = x
          return self  # returns modified self

This is finding 086. But there's a SUBTLER variant: a method that
CONDITIONALLY modifies and returns self vs returns new:

  def ensure_positive(self) -> "Counter":
      if self.value < 0:
          return Counter(value=0)  # new instance
      return self  # same instance, unmodified

In the model, BOTH branches return independent values. The caller
cannot distinguish "self was returned unchanged" from "a new equal
instance was returned." This is SOUND for @dataclass (no mutation),
but the model OVER-PROVES: it can't prove c2 is c (identity), only
that c2 == c (equality).

The UNSOUND case: when the return-self pattern is used with a
non-@dataclass that has identity semantics (finding 357), the model
incorrectly treats the returned value as a fresh independent object.
"""
from dataclasses import dataclass


@dataclass
class Interval:
    lo: int
    hi: int

    def clamp(self: "Interval", value: int) -> int:
        """Pure method — no self-return issues."""
        if value < self.lo:
            return self.lo
        if value > self.hi:
            return self.hi
        return value

    def intersect(self: "Interval", other: "Interval") -> "Interval":
        """Returns new Interval (never self). Model handles correctly."""
        new_lo: int = self.lo
        if other.lo > new_lo:
            new_lo = other.lo
        new_hi: int = self.hi
        if other.hi < new_hi:
            new_hi = other.hi
        if new_lo > new_hi:
            return Interval(lo=0, hi=0)  # empty interval
        return Interval(lo=new_lo, hi=new_hi)

    def widen(self: "Interval", amount: int) -> "Interval":
        """Conditional return: self if amount==0, new instance otherwise.
        
        CPython: if amount==0, returns same object (identity preserved)
        Model: always returns a copy (identity lost, but equality preserved)
        """
        if amount == 0:
            return self  # identity return
        return Interval(lo=self.lo - amount, hi=self.hi + amount)

    def normalize(self: "Interval") -> "Interval":
        """Ensure lo <= hi. Returns self if already normalized.
        
        CPython: returns self when no swap needed
        Model: returns copy of self (equal but not identical)
        """
        if self.lo <= self.hi:
            return self  # already normalized
        return Interval(lo=self.hi, hi=self.lo)  # swap


def test_conditional_self_return() -> bool:
    """Test that conditional self-return produces correct VALUES.
    
    Under value semantics, this is SOUND because:
    - @dataclass __eq__ is structural
    - No mutation after return means alias is unobservable
    
    The model produces correct equality results even though
    it doesn't preserve identity.
    """
    i: Interval = Interval(lo=1, hi=10)
    
    # widen(0) returns self in CPython, copy in model
    i2: Interval = i.widen(0)
    # Both: i == i2 is True (structural equality)
    
    # widen(5) returns new instance in both
    i3: Interval = i.widen(5)
    # Both: i3 == Interval(-4, 15)
    
    return i == i2 and i3.lo == -4 and i3.hi == 15


def test_normalize_idempotent() -> bool:
    """Normalizing twice should produce same result.
    
    CPython: second normalize returns self (already normalized)
    Model: second normalize returns a copy (but equal)
    """
    i: Interval = Interval(lo=10, hi=1)  # inverted
    n1: Interval = i.normalize()  # returns Interval(1, 10)
    n2: Interval = n1.normalize()  # returns self (already ok)
    
    # In both CPython and model: n1 == n2
    return n1 == n2 and n2.lo == 1 and n2.hi == 10


def test_chain_operations() -> bool:
    """Chain of operations where some return self, some return new.
    
    The model must correctly track values through the chain
    regardless of whether each step returns self or new.
    """
    i: Interval = Interval(lo=0, hi=100)
    
    # normalize returns self (already normalized)
    i = i.normalize()
    # widen(0) returns self
    i = i.widen(0)
    # widen(10) returns new
    i = i.widen(10)
    
    return i.lo == -10 and i.hi == 110


def main() -> None:
    assert test_conditional_self_return()
    assert test_normalize_idempotent()
    assert test_chain_operations()

    # Direct value checks
    i: Interval = Interval(lo=3, hi=7)
    assert i.clamp(1) == 3
    assert i.clamp(5) == 5
    assert i.clamp(9) == 7

    # Intersection
    a: Interval = Interval(lo=1, hi=10)
    b: Interval = Interval(lo=5, hi=15)
    c: Interval = a.intersect(b)
    assert c.lo == 5
    assert c.hi == 10

    print("all passed")


main()
