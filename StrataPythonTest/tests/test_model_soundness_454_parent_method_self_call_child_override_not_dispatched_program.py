# Parent method calls `self.method()`, child overrides that method — model
# uses static dispatch (parent's version); CPython uses virtual dispatch
# (child's override)
"""
PARENT METHOD CALLS self.method() — CHILD OVERRIDE NOT DISPATCHED

The subset allows:
  - Single inheritance (IN)
  - Method override in child class (IN, finding 055/375)
  - Method calling another method on self (IN, finding 247)

The NOVEL gap: a PARENT method calls self.other_method(), and the
CHILD overrides other_method(). In CPython, the parent's call dispatches
to the child's override (virtual dispatch). In the model, the parent's
call dispatches to the PARENT's version (static dispatch).

This is the "template method pattern" — extremely common in OOP:

  class Base:
      def template(self) -> str:
          return self.step()  # should dispatch to child's step()
      def step(self) -> str:
          return "base"

  class Child(Base):
      def step(self) -> str:
          return "child"

  Child().template()
  # CPython: "child" (self.step() dispatches to Child.step)
  # Model:  "base"  (self.step() dispatches to Base.step — WRONG)

ROOT CAUSE: When translating Base.template(), the translator sees
self.step() and translates it as Base_step(self) (static dispatch
based on the class where the method is defined). It doesn't know
that self might be a Child instance at runtime.

This is distinct from:
  - Finding 055 (method override no virtual dispatch) — that's about
    EXTERNAL calls: caller.method() on a parent-typed variable
  - Finding 375 (classname-based dispatch) — that's about the dispatch
    mechanism, not the internal-call scenario
  - Finding 247 (method calling another method on self) — that's about
    the SAME class, not cross-class dispatch
  - Finding 313 (inherited method not found on child) — that's about
    finding the method at all, not about override dispatch

The template method pattern is one of the most common OOP patterns.
If the model can't handle it, a large class of programs is unsound.
"""
from dataclasses import dataclass


@dataclass
class Formatter:
    prefix: str

    def format_value(self: "Formatter", value: int) -> str:
        """Template method: calls self.transform() which child overrides."""
        transformed: str = self.transform(value)
        return self.prefix + ": " + transformed

    def transform(self: "Formatter", value: int) -> str:
        """Base implementation — child overrides this."""
        return str(value)


@dataclass
class HexFormatter(Formatter):
    """Child that overrides transform to produce hex strings."""

    def transform(self: "HexFormatter", value: int) -> str:
        """Override: format as hex-like string."""
        # Simple hex-like formatting without using hex() builtin
        if value == 0:
            return "0x0"
        result: str = ""
        n: int = value
        while n > 0:
            digit: int = n % 16
            if digit < 10:
                result = str(digit) + result
            else:
                # a=10, b=11, etc — simplified
                result = "?" + result
            n = n // 16
        return "0x" + result


@dataclass
class DoubleFormatter(Formatter):
    """Child that overrides transform to double the value."""

    def transform(self: "DoubleFormatter", value: int) -> str:
        """Override: show doubled value."""
        return str(value * 2)


@dataclass
class Validator:
    min_val: int
    max_val: int

    def validate(self: "Validator", x: int) -> bool:
        """Template: calls self.check() which child can override."""
        if x < self.min_val:
            return False
        if x > self.max_val:
            return False
        return self.check(x)

    def check(self: "Validator", x: int) -> bool:
        """Base: no additional check."""
        return True


@dataclass
class EvenValidator(Validator):
    """Only accepts even numbers within range."""

    def check(self: "EvenValidator", x: int) -> bool:
        """Override: additionally require even."""
        return x % 2 == 0


def test_formatter_dispatch() -> str:
    """Parent's format_value calls self.transform — must dispatch to child.
    
    CPython: HexFormatter.format_value() calls HexFormatter.transform()
    Model:  HexFormatter.format_value() → inherited from Formatter →
            Formatter_format_value(self) → calls Formatter_transform(self)
            → returns str(value) instead of hex string
    """
    fmt: DoubleFormatter = DoubleFormatter(prefix="result")
    # format_value is inherited from Formatter
    # It calls self.transform(value)
    # CPython: dispatches to DoubleFormatter.transform → "10"
    # Model: dispatches to Formatter.transform → "5"
    return fmt.format_value(5)


def test_validator_dispatch() -> bool:
    """Parent's validate calls self.check — must dispatch to child.
    
    CPython: EvenValidator.validate() calls EvenValidator.check()
    Model:  EvenValidator.validate() → inherited from Validator →
            Validator_validate(self) → calls Validator_check(self)
            → returns True (base always passes)
    """
    v: EvenValidator = EvenValidator(min_val=0, max_val=100)
    # validate is inherited from Validator
    # It calls self.check(x)
    # CPython: dispatches to EvenValidator.check → x%2==0
    # Model: dispatches to Validator.check → True (always)
    
    # 7 is odd, in range [0,100] — should FAIL the even check
    return v.validate(7)


def main() -> None:
    # Test formatter: parent calls self.transform, child overrides
    result: str = test_formatter_dispatch()
    # CPython: DoubleFormatter.transform(5) → "10"
    # format_value returns "result: 10"
    assert result == "result: 10"

    # Test validator: parent calls self.check, child overrides
    # 7 is odd → EvenValidator.check returns False
    assert test_validator_dispatch() == False

    # 8 is even → EvenValidator.check returns True
    v: EvenValidator = EvenValidator(min_val=0, max_val=100)
    assert v.validate(8) == True

    # 200 is out of range → fails in parent's validate before check
    assert v.validate(200) == False

    print("all passed")


main()
