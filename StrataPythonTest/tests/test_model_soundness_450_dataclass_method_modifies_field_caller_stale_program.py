# Field write then method call — translator must rebind variable after field
# write; without rebind, method reads stale pre-write ClassInstance
"""
DATACLASS METHOD THAT READS FIELD WRITTEN BY CALLER — STALE SELF

This is a specific interaction between:
  - Finding 191 (field write requires full reconstruction + rebind)
  - Finding 360 (field write then method call — stale self)
  - Finding 234 (method reads field after caller write)

The NOVEL aspect here: a method that RETURNS a value computed from
a field that was JUST WRITTEN by the caller. The caller writes a field,
then immediately calls a method that reads that field. Under value
semantics, the method receives the PRE-WRITE version of self unless
the caller properly rebinds.

CPython (reference semantics):
  obj.x = 10
  result = obj.get_x()  # returns 10 — same object, field was mutated

Model (value semantics):
  obj = ClassInstance_set(obj, "x", from_int(10))  # rebind obj
  result = get_x(obj)  # IF obj was rebound, returns 10 ✓
  
  BUT if the translator doesn't rebind obj after field write:
  obj_old.x = 10  → side effect lost
  result = get_x(obj_old)  # returns OLD value of x

The CRITICAL test: does the translator emit the rebind?
If yes → correct (value semantics works)
If no → stale self, wrong result, UNSOUND

This finding provides a MINIMAL test case that distinguishes correct
translation (with rebind) from incorrect translation (without rebind).
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def get(self: "Counter") -> int:
        return self.value

    def is_positive(self: "Counter") -> bool:
        return self.value > 0


@dataclass
class Accumulator:
    total: int
    count: int

    def average(self: "Accumulator") -> int:
        if self.count == 0:
            return 0
        return self.total // self.count

    def add(self: "Accumulator", x: int) -> "Accumulator":
        return Accumulator(total=self.total + x, count=self.count + 1)


def write_then_read_method(initial: int, new_value: int) -> int:
    """Write a field, then call method that reads it.
    
    CPython: c.value = new_value mutates c; c.get() returns new_value.
    Model (correct): c = Counter(value=new_value); c.get() returns new_value.
    Model (wrong): field write lost; c.get() returns initial.
    """
    c: Counter = Counter(value=initial)
    c = Counter(value=new_value)  # Must rebind! (value semantics)
    return c.get()


def write_then_conditional_method(x: int) -> bool:
    """Write field, then call method that uses it in a condition.
    
    CPython: c.value = x; c.is_positive() checks x > 0.
    Model: if rebind correct, checks x > 0. If stale, checks 0 > 0 = False.
    """
    c: Counter = Counter(value=0)
    c = Counter(value=x)  # Rebind with new value
    return c.is_positive()


def sequential_modifications(start: int) -> int:
    """Multiple writes then method call — only last write matters.
    
    CPython: c.value = start, then +10, then +20; get() returns start+20.
    Model: each write must rebind; method sees latest.
    """
    c: Counter = Counter(value=start)
    c = Counter(value=c.value + 10)
    c = Counter(value=c.value + 20)
    return c.get()


def method_returns_new_then_read(x: int, y: int) -> int:
    """Method returns new object; caller reads field from result.
    
    This tests whether the return value of add() is properly
    connected to subsequent field access.
    
    CPython: acc.add(x) returns new Accumulator; .average() reads it.
    Model: add() returns from_ClassInstance; average() must read its fields.
    """
    acc: Accumulator = Accumulator(total=0, count=0)
    acc = acc.add(x)
    acc = acc.add(y)
    return acc.average()


def chain_write_method_write_method(a: int, b: int) -> int:
    """Interleave field writes and method calls.
    
    Each method call must see the LATEST field values.
    """
    c: Counter = Counter(value=a)
    v1: int = c.get()  # Should be a
    c = Counter(value=b)
    v2: int = c.get()  # Should be b
    return v1 + v2


def main() -> None:
    # Write then read — the fundamental test
    assert write_then_read_method(0, 42) == 42
    assert write_then_read_method(100, 0) == 0

    # Write then conditional
    assert write_then_conditional_method(5) == True
    assert write_then_conditional_method(-3) == False
    assert write_then_conditional_method(0) == False

    # Sequential modifications
    assert sequential_modifications(0) == 30   # 0 + 10 + 20
    assert sequential_modifications(5) == 35   # 5 + 10 + 20

    # Method returns new object
    assert method_returns_new_then_read(10, 20) == 15  # (10+20) // 2

    # Interleaved writes and reads
    assert chain_write_method_write_method(3, 7) == 10  # 3 + 7

    print(write_then_read_method(0, 42),
          sequential_modifications(5),
          method_returns_new_then_read(10, 20))


main()
