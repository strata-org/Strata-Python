# Modifies clause missing — heap havoc'd after method call; unrelated objects'
# fields become unconstrained (Composite-specific)
"""
MODIFIES CLAUSE MISSING — HEAP HAVOC'D AFTER METHOD CALL

CPython: a.method() modifies only a's fields.
         b (unrelated object) is unchanged after a.method().

Model (Composite/heap):
  Without a modifies clause, the verifier HAVOCS the entire heap
  after any method call. This means:
  - b.field becomes unconstrained after a.method()
  - Local variables holding field values become stale
  - Any property proved before the call is lost

  With a correct modifies clause:
    modifies { a.field1, a.field2 }
  The verifier knows only a's fields change; b is preserved.

Finding 103 identified this issue. Finding 196 noted the clause is
too broad. This finding shows the CONCRETE impact: after calling
one object's method, an unrelated object's fields become unprovable.
"""
from dataclasses import dataclass


@dataclass
class Account:
    owner: str
    balance: int

    def deposit(self: "Account", amount: int) -> "Account":
        return Account(self.owner, self.balance + amount)

    def get_balance(self: "Account") -> int:
        return self.balance


@dataclass
class Logger:
    count: int

    def log(self: "Logger", msg: str) -> "Logger":
        return Logger(self.count + 1)

    def get_count(self: "Logger") -> int:
        return self.count


def unrelated_objects_preserved() -> bool:
    """After modifying one object, unrelated object unchanged."""
    acc: Account = Account("Alice", 100)
    log: Logger = Logger(0)

    # Modify acc — log should be unchanged
    acc = acc.deposit(50)

    # Under value semantics: log is trivially preserved (independent values)
    # Under heap semantics WITHOUT modifies clause:
    #   deposit() havocs entire heap → log.count is unconstrained
    return log.get_count() == 0 and acc.get_balance() == 150


def multiple_objects_one_modified() -> bool:
    """Three objects, modify one, verify others preserved."""
    a: Account = Account("A", 10)
    b: Account = Account("B", 20)
    c: Account = Account("C", 30)

    # Modify only b
    b = b.deposit(5)

    # a and c must be unchanged
    # Heap havoc: a.balance and c.balance become unconstrained
    return a.balance == 10 and b.balance == 25 and c.balance == 30


def interleaved_operations() -> bool:
    """Interleaved operations on different objects."""
    acc: Account = Account("X", 100)
    log: Logger = Logger(0)

    acc = acc.deposit(10)
    log = log.log("deposit 1")
    acc = acc.deposit(20)
    log = log.log("deposit 2")

    # After all operations: each object reflects only ITS modifications
    return acc.balance == 130 and log.count == 2


def main() -> None:
    assert unrelated_objects_preserved()
    assert multiple_objects_one_modified()
    assert interleaved_operations()

    print("all passed")


main()
