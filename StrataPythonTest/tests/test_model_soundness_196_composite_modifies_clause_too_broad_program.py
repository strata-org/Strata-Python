# Composite modifies clause too broad — without precise clause, method call
# havocs entire heap; unrelated objects become unprovable
"""
Composite types use `modifies` clauses to specify which heap locations
a method may change. If the modifies clause is TOO BROAD (e.g., "modifies
the entire heap"), then after a method call, the solver knows NOTHING
about any object — even unrelated ones.

Finding 103 identified this: "No modifies clause on methods — after call,
entire heap is havoc'd; unmodified fields become unprovable."

This finding shows the concrete impact: after calling one object's method,
properties of OTHER objects become unprovable because the solver assumes
the entire heap was modified.

Uses ONLY confirmed-accepted constructs: @dataclass, method, int.
"""
from dataclasses import dataclass


@dataclass
class BankAccount:
    owner: str
    balance: int

    def deposit(self: "BankAccount", amount: int) -> "BankAccount":
        return BankAccount(owner=self.owner, balance=self.balance + amount)


@dataclass
class Logger:
    count: int

    def log(self: "Logger", msg: str) -> "Logger":
        return Logger(count=self.count + 1)


def unrelated_objects_preserved() -> bool:
    """After modifying account, logger must be unchanged."""
    account: BankAccount = BankAccount(owner="alice", balance=100)
    logger: Logger = Logger(count=0)

    # Modify account
    account = account.deposit(50)

    # Logger must be unchanged — it's a completely unrelated object
    # If modifies clause is "entire heap", solver can't prove logger.count == 0
    return logger.count == 0 and account.balance == 150


def multiple_objects_one_modified() -> int:
    """Only the modified object changes; others are preserved."""
    a: BankAccount = BankAccount(owner="a", balance=10)
    b: BankAccount = BankAccount(owner="b", balance=20)
    c: BankAccount = BankAccount(owner="c", balance=30)

    # Only modify b
    b = b.deposit(100)

    # a and c must be provably unchanged
    return a.balance + b.balance + c.balance  # 10 + 120 + 30 = 160


def method_call_preserves_locals() -> int:
    """Local variables unrelated to the method call are preserved."""
    x: int = 42
    account: BankAccount = BankAccount(owner="test", balance=0)

    account = account.deposit(10)

    # x must still be 42 — method call can't affect local ints
    return x + account.balance  # 42 + 10 = 52


def main() -> None:
    assert unrelated_objects_preserved() == True
    assert multiple_objects_one_modified() == 160
    assert method_call_preserves_locals() == 52

    print(unrelated_objects_preserved(), multiple_objects_one_modified(),
          method_call_preserves_locals())


main()
