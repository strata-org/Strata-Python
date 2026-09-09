# Cross-object method interaction — value semantics is SOUND for functional
# style; caller must rebind all modified objects
"""
When one object's method takes another object as argument and modifies
it, value semantics means the caller's reference to the second object
is unchanged.

Example: `manager.add_employee(emp)` — in CPython, if add_employee
stores emp in manager's list, both manager and the caller's `emp`
reference the same object. Under value semantics, manager gets a COPY.

But more subtly: if a method on object A reads fields from object B
(passed as argument), and B was modified between construction and the
call, the model must have the CURRENT state of B, not a stale copy.

Uses ONLY confirmed-accepted constructs: @dataclass, method, int.
"""
from dataclasses import dataclass


@dataclass
class Account:
    owner: str
    balance: int

    def deposit(self: "Account", amount: int) -> "Account":
        return Account(owner=self.owner, balance=self.balance + amount)


@dataclass
class Bank:
    total_deposits: int

    def process_deposit(self: "Bank", acc: Account, amount: int) -> "Bank":
        """Process a deposit — bank tracks total."""
        # In CPython: acc is modified in place, bank sees it
        # Under value semantics: acc is a copy, modifications don't propagate
        return Bank(total_deposits=self.total_deposits + amount)

    def get_total(self: "Bank") -> int:
        return self.total_deposits


def transfer(src: Account, dst: Account, amount: int) -> Account:
    """Transfer from src to dst. Returns updated dst."""
    # Under value semantics, src is unchanged from caller's perspective
    # (finding 122). But dst IS the return value, so caller gets update.
    return Account(owner=dst.owner, balance=dst.balance + amount)


def multi_object_interaction() -> int:
    acc: Account = Account(owner="alice", balance=100)
    bank: Bank = Bank(total_deposits=0)

    # Deposit: must update BOTH acc and bank
    acc = acc.deposit(50)
    bank = bank.process_deposit(acc, 50)

    # acc.balance should be 150, bank.total_deposits should be 50
    return acc.balance + bank.get_total()


def transfer_between_accounts() -> int:
    a: Account = Account(owner="alice", balance=100)
    b: Account = Account(owner="bob", balance=50)

    # Transfer 30 from a to b
    a = Account(owner=a.owner, balance=a.balance - 30)
    b = Account(owner=b.owner, balance=b.balance + 30)

    return a.balance + b.balance  # 70 + 80 = 150 (conserved)


def stale_reference_problem() -> int:
    """Demonstrates that passing an object doesn't create a live link."""
    acc: Account = Account(owner="carol", balance=200)

    # Modify acc
    acc = acc.deposit(100)  # acc.balance = 300

    # Pass acc to a function that reads it
    # The function sees balance=300 (current state)
    return acc.balance


def main() -> None:
    # Multi-object interaction
    assert multi_object_interaction() == 200  # 150 + 50

    # Transfer conserves total
    assert transfer_between_accounts() == 150

    # Current state is passed (not stale)
    assert stale_reference_problem() == 300

    # Direct transfer
    a: Account = Account(owner="x", balance=100)
    b: Account = Account(owner="y", balance=50)
    b = transfer(a, b, 25)
    assert b.balance == 75
    assert a.balance == 100  # unchanged (value semantics — correct here!)

    print(multi_object_interaction(), transfer_between_accounts(),
          a.balance)


main()
