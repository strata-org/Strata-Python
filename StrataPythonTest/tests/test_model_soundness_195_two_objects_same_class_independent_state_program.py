# Two objects same class independent state — value semantics CORRECTLY models
# independence; no fix needed (positive confirmation)
"""
Two objects of the same class must have INDEPENDENT state. Modifying
one must not affect the other. Under value semantics this is AUTOMATIC
(they're separate values). Under reference semantics it's also true
(separate allocations).

This finding verifies that the model correctly handles independent
objects — a case where value semantics is actually CORRECT and matches
CPython. The key test: after `a = MyClass(); b = MyClass()`, modifying
`a` must not affect `b`.

This is the POSITIVE case — value semantics gets this right.
(Contrast with aliasing `b = a` which is OUT of subset.)

Uses ONLY confirmed-accepted constructs: @dataclass, int, function def.
"""
from dataclasses import dataclass


@dataclass
class Wallet:
    balance: int

    def deposit(self: "Wallet", amount: int) -> "Wallet":
        return Wallet(balance=self.balance + amount)

    def withdraw(self: "Wallet", amount: int) -> "Wallet":
        return Wallet(balance=self.balance - amount)


def independent_objects() -> bool:
    """Two wallets are independent — modifying one doesn't affect other."""
    alice: Wallet = Wallet(balance=100)
    bob: Wallet = Wallet(balance=50)

    alice = alice.deposit(30)
    # alice.balance = 130, bob.balance = 50 (unchanged)
    return alice.balance == 130 and bob.balance == 50


def same_initial_state() -> bool:
    """Two objects with same initial values are still independent."""
    w1: Wallet = Wallet(balance=100)
    w2: Wallet = Wallet(balance=100)

    w1 = w1.withdraw(20)
    # w1.balance = 80, w2.balance = 100 (unchanged)
    return w1.balance == 80 and w2.balance == 100


def objects_in_function(w: Wallet) -> Wallet:
    """Function receives a copy — caller's object unchanged."""
    return w.deposit(999)


def caller_independence() -> bool:
    original: Wallet = Wallet(balance=50)
    modified: Wallet = objects_in_function(original)
    # original is unchanged (value semantics — correct!)
    # modified has the new balance
    return original.balance == 50 and modified.balance == 1049


def list_of_independent_objects() -> bool:
    """Objects in a list are independent copies."""
    wallets: list[Wallet] = [
        Wallet(balance=10),
        Wallet(balance=20),
        Wallet(balance=30),
    ]
    # Modify first wallet (using correct read-modify-write pattern)
    w: Wallet = wallets[0]
    w = w.deposit(100)
    wallets[0] = w
    # Other wallets unchanged
    return wallets[0].balance == 110 and wallets[1].balance == 20


def main() -> None:
    assert independent_objects() == True
    assert same_initial_state() == True
    assert caller_independence() == True
    assert list_of_independent_objects() == True

    print(independent_objects(), same_initial_state(),
          caller_independence())


main()
