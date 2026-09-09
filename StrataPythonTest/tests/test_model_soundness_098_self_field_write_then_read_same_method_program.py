# `self.x = v; return self.x` — read after write in same method sees stale
# value if self not rebound
"""
When a method writes to self.x and then reads self.x in the same method,
the read must see the written value. Under value semantics, `self` is a
from_ClassInstance value. Writing `self.x = v` creates a NEW ClassInstance
with updated attrs. If the translator doesn't rebind `self` to the new
value, subsequent reads of `self.x` see the OLD value.
"""
from dataclasses import dataclass


@dataclass
class Account:
    balance: int
    transactions: int

    def deposit(self: "Account", amount: int) -> int:
        self.balance = self.balance + amount
        self.transactions = self.transactions + 1
        # Must read the UPDATED balance, not the original
        return self.balance

    def transfer_out(self: "Account", amount: int) -> bool:
        if self.balance >= amount:
            self.balance = self.balance - amount
            self.transactions = self.transactions + 1
            # self.balance here must reflect the subtraction
            return self.balance >= 0
        return False

    def reset(self: "Account") -> int:
        old: int = self.balance
        self.balance = 0
        self.transactions = self.transactions + 1
        # self.balance must be 0 here, not old
        assert self.balance == 0
        return old


def main() -> None:
    acc: Account = Account(balance=100, transactions=0)

    # deposit: writes balance, then reads it
    new_bal: int = acc.deposit(50)
    # CPython: self.balance = 150, returns 150
    # Model (no rebind): self.balance still 100 after write, returns 100
    assert new_bal == 150

    # transfer_out: writes balance, then checks it
    acc2: Account = Account(balance=80, transactions=0)
    ok: bool = acc2.transfer_out(30)
    # CPython: balance becomes 50, 50 >= 0 → True
    # Model (no rebind): reads original 80, 80 >= 0 → True (accidentally correct)
    assert ok == True

    # transfer_out with exact amount
    acc3: Account = Account(balance=50, transactions=0)
    ok2: bool = acc3.transfer_out(50)
    # CPython: balance becomes 0, 0 >= 0 → True
    assert ok2 == True

    # reset: writes 0, then asserts it's 0
    acc4: Account = Account(balance=200, transactions=5)
    old: int = acc4.reset()
    assert old == 200

    print(new_bal, ok, old)


main()
