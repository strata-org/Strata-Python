# Method call on exception value — `exception(...).method()` dispatches on
# wrong tag; propagation check needed BEFORE dispatch
"""
METHOD CALL ON EXCEPTION VALUE — NO PROPAGATION BEFORE DISPATCH

CPython: If obj holds an exception (from a raising function), calling
         obj.method() never happens — the exception propagates.

Model:   obj.method() translates to ClassName_method(obj).
         If obj = exception(...), the function receives an exception value
         as its `self` parameter. It then tries to access self.field →
         undefined (finding 347). But BEFORE that, the method DISPATCH
         itself is wrong: looking up "method" on an exception value.

This is the METHOD CALL variant of finding 347 (field access on exception).
The propagation check must happen BEFORE method resolution, not just
before field access inside the method body.
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

    def is_overdrawn(self: "Account") -> bool:
        return self.balance < 0


def create_account(name: str, initial: int) -> Account:
    if initial < 0:
        raise ValueError("initial balance cannot be negative")
    return Account(name, initial)


def deposit_to_new(name: str, initial: int, amount: int) -> Account:
    """Method call on potentially-exception value."""
    acc: Account = create_account(name, initial)
    # If initial < 0: acc = exception(ValueError)
    # Then acc.deposit(amount) dispatches method on exception → undefined
    result: Account = acc.deposit(amount)
    return result


def check_balance(name: str, initial: int) -> int:
    """Another method call pattern."""
    acc: Account = create_account(name, initial)
    return acc.get_balance()


def chained_methods(name: str, initial: int) -> bool:
    """Chain of method calls where first may produce exception."""
    acc: Account = create_account(name, initial)
    acc2: Account = acc.deposit(100)
    return acc2.is_overdrawn()


def main() -> None:
    # Test 1: valid path
    acc: Account = deposit_to_new("Alice", 100, 50)
    assert acc.balance == 150

    # Test 2: method call on exception must propagate
    raised: bool = False
    try:
        bad: Account = deposit_to_new("Bob", -10, 50)
    except ValueError:
        raised = True
    # CPython: raised == True (exception from create_account propagates)
    # Model: exception flows into deposit() as self → undefined behavior
    assert raised

    # Test 3: get_balance on exception
    raised2: bool = False
    try:
        bal: int = check_balance("Carol", -5)
    except ValueError:
        raised2 = True
    assert raised2

    # Test 4: chained methods
    raised3: bool = False
    try:
        result: bool = chained_methods("Dave", -1)
    except ValueError:
        raised3 = True
    assert raised3

    print("all passed")


main()
