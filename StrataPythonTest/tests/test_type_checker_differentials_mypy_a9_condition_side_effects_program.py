# Short-circuit `and`, walrus operator, ternary expression, generator
# expression — all can have side effects that invalidate narrowing within the
# same condition.
"""
a9_condition_side_effects.py — The narrowing condition's RHS mutates the narrowed field.

In `isinstance(x.f, int) and x.mutate()`, mypy narrows x.f to int based on
the isinstance, then evaluates x.mutate() which changes x.f. The narrowing
persists because mypy treats the entire `and` expression as establishing the
narrowing for the if-body.

Also: walrus operator in condition, ternary with side effect, genexpr side effect.

mypy --strict: Success (0 errors)
Runtime: TypeError on all variants
"""

class Obj:
    def __init__(self) -> None:
        self.x: int | str = 10

    def check_and_mutate(self) -> bool:
        self.x = "changed"
        return True

# --- Short-circuit: isinstance AND mutating_call ---
def test_short_circuit() -> None:
    o = Obj()
    if isinstance(o.x, int) and o.check_and_mutate():
        # isinstance narrows, then check_and_mutate changes o.x
        result: int = o.x - 1  # TypeError

# --- Walrus in condition ---
class Box:
    def __init__(self) -> None:
        self.val: int | str = 42

    def mutate(self) -> bool:
        self.val = "mutated"
        return True

def test_walrus() -> None:
    b = Box()
    if isinstance(b.val, int) and (flag := b.mutate()):
        result: int = b.val - 1  # TypeError

# --- Ternary with side effect ---
class State:
    def __init__(self) -> None:
        self.x: int | str = 10

    def corrupt(self) -> int:
        self.x = "bad"
        return 0

def test_ternary() -> None:
    s = State()
    if isinstance(s.x, int):
        _ = s.corrupt() if True else 0
        result: int = s.x - 1  # TypeError

# --- Generator expression side effect ---
class G:
    def __init__(self) -> None:
        self.x: int | str = 10

    def produce(self) -> int:
        self.x = "produced"
        return 1

def test_genexpr() -> None:
    g = G()
    if isinstance(g.x, int):
        total: int = sum(g.produce() for _ in range(3))
        result: int = g.x - 1  # TypeError

def main() -> None:
    tests = [
        ("short-circuit 'and'", test_short_circuit),
        ("walrus in condition", test_walrus),
        ("ternary side effect", test_ternary),
        ("genexpr side effect", test_genexpr),
    ]
    for name, fn in tests:
        try:
            fn()
        except TypeError as e:
            print(f"  TypeError via {name}: {e}")

if __name__ == "__main__":
    main()
