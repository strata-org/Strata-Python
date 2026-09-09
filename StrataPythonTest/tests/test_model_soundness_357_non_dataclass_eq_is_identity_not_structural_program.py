# Non-@dataclass `==` is identity not structural — model uses structural
# equality (over-proves); two same-field objects are NOT equal in CPython
"""
NON-@dataclass CLASS == IS IDENTITY, NOT STRUCTURAL — MODEL IS WRONG

CPython: For classes WITHOUT @dataclass, == is IDENTITY comparison.
         Two objects with identical fields are NOT equal unless same object.
         a = Config("x", 1); b = Config("x", 1); a == b → False!

Model:   from_ClassInstance uses structural equality on DictStrAny.
         Two ClassInstances with same classname and same attrs are EQUAL.
         PEq(from_ClassInstance("Config", {h:"x",p:1}),
             from_ClassInstance("Config", {h:"x",p:1})) → True (WRONG!)

Finding 037 identified this issue. This finding provides the CONCRETE
program showing the model OVER-PROVES: it says objects are equal when
CPython says they're not. This is a FALSE POSITIVE — the verifier
accepts code that would fail at runtime.
"""


class Config:
    def __init__(self: "Config", host: str, port: int) -> None:
        self.host: str = host
        self.port: int = port


class Connection:
    def __init__(self: "Connection", url: str) -> None:
        self.url: str = url


def configs_equal(a: Config, b: Config) -> bool:
    """Non-dataclass equality is identity, not structural."""
    return a == b


def find_config(configs: list[Config], target: Config) -> bool:
    """Search using == — identity-based for non-dataclass."""
    for c in configs:
        if c == target:
            return True
    return False


def deduplicate_wrong(items: list[Config]) -> list[Config]:
    """Deduplication using == — won't work for non-dataclass."""
    result: list[Config] = []
    for item in items:
        found: bool = False
        for existing in result:
            if existing == item:
                found = True
        if not found:
            result.append(item)
    return result


def main() -> None:
    # Test 1: same fields, different objects → NOT equal
    a: Config = Config("localhost", 8080)
    b: Config = Config("localhost", 8080)
    # CPython: a == b → False (identity comparison, different objects)
    # Model: PEq → True (structural equality on same attrs) — WRONG!
    assert not configs_equal(a, b)

    # Test 2: same object → equal
    assert configs_equal(a, a)

    # Test 3: find_config with identity semantics
    configs: list[Config] = [a, b]
    # CPython: find_config(configs, a) → True (same object in list)
    assert find_config(configs, a)
    # CPython: find_config(configs, Config("localhost", 8080)) → False
    #          (new object, not in list by identity)
    c: Config = Config("localhost", 8080)
    assert not find_config(configs, c)

    # Test 4: deduplication — all items are "unique" by identity
    items: list[Config] = [
        Config("a", 1),
        Config("a", 1),
        Config("a", 1),
    ]
    deduped: list[Config] = deduplicate_wrong(items)
    # CPython: len == 3 (all different objects, none "equal")
    # Model: len == 1 (structural equality says all are same) — WRONG!
    assert len(deduped) == 3

    print("all passed")


main()
