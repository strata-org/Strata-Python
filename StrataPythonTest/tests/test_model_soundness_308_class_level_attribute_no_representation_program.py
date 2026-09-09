# Class-level attributes (`ClassName.attr`) have no representation in
# `from_ClassInstance`; shared mutable state unmodeled
"""
Class-level attributes (class variables) are shared across all instances
and accessible via both the class name and instances. The `from_ClassInstance`
encoding stores only instance attributes in a per-instance DictStrAny.
There is no representation for class-level shared state.

    class Counter:
        count: int = 0  # class-level attribute

        def __init__(self: "Counter", name: str) -> None:
            self.name = name
            Counter.count += 1  # modifies shared class state

The subset says class body annotations are IN. But class-level attributes
that are READ via `ClassName.attr` or WRITTEN via `ClassName.attr = v`
have no representation in `from_ClassInstance(classname, instance_attrs)`.

Uses ONLY confirmed-accepted constructs: class, int, str, method, @dataclass.
"""
from dataclasses import dataclass


@dataclass
class Config:
    host: str
    port: int


# Class-level constant accessed via class name
MAX_CONNECTIONS: int = 100


def get_max() -> int:
    """Access a module-level constant (finding 126/231 covers this)."""
    return MAX_CONNECTIONS


@dataclass
class Tracker:
    name: str
    value: int

    def is_above_threshold(self: "Tracker") -> bool:
        """Method that references a module-level constant."""
        return self.value > MAX_CONNECTIONS


class Registry:
    """Class with a class-level attribute used as shared state."""
    total: int = 0  # class-level attribute

    def __init__(self: "Registry", name: str) -> None:
        self.name: str = name
        Registry.total = Registry.total + 1  # modify class attribute

    def get_total(self: "Registry") -> int:
        """Read class attribute through instance method."""
        return Registry.total


def create_registries() -> int:
    """Each construction increments the shared class counter."""
    r1: Registry = Registry("first")
    r2: Registry = Registry("second")
    r3: Registry = Registry("third")
    # CPython: Registry.total == 3 (shared, incremented 3 times)
    # Model: no representation for Registry.total; likely Hole or 0
    return r3.get_total()


class Versioned:
    """Class where class attribute tracks version across all instances."""
    version: int = 1

    def __init__(self: "Versioned", data: str) -> None:
        self.data: str = data

    def get_version(self: "Versioned") -> int:
        return Versioned.version


def check_version_shared() -> bool:
    """All instances see the same class-level version."""
    a: Versioned = Versioned("alpha")
    b: Versioned = Versioned("beta")
    # Both should see version == 1
    return a.get_version() == b.get_version()


def main() -> None:
    # Class-level attribute incremented by constructor
    # Reset for test isolation (in real code this accumulates)
    Registry.total = 0
    count: int = create_registries()
    assert count == 3  # CPython: 3 registries created

    # Shared version
    assert check_version_shared() == True

    # Module constant via method
    t: Tracker = Tracker("sensor", 150)
    assert t.is_above_threshold() == True

    t2: Tracker = Tracker("sensor2", 50)
    assert t2.is_above_threshold() == False

    print("All class-level attribute tests pass")


main()
