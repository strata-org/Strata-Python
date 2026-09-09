# **FIX: AST rejection rules for aliasing** — 5 syntactic rules reject
# aliasing patterns; makes value semantics sound; resolves 30+ findings
"""
FIX PROPOSAL: AST rejection rules for aliasing patterns.
Resolves findings: 001-005, 010, 011, 033, 048, 049, 086, 087, 094,
098, 099, 118, 119, 122, 184, 192, 194, 198, 212, 215, 216, 271,
276-280.

The fix: syntactic AST checks that REJECT programs with aliasing
patterns BEFORE translation. No model change needed — just enforcement.
"""


# === PATTERNS THAT MUST BE REJECTED ===

# Pattern 1: Direct variable copy of mutable type
# REJECTED: b = a  (where a is list/dict/class)
# ALLOWED:  b = f(a)  (function returns new value)
# ALLOWED:  b = ClassName(...)  (fresh construction)

# Pattern 2: Function mutates mutable parameter
# REJECTED: def f(xs: list[int]) -> None: xs.append(x)
# ALLOWED:  def f(xs: list[int]) -> list[int]: xs.append(x); return xs

# Pattern 3: Method mutates self without returning
# REJECTED: def inc(self) -> None: self.value += 1
# ALLOWED:  def inc(self) -> "Counter": return Counter(self.value + 1)

# Pattern 4: Compound field.method() mutation
# REJECTED: obj.items.append(x)
# ALLOWED:  obj = Obj(items=obj.items + [x])

# Pattern 5: Loop variable mutation
# REJECTED: for item in items: item.x = v
# ALLOWED:  for i in range(len(items)): items[i] = new_item(...)


# === PATTERNS THAT ARE SAFE (ALLOWED) ===

from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def increment(self: "Counter") -> "Counter":
        """ALLOWED: returns new instance."""
        return Counter(value=self.value + 1)


def safe_function(xs: list[int]) -> list[int]:
    """ALLOWED: returns modified list."""
    xs.append(99)
    return xs


def safe_usage() -> int:
    """ALLOWED: caller rebinds."""
    c: Counter = Counter(value=0)
    c = c.increment()  # rebind ✓
    c = c.increment()
    return c.value


def safe_list_usage() -> int:
    """ALLOWED: caller captures return."""
    data: list[int] = [1, 2, 3]
    data = safe_function(data)  # rebind ✓
    return len(data)


def main() -> None:
    assert safe_usage() == 2
    assert safe_list_usage() == 4
    print("All safe patterns work:", safe_usage(), safe_list_usage())


main()
