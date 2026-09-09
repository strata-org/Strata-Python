# Chained string methods `s.strip().lower()` — intermediate Hole poisons
# entire chain; all downstream results are Hole
"""
Chained string methods — intermediate Hole poisons the chain.

In CPython:
  "  Hello  ".strip().lower()  → "hello"
  "Hello World".lower().replace("world", "python")  → "hello python"

Each method returns a new string, and the next method is called on it.
This works because each method is pure (finding 310).

But in the Laurel model, string methods have no model (findings 144, 220).
Each returns Hole. When methods are CHAINED:
  s.strip()  → Hole
  Hole.lower()  → calling method on Hole → Hole or error

The intermediate Hole propagates through the chain. Even if ONE method
had a model, the chain breaks if ANY method in it returns Hole.

This is distinct from:
- Finding 144 (individual string methods return Hole)
- Finding 310 (string methods are pure — correct property)
- Finding 159 (method chaining on class instances)

This finding tests that chained string methods compound the Hole problem.

Uses ONLY confirmed-accepted constructs: str methods (strip, lower, upper).
"""


def strip_then_lower(s: str) -> str:
    """Chain: strip whitespace then lowercase."""
    return s.strip().lower()
    # CPython: "  Hello  ".strip().lower() → "hello"
    # Model: strip() → Hole; Hole.lower() → Hole or error


def lower_then_replace(s: str) -> str:
    """Chain: lowercase then replace."""
    return s.lower().replace("world", "python")
    # CPython: "Hello World" → "hello world" → "hello python"
    # Model: lower() → Hole; Hole.replace(...) → Hole


def upper_then_startswith(s: str) -> bool:
    """Chain: uppercase then check prefix."""
    return s.upper().startswith("HELLO")
    # CPython: "hello world".upper().startswith("HELLO") → True
    # Model: upper() → Hole; Hole.startswith(...) → Hole (not bool!)


def multi_chain(s: str) -> str:
    """Three methods chained."""
    return s.strip().lower().replace(" ", "_")
    # CPython: "  Hello World  " → "Hello World" → "hello world" → "hello_world"
    # Model: Hole at first step, everything after is Hole


def chain_with_comparison(s: str) -> bool:
    """Chained result used in comparison — unprovable."""
    cleaned: str = s.strip().lower()
    return cleaned == "hello"
    # CPython: "  Hello  " → True
    # Model: Hole == "hello" → unknown


def main() -> None:
    assert strip_then_lower("  Hello  ") == "hello"
    assert lower_then_replace("Hello World") == "hello python"
    assert upper_then_startswith("hello world") == True
    assert multi_chain("  Hello World  ") == "hello world"
    assert chain_with_comparison("  Hello  ") == True
    assert chain_with_comparison("  World  ") == False
