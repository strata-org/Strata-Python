# Bool as dict key — `d[True]` and `d[1]` are same key in CPython (hash
# equivalence); model's separate tags make them different entries
"""
BOOL AS DICT KEY — True/1 AND False/0 ARE THE SAME KEY IN CPYTHON

CPython: bool is a subclass of int. True==1 and False==0 for hashing.
         d = {1: "one"}; d[True] → "one" (same hash bucket, same key)
         d = {True: "yes", 1: "one"} → {True: "one"} (1 overwrites True)

Model:   DictStrAny only supports string keys (finding 175/029).
         But even if int keys were added, from_bool(True) and from_int(1)
         are DIFFERENT tags. A dict keyed by int would store them separately.
         d[from_bool(True)] and d[from_int(1)] would be different entries.

This is a SUBSET INTERACTION: the subset allows dict[int, V] (finding 217
notes it's promised but unrepresentable). If/when int-keyed dicts are added,
the bool/int key equivalence must be modeled.

For NOW with string keys: d["True"] vs d["1"] are obviously different.
But the CONCEPTUAL gap exists for any future DictIntAny encoding.
"""


def count_with_bool_keys() -> dict[str, int]:
    """Demonstrates the issue using string representation."""
    # This is the closest we can get in the current subset
    # The real issue is with dict[int, V] which is IN but unrepresentable
    d: dict[str, int] = {}
    d[str(True)] = 1   # d["True"] = 1
    d[str(1)] = 2      # d["1"] = 2 — different key!
    return d


def bool_int_key_equivalence() -> int:
    """The actual CPython behavior we can't model."""
    # In CPython: {True: "a", 1: "b"} → {True: "b"} (one entry!)
    # Because hash(True) == hash(1) and True == 1
    #
    # With dict[int, V] (if it existed in model):
    # d = {}; d[1] = "a"; d[True] = "b"
    # CPython: len(d) == 1, d[1] == "b"
    # Model: len(d) == 2 (separate from_int(1) and from_bool(True) entries)

    # Demonstrate with a workaround using int keys conceptually:
    # We use a list to simulate indexed access
    flags: list[bool] = [True, False, True, True]
    count: int = 0
    for f in flags:
        # In CPython: True + True == 2 (bool is int)
        # This part works IF finding 166/261 are fixed
        if f:
            count += 1
    return count


def main() -> None:
    # Test 1: string-key version (works but doesn't show the real bug)
    d: dict[str, int] = count_with_bool_keys()
    assert d[str(True)] == 1
    assert d[str(1)] == 2
    assert len(d) == 2  # These ARE different string keys

    # Test 2: The real issue (bool as int for counting)
    assert bool_int_key_equivalence() == 3

    # Test 3: Direct bool/int equality (the root cause)
    # CPython: True == 1 → True, False == 0 → True
    assert True == 1
    assert False == 0
    assert not (True == 2)

    # Test 4: bool in int list membership
    # CPython: True in [0, 1, 2] → True (because True == 1)
    assert True in [0, 1, 2]
    assert False in [0, 1, 2]

    print("all passed")


main()
