# Dict key addition during `for k in d:` iteration — CPython raises
# RuntimeError (size changed); model iterates snapshot silently, misses the
# error
"""
DICT MODIFICATION DURING ITERATION — RuntimeError IN CPYTHON, SILENT IN MODEL

The subset allows:
  - for k in d: (dict iteration yields keys — finding 051)
  - d[k] = v (dict assignment)
  - del is OUT, but d[new_key] = v ADDS a key (changes size)

CPython behavior:
  d = {"a": 1, "b": 2}
  for k in d:
      d["new_" + k] = d[k] * 2
  # RAISES RuntimeError: dictionary changed size during iteration

  This is a RUNTIME CHECK in CPython's dict iterator. If the dict's
  internal version counter changes (due to insertion or deletion),
  the iterator raises RuntimeError on the next __next__ call.

Model behavior:
  Under value semantics, the for loop iterates over a SNAPSHOT of keys.
  Adding keys to d inside the loop modifies a COPY (or the rebound d),
  but the iteration continues over the original key set.
  
  Result: the model says the loop completes successfully with the
  modified dict. CPython raises RuntimeError.

This is UNSOUND: the model verifies a program that crashes at runtime.

IMPORTANT DISTINCTION:
  - Modifying VALUES of existing keys during iteration is ALLOWED in CPython:
    for k in d: d[k] = d[k] * 2  ← OK (size unchanged)
  - Adding NEW keys or deleting keys during iteration RAISES RuntimeError:
    for k in d: d["new"] = 1  ← RuntimeError

The model cannot distinguish these cases because:
1. It has no concept of "iteration is in progress"
2. It has no concept of "dict size changed since iteration started"
3. Value semantics means the iterated-over dict is frozen anyway

ROOT CAUSE: The model's for-loop-over-dict translation takes a snapshot
of keys and iterates over that snapshot. This is CORRECT for the key
sequence but MISSES the RuntimeError that CPython raises when the dict
is mutated during iteration.
"""
from dataclasses import dataclass


def modify_value_during_iteration(d: dict[str, int]) -> dict[str, int]:
    """Modify VALUES during iteration — this is ALLOWED in CPython.
    
    CPython: succeeds (size unchanged, only values modified)
    Model: succeeds (value semantics, rebind d each iteration)
    Both agree: this is fine.
    """
    for k in d:
        d[k] = d[k] * 2
    return d


def add_key_during_iteration(d: dict[str, int]) -> dict[str, int]:
    """Add NEW KEY during iteration — RAISES RuntimeError in CPython.
    
    CPython: RuntimeError: dictionary changed size during iteration
    Model: succeeds silently (iterates over snapshot of original keys,
           adds new keys to the rebound dict)
    
    DIVERGENCE: Model says program succeeds. CPython crashes.
    """
    for k in d:
        d["new_" + k] = d[k] * 10
    return d


def conditional_add_during_iteration(d: dict[str, int]) -> dict[str, int]:
    """Conditionally add key during iteration — still raises.
    
    CPython: if the condition is True for ANY key, RuntimeError
    Model: succeeds (adds keys to copy/rebound dict)
    """
    for k in d:
        if d[k] > 5:
            d[k + "_big"] = d[k]
    return d


def safe_pattern_collect_then_modify(d: dict[str, int]) -> dict[str, int]:
    """The CORRECT pattern: collect keys first, then modify.
    
    CPython: succeeds (iteration is over the list, not the dict)
    Model: succeeds
    Both agree.
    """
    keys_to_process: list[str] = []
    for k in d:
        keys_to_process.append(k)
    
    for k in keys_to_process:
        d["new_" + k] = d[k] * 10
    return d


def main() -> None:
    # Value modification is fine in both
    d1: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    result1: dict[str, int] = modify_value_during_iteration(d1)
    assert result1["a"] == 2
    assert result1["b"] == 4

    # Key addition during iteration: CPython raises RuntimeError
    d2: dict[str, int] = {"x": 10, "y": 20}
    raised: bool = False
    try:
        add_key_during_iteration(d2)
    except RuntimeError:
        raised = True
    assert raised == True  # CPython: True. Model: False (no error)

    # Conditional add: also raises
    d3: dict[str, int] = {"a": 1, "b": 10}
    raised2: bool = False
    try:
        conditional_add_during_iteration(d3)
    except RuntimeError:
        raised2 = True
    assert raised2 == True  # CPython: True. Model: False

    # Safe pattern works in both
    d4: dict[str, int] = {"p": 5, "q": 7}
    result4: dict[str, int] = safe_pattern_collect_then_modify(d4)
    assert result4["new_p"] == 50
    assert result4["new_q"] == 70

    print("all passed")


main()
