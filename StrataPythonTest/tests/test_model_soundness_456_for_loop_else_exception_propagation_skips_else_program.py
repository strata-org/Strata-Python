# For-loop else clause skipped when exception propagates — model executes else
# because exception doesn't terminate iteration (break-flag unset)
"""
FOR-LOOP ELSE CLAUSE SKIPPED WHEN EXCEPTION PROPAGATES OUT OF BODY

The subset allows:
  - for/else (IN, findings 065/316/330 cover break-based semantics)
  - try/except (IN)
  - raise (IN)

The NOVEL gap: when an EXCEPTION propagates out of the for-loop body
(not caught inside the loop), the else clause must NOT execute.

CPython's rule for for/else:
  - else executes if loop completes normally (exhausts iterable)
  - else does NOT execute if loop exits via break
  - else does NOT execute if loop exits via exception propagation

Existing findings 065/316/330 cover the break case. This finding covers
the EXCEPTION case, which is a distinct control-flow path.

  def find_or_raise(xs: list[int], target: int) -> int:
      for x in xs:
          if x == target:
              return x
          if x < 0:
              raise ValueError("negative element")
      else:
          # Should NOT execute if ValueError propagated
          return -1
      return -1  # unreachable

  find_or_raise([1, 2, -3, 4], 5)
  # CPython: raises ValueError (else never reached)
  # Model: if exception-as-value doesn't terminate loop iteration,
  #         loop "completes" and else executes, returning -1

ROOT CAUSE: The exception-as-value model (finding 274) doesn't terminate
the current loop iteration. The exception value flows through remaining
iterations, and the loop "completes normally" from the model's perspective.
The else clause then executes because no break was seen.

This is distinct from:
  - Finding 065 (for/else break semantics) — that's about break
  - Finding 316 (while/else) — that's about while loops
  - Finding 330 (for/else conditional break) — that's about break in nested if
  - Finding 274 (exception no propagation) — that's the root cause, but
    this finding shows a SPECIFIC consequence: else clause incorrectly executes
"""


def search_validated(xs: list[int], target: int) -> int:
    """Search for target, but validate elements along the way.
    
    CPython: raises ValueError on negative element BEFORE reaching else.
    Model: exception doesn't terminate iteration; else clause executes.
    """
    found: int = -1
    for x in xs:
        if x < 0:
            raise ValueError("negative element found")
        if x == target:
            found = x
            break
    else:
        # This should NOT execute if ValueError was raised
        # It should only execute if loop exhausted without break
        found = 0  # sentinel: "searched all, not found"
    return found


def count_valid_before_target(xs: list[int], target: int) -> int:
    """Count elements before target, raising on invalid data.
    
    The else clause sets a "not found" flag. If an exception propagates,
    neither the break path nor the else path should complete — the
    exception should propagate to the caller.
    """
    count: int = 0
    for x in xs:
        if x > 1000:
            raise ValueError("element too large")
        if x == target:
            break
        count += 1
    else:
        # "target not found" — only valid if loop completed normally
        count = -1
    return count


def first_valid_match(xs: list[int], threshold: int) -> int:
    """Find first element above threshold, validating all elements.
    
    Three possible outcomes:
    1. Found: break fires, else skipped, return the element
    2. Not found: loop exhausts, else fires, return -1
    3. Invalid: exception propagates, else MUST NOT fire
    
    Model may conflate cases 2 and 3 if exception doesn't terminate.
    """
    result: int = -1
    for x in xs:
        if x < 0:
            raise ValueError("invalid negative")
        if x > threshold:
            result = x
            break
    else:
        result = -1
    return result


def main() -> None:
    # Case 1: normal completion, else executes
    r1: int = count_valid_before_target([1, 2, 3, 4, 5], 99)
    # target not found, loop exhausts, else sets count=-1
    assert r1 == -1

    # Case 2: break fires, else skipped
    r2: int = count_valid_before_target([1, 2, 3, 4, 5], 3)
    # found target at index 2, count=2 elements before it
    assert r2 == 2

    # Case 3: exception propagates, else must NOT execute
    caught: bool = False
    try:
        r3: int = count_valid_before_target([1, 2, 9999, 4], 4)
        # Should NOT reach here
        assert False
    except ValueError:
        caught = True
    assert caught

    # Verify search_validated
    r4: int = search_validated([1, 2, 3], 2)
    assert r4 == 2  # found via break

    r5: int = search_validated([1, 2, 3], 99)
    assert r5 == 0  # not found, else executed

    caught2: bool = False
    try:
        search_validated([1, -2, 3], 3)
    except ValueError:
        caught2 = True
    assert caught2  # exception propagated, else NOT executed

    print("all passed")


main()
