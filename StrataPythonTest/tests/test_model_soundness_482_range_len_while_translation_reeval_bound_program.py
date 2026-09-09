# FOR i IN RANGE(LEN(lst)) — WHILE-LOOP TRANSLATION RE-EVALUATES len(lst)
"""
FOR i IN RANGE(LEN(lst)) — WHILE-LOOP TRANSLATION RE-EVALUATES len(lst)

The subset allows:
  - for i in range(len(lst)) (IN — common pattern)
  - list.append() in loop body (IN)
  - range with computed argument (IN)

The NOVEL gap: CPython evaluates `range(len(lst))` ONCE at loop entry,
creating a fixed range object. The loop iterates exactly `len(lst)` times
(the length at entry). If the body modifies `lst` (e.g., appends), the
range does NOT grow — iteration count is fixed.

But if the translator converts this to a while-loop:
    i = 0; while i < len(lst): BODY; i += 1
then `len(lst)` is re-evaluated EACH iteration. If the body appends to
lst (with proper rebinding), `len(lst)` grows, and the loop runs MORE
iterations than CPython would.

CPython: lst=[1,2,3]; for i in range(len(lst)): lst.append(0)
         → iterates 3 times (range(3) is fixed), lst becomes [1,2,3,0,0,0]

Model (while translation): i=0; while i < len(lst): lst=lst+[0]; i+=1
         → len(lst) grows each iteration → INFINITE LOOP (or very long)

This is UNSOUND: the model may fail to terminate (report timeout) or
execute more iterations than CPython, proving properties about states
that CPython never reaches.

DISTINCT FROM:
  - Finding 031 (iterator snapshot) — covers reassigning the LIST variable;
    this is about the RANGE BOUND being re-evaluated
  - Finding 305 (range(len) no index axiom) — covers the axiom connecting
    range output to list bounds; this is about ITERATION COUNT
  - Finding 445 (range stop exclusive) — covers off-by-one; this is about
    the bound being DYNAMIC vs FIXED
  - Finding 474 (loop variable reassignment) — covers reassigning i;
    this is about the BOUND changing
"""


def append_in_range_len_loop(lst: list[int]) -> list[int]:
    """Append in loop — range is fixed, loop runs len(lst) times."""
    n: int = len(lst)  # capture length
    for i in range(n):
        lst = lst + [0]  # append (value semantics rebind)
    return lst
    # CPython: lst grows by original length
    # Model (if while i < len(lst)): infinite loop!


def append_in_range_len_direct(lst: list[int]) -> list[int]:
    """Direct range(len(lst)) — the problematic pattern."""
    for i in range(len(lst)):
        lst = lst + [i * 10]
    return lst
    # CPython: [1,2,3] → [1,2,3,0,10,20] (3 appends)
    # Model (while): len grows each iteration → more than 3 appends


def count_iterations_with_append() -> int:
    """Count how many iterations actually execute."""
    lst: list[int] = [1, 2, 3]
    count: int = 0
    for i in range(len(lst)):
        lst = lst + [99]
        count = count + 1
    return count
    # CPython: count == 3 (range(3) is fixed)
    # Model (while): count > 3 (len grows each iteration)


def safe_pattern_capture_length() -> int:
    """Safe pattern: capture length before loop."""
    lst: list[int] = [1, 2, 3, 4, 5]
    n: int = len(lst)
    result: int = 0
    for i in range(n):
        lst = lst + [0]
        result = result + lst[i]
    return result
    # Both CPython and model: n is fixed, loop runs 5 times
    # This pattern is SAFE because n doesn't change


def shrink_in_range_len_loop() -> int:
    """Removing elements — range is still fixed (may cause IndexError)."""
    lst: list[int] = [10, 20, 30, 40, 50]
    total: int = 0
    for i in range(len(lst)):
        total = total + lst[i]
        # If we could remove elements, range would still iterate 5 times
        # potentially causing IndexError on later iterations
    return total


def main() -> None:
    # append_in_range_len_loop: starts with [1,2,3], appends 3 zeros
    result1: list[int] = append_in_range_len_loop([1, 2, 3])
    assert len(result1) == 6, f"Got len={len(result1)}"

    # count_iterations: exactly 3
    assert count_iterations_with_append() == 3

    # safe pattern: captures length
    assert safe_pattern_capture_length() == 1 + 2 + 3 + 4 + 5

    print("All passed")


main()
