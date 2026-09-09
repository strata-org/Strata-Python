# For-loop variable reassignment in body ignored by range iterator — while-
# loop translation uses same variable for iteration state and user binding;
# reassigning i in body derails iteration
"""
FOR-LOOP VARIABLE REASSIGNMENT IGNORED BY RANGE ITERATOR

The subset allows:
  - for loops over range() (IN)
  - Assignment to loop variable in body (IN — no rule forbids it)
  - Arithmetic on loop variable (IN)

The NOVEL gap: reassigning the loop variable inside the body does NOT
affect iteration in CPython (the range iterator maintains its own state),
but if the model translates `for i in range(n)` as a while loop:
    i = 0; while i < n: BODY; i += 1
then reassigning `i` in BODY changes the iteration sequence.

CPython behavior:
  - `for i in range(5)` creates a range_iterator object
  - Each iteration, the iterator produces the NEXT value regardless of i
  - Reassigning i in the body is overwritten at the next iteration start

Model behavior (while-loop translation):
  - `i = 0; while i < n: BODY; i += 1`
  - If BODY contains `i = 99`, then `i += 1` makes i=100, loop exits
  - CPython would continue with i=1, i=2, i=3, i=4

DISTINCT FROM:
  - Finding 031 (reassigning the ITERABLE variable, not the loop variable)
  - Finding 307 (nested loops with same variable name)
  - Finding 460 (sequential loops with same variable)
"""


def count_iterations_with_reassign() -> int:
    """Loop variable reassignment does NOT affect iteration count."""
    count: int = 0
    for i in range(5):
        i = 999  # CPython ignores this; next iteration i is still next range value
        count = count + 1
    # CPython: count == 5 (all 5 iterations execute)
    # Model (while-loop): i=999, i+=1 → i=1000, 1000<5 is False → count==1
    return count


def sum_with_reassign() -> int:
    """Sum of range values despite reassignment in body."""
    total: int = 0
    for i in range(4):
        total = total + i  # uses the iterator-provided value
        i = 0  # CPython: ignored; model: next iteration i=0+1=1 forever
    # CPython: total = 0 + 1 + 2 + 3 = 6
    # Model: total = 0 + 1 + 1 + 1 + ... (infinite or wrong)
    return total


def conditional_reassign(n: int) -> int:
    """Conditional reassignment of loop variable."""
    total: int = 0
    for i in range(n):
        if i == 2:
            i = 0  # CPython: ignored; model: resets counter
        total = total + 1
    # CPython: total == n (always iterates n times)
    # Model: may loop forever (i resets to 0, then 0+1=1, 1<n, ...)
    return total


def main() -> None:
    c: int = count_iterations_with_reassign()
    assert c == 5, f"Expected 5, got {c}"

    s: int = sum_with_reassign()
    assert s == 6, f"Expected 6, got {s}"

    t: int = conditional_reassign(5)
    assert t == 5, f"Expected 5, got {t}"

    print(c, s, t)


main()
