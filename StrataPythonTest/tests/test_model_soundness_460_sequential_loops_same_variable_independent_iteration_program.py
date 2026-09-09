# Sequential for-loops with same variable — each loop must create fresh
# iteration state; shared counter causes second loop to skip or start wrong
"""
FOR-LOOP ITERATION VARIABLE REUSE ACROSS SEQUENTIAL LOOPS

The subset allows:
  - for loops (IN)
  - Variable reuse (IN, type stability required)
  - Sequential code (IN)

The NOVEL gap: when two sequential for-loops use the SAME iteration
variable name, the second loop must start fresh — the variable's value
from the first loop's last iteration must not "leak" into the second
loop's iteration mechanism.

  xs: list[int] = [10, 20, 30]
  ys: list[int] = [1, 2, 3]
  
  total: int = 0
  for x in xs:
      total += x
  # After first loop: x == 30 (last element), total == 60
  
  for x in ys:
      total += x
  # After second loop: x == 3, total == 66
  # CPython: second loop iterates over ys independently
  # Model risk: if loop variable is not re-initialized, second loop
  #             may start with x==30 or skip iteration

Finding 156 covers loop variable PERSISTING after loop (scope leak).
Finding 307 covers NESTED loops with same variable (inner rebinds outer).
This finding covers SEQUENTIAL loops with same variable — the second
loop must iterate its own iterable independently of the first loop's
final state.

The model risk: if the translator encodes `for x in xs` as:
  x = List_get(xs, 0); body; x = List_get(xs, 1); body; ...
then the second `for x in ys` must reset the index counter. If the
translator uses a shared counter or doesn't reinitialize, the second
loop starts at the wrong position or doesn't iterate at all.

Additionally, if the model uses a "loop variable unchanged" invariant
(e.g., for proving properties about x after the loop), this invariant
from the first loop must not carry into the second loop.
"""
from dataclasses import dataclass


def sum_two_lists(xs: list[int], ys: list[int]) -> int:
    """Sum elements of two lists using same loop variable.
    
    CPython: iterates xs fully, then ys fully, total = sum(xs) + sum(ys)
    Model risk: second loop doesn't iterate if counter not reset
    """
    total: int = 0
    for x in xs:
        total += x
    for x in ys:
        total += x
    return total


def collect_from_two_sources(xs: list[int], ys: list[int]) -> list[int]:
    """Build result list from two sequential loops with same variable.
    
    Tests that the second loop produces fresh iterations.
    """
    result: list[int] = []
    for x in xs:
        result.append(x * 2)
    # result should be [xs[0]*2, xs[1]*2, ...]
    for x in ys:
        result.append(x + 100)
    # result should also contain [ys[0]+100, ys[1]+100, ...]
    return result


def loop_variable_value_between_loops() -> int:
    """The loop variable retains its last value between loops.
    
    After first loop: x == last element of first list
    Before second loop starts: x is still that value
    Second loop then rebinds x to first element of second list
    
    CPython: x == 30 after first loop, x == 1 at start of second loop body
    Model: must correctly rebind x at each iteration start
    """
    xs: list[int] = [10, 20, 30]
    x: int = 0
    for x in xs:
        pass
    # x == 30 here (finding 156)
    saved: int = x  # should be 30
    
    ys: list[int] = [1, 2, 3]
    for x in ys:
        pass
    # x == 3 here
    return saved + x  # 30 + 3 = 33


def different_length_sequential(short: list[int], long: list[int]) -> int:
    """Sequential loops with different-length lists.
    
    Critical test: if the model uses a shared iteration counter,
    the second loop might think it's already past its elements.
    """
    count: int = 0
    for x in short:  # iterates len(short) times
        count += 1
    
    for x in long:  # must iterate len(long) times, not len(long)-len(short)
        count += 1
    
    return count  # should be len(short) + len(long)


def three_sequential_loops() -> int:
    """Three loops with same variable — each must iterate independently."""
    total: int = 0
    
    for i in [1, 2, 3]:
        total += i  # 6
    
    for i in [10, 20]:
        total += i  # 30
    
    for i in [100]:
        total += i  # 100
    
    return total  # 136


def main() -> None:
    # Basic sequential sum
    assert sum_two_lists([1, 2, 3], [4, 5, 6]) == 21

    # Different lengths
    assert sum_two_lists([1], [2, 3, 4, 5]) == 15

    # Empty first list
    assert sum_two_lists([], [1, 2, 3]) == 6

    # Empty second list
    assert sum_two_lists([1, 2, 3], []) == 6

    # Loop variable value between loops
    assert loop_variable_value_between_loops() == 33

    # Different length sequential
    assert different_length_sequential([1, 2], [1, 2, 3, 4, 5]) == 7

    # Three sequential loops
    assert three_sequential_loops() == 136

    # Collect from two sources
    result: list[int] = collect_from_two_sources([1, 2], [3, 4])
    assert result[0] == 2    # 1*2
    assert result[1] == 4    # 2*2
    assert result[2] == 103  # 3+100
    assert result[3] == 104  # 4+100

    print("all passed")


main()
