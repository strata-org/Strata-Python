# List growth in while loop — `result = result + [x]` each iteration requires
# rebinding + concat + len axioms
"""
Growing a list in a while loop using concatenation: `lst = lst + [x]`.
Each iteration must rebind `lst` to the new ListAny. The loop condition
`i < n` uses a simple int counter (not len(lst)), so termination is
straightforward. But the model must correctly thread the growing list.

Uses ONLY confirmed-accepted constructs: list create, list concat (+),
while loop, int arithmetic, len(), subscript.
"""


def build_squares(n: int) -> list[int]:
    result: list[int] = []
    i: int = 0
    while i < n:
        result = result + [i * i]
        i = i + 1
    return result


def build_countdown(start: int) -> list[int]:
    result: list[int] = []
    i: int = start
    while i > 0:
        result = result + [i]
        i = i - 1
    return result


def filter_positive(lst: list[int]) -> list[int]:
    result: list[int] = []
    i: int = 0
    while i < len(lst):
        if lst[i] > 0:
            result = result + [lst[i]]
        i = i + 1
    return result


def main() -> None:
    # Build squares
    sq: list[int] = build_squares(5)
    assert len(sq) == 5
    assert sq[0] == 0
    assert sq[1] == 1
    assert sq[4] == 16

    # Countdown
    cd: list[int] = build_countdown(3)
    assert len(cd) == 3
    assert cd[0] == 3
    assert cd[2] == 1

    # Filter
    filtered: list[int] = filter_positive([-1, 2, -3, 4, 0, 5])
    assert len(filtered) == 3
    assert filtered[0] == 2
    assert filtered[1] == 4
    assert filtered[2] == 5

    print(len(sq), sq[4], len(filtered))


main()
