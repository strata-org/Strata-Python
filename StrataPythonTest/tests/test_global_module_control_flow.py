if True:
    branch_value = 3

loop_guard: bool = True
while loop_guard:
    loop_value = 4
    loop_guard = False

left = right = 5
left += 2
first, second = (6, 7)

for loop_index in range(1):
    pass


def read_branch_value() -> int:
    return branch_value


def read_loop_value() -> int:
    return loop_value


def read_loop_index() -> int:
    return loop_index


assert read_branch_value() == 3, "if-body assignment creates module field"
assert read_loop_value() == 4, "while-body assignment creates module field"
assert read_loop_index() == 0, "for target creates module field"
assert left == 7, "module augmented assignment updates module field"
assert right == 5, "chained assignment initializes every module field"
assert first == 6, "destructuring initializes first module field"
assert second == 7, "destructuring initializes second module field"
