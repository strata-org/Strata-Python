first: int = 0
second: int = 0
chain_left: int = 0
chain_right: int = 0
loop_index: int = -1


def update_globals():
    global first, second, chain_left, chain_right, loop_index
    first, second = (1, 2)
    chain_left = chain_right = 3
    for loop_index in range(1):
        pass


update_globals()
assert first == 1, "global tuple assignment updates first target"
assert second == 2, "global tuple assignment updates second target"
assert chain_left == 3, "global chained assignment updates first target"
assert chain_right == 3, "global chained assignment updates second target"
assert loop_index == 0, "global for target is bound by iteration"
