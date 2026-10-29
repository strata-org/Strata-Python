# `while` with `else`, `break` and `continue`.
def loop(n):
    i = 0
    while i < n:
        i += 1
        if i == 2:
            continue
        if i == 5:
            break
    else:
        i = -1
    return i
