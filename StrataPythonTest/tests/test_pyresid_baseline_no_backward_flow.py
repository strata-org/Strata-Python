def no_backward_flow(flag: bool) -> int:
    value = 1
    before = value + 1
    if flag:
        value = "later"
        after = value + "!"
    return before


result = no_backward_flow(True)
