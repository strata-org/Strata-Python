len: int = 1


def read_len() -> int:
    return len


assert read_len() == 1, "Python builtin shadowing remains valid"
