# Interaction: allocation inside a loop inside try, user raise joining
# at the handler: the recency fold and the handler join must compose
# (each iteration demotes the previous Box to the summary; the handler
# sees both recent and summary states joined).
class Box:
    def __init__(self, v: int):
        self.v = v


class Stop(Exception):
    pass


def build(n: int) -> int:
    total = 0
    last = Box(0)
    try:
        for i in range(n):
            b = Box(i)
            last = b
            if i > 2:
                raise Stop()
            total = total + b.v
    except Stop:
        total = total + last.v
    return total


r = build(5)
