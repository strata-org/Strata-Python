class Chain:
    def __init__(self):
        self.x0 = "reached"
        self.x1 = None
        self.x2 = None
        self.x3 = None
        self.x4 = None
        self.x5 = None
        self.x6 = None
        self.x7 = None
        self.x8 = None
        self.x9 = None
        self.x10 = None
        self.x11 = None
        self.x12 = None
        self.x13 = None
        self.x14 = None
        self.x15 = None
        self.x16 = None
        self.x17 = None
        self.x18 = None
        self.x19 = None
        self.x20 = None
        self.x21 = None
        self.x22 = None
        self.x23 = None
        self.x24 = None
        self.x25 = None


def advance(chain: Chain) -> None:
    chain.x25 = chain.x24
    chain.x24 = chain.x23
    chain.x23 = chain.x22
    chain.x22 = chain.x21
    chain.x21 = chain.x20
    chain.x20 = chain.x19
    chain.x19 = chain.x18
    chain.x18 = chain.x17
    chain.x17 = chain.x16
    chain.x16 = chain.x15
    chain.x15 = chain.x14
    chain.x14 = chain.x13
    chain.x13 = chain.x12
    chain.x12 = chain.x11
    chain.x11 = chain.x10
    chain.x10 = chain.x9
    chain.x9 = chain.x8
    chain.x8 = chain.x7
    chain.x7 = chain.x6
    chain.x6 = chain.x5
    chain.x5 = chain.x4
    chain.x4 = chain.x3
    chain.x3 = chain.x2
    chain.x2 = chain.x1
    chain.x1 = chain.x0
    return None


def propagate_through_comprehension() -> str:
    chain = Chain()
    values = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
        13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    ]
    effects = [advance(chain) for item in values]
    return chain.x25


result = propagate_through_comprehension()
