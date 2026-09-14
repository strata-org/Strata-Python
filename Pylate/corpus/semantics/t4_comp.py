class Box:
    def __init__(self, v):
        self.v = v


boxes = [Box(1), Box(2)]
vals = [b.v for b in boxes]
same = [b for b in boxes]
wrapped = [Box(b.v + 1) for b in boxes]
names = {b.v for b in boxes}
table = {b.v: b for b in boxes}

first = same[0]
w = first.v + 1
big = [b for b in boxes if b.v > 0]
