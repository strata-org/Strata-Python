# Interaction: two names aliasing one recent location: a strong field
# update through one name is visible through the other; after the
# object escapes into a list the summary loses the strong license.
class Cell:
    def __init__(self, v: int):
        self.v = v


a = Cell(1)
b = a
b.v = 2
after = a.v
holder = [a]
c = Cell(3)
holder.append(c)
c.v = 4
