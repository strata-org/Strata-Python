# A tuple assignment shadowing `ghost` makes later calls ordinary expressions.
ghost, other = int, str
ghost(name="collide", type=int, init=0)
