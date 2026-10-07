def f(rows):
    return [[(row := c) for c in row] for row in rows]
