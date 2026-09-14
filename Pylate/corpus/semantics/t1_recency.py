class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y
        self.prev = None


pts = []
prev = None
i = 0
while i < 3:
    p = Point(i, i + 1)
    p.prev = prev
    d = p.x + p.y
    pts.append(p)
    prev = p
    i = i + 1

q = pts[0]
s = q.x + 1
r = q.prev
