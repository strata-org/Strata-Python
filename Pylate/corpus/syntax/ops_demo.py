from dataclasses import dataclass


@dataclass(frozen=True)
class Pt:
    x: int
    y: int


xs = [1, 2, 3]
xs.append(4)
xs.extend([5, 6])
xs.insert(0, 0)
n = xs.count(2)
i = xs.index(2)
xs.sort()
xs.reverse()
ys = xs.copy()
xs.clear()
after_clear = xs.pop()

d = {"a": 1}
d.update({"b": 2})
sd = d.setdefault("c", 3)
items = d.items()
d2 = d.copy()
d.clear()

s = {1, 2}
s.add(3)
s.discard(9)
u = s.union({4})
b = s.issubset(u)
s.clear()

t = (10, "label", None)
first = t[0]
second = t[1]
dyn = t[i]

p = Pt(1, 2)
q = p.x + p.y
p.x = 99

msg = "a-b"
ok = msg.startswith("a")
pos = msg.find("-")
parts = msg.rsplit("-")
