from typing import TypedDict


class Movie(TypedDict):
    title: str
    year: int


m = Movie(title="Alien", year=1979)
t = m["title"]
y = m["year"] + 1
bad = m["director"]
g = m.get("title")
g2 = m.get("director")
n = len(m)
ks = [k for k in m]
m["year"] = 2024
m["extra"] = 1
partial = Movie(title="Blade")

m.clear()
m.pop("title")
victim = m.popitem()
m.update({"stray": 1})
m2 = Movie(title="Heat", year=1995)
m.update(m2)
sd_ok = m.setdefault("title", "z")
m.setdefault("brand_new", 0)
