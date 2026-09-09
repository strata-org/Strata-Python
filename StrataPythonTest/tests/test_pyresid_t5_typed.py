from dataclasses import dataclass
from typing import TypedDict


@dataclass
class Pair:
    a: int
    b: str


class Movie(TypedDict):
    title: str
    year: int


class Half:
    def __init__(self, full):
        self.a = 1
        if full:
            self.b = 2


p = Pair(1, "x")
n = p.a + 2
p.b = "z"
u = p.b

m = Movie(title="Alien", year=1979)
t = m["title"]
y = m["year"] + 1
bad = m["director"]

h = Half(0)
c = h.b + 1
