class Animal:
    def __init__(self, name: str):
        self.name = name

    def speak(self) -> str:
        return "..."


class Dog(Animal):
    def speak(self) -> str:
        return "woof"


class Counter:
    total: int

    def __init__(self):
        self.total = 0


def greet(a: Animal, times: int) -> str:
    return a.speak()


def bad() -> int:
    return "s"


def maybe(flag: int) -> int:
    if flag:
        return 1


d = Dog("rex")
s = greet(d, 3)
t = greet(d, "x")

x = d if len(s) > 1 else None
v = greet(x, 1)

c = Counter()
c.total = "oops"

w: int = len(s)
z: int = "nope"

b1 = bad()
b2 = maybe(0)
