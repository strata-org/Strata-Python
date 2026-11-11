# str.join over exact lists and tuples, user iterables (gathered first, with iter(iter) and the
# length hint), iterators, sets, the item errors, and join reached inside another operation.
class S(str):
    pass


class It:
    def __init__(self, xs):
        self.xs = list(xs)

    def __iter__(self):
        print("iter")
        return self

    def __next__(self):
        if not self.xs:
            raise StopIteration
        x = self.xs.pop(0)
        print("next", x)
        return x

    def __length_hint__(self):
        print("hint")
        return 2


def show(f, *args):
    try:
        print(repr(f(*args)))
    except TypeError as e:
        print("TypeError", e.args[0])


print(", ".join(["a", "b", "c"]))
print("-".join(("x", S("y"))))
print("".join([]), "+".join(["only"]))
print(".".join(It("abc")))
print("|".join(iter(["aa", "bb"])))
print(",".join(sorted({"b", "a"})))
print(S("/").join(["p", "q"]), type(S("/").join(["p", "q"])).__name__)
print(str.join(":", ["k", "v"]))
show(",".join, 5)
show(",".join, [1])
show(",".join, ["a", 2])
show(",".join, It(["a", 3]))
show(str.join, 1, [])


class P(list):
    p = property(" ".join)


print(P(["m", "n"]).p)
