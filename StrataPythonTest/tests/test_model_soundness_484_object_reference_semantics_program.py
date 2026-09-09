# Witness: object mutated through a function parameter (aliasing).
# CPython: box.value == 42 (b and box are the SAME object).
# Strata:  value semantics -> mutate() operates on a COPY -> box.value stays 0
#          -> the model diverges from CPython (laurel findings 271, 278, 122).
class Box:
    def __init__(self) -> None:
        self.value: int = 0

def mutate(b: "Box") -> None:
    b.value = 42

box: "Box" = Box()
mutate(box)
assert box.value == 42
