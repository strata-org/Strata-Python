# Class field mutation through method call invisible to caller
# (from_ClassInstance is value-typed)
"""
A method mutates self.field. A second reference to the same object
does not see the mutation in the Laurel encoding because ClassInstance
is a value type (from_ClassInstance(name, DictStrAny)).
"""
from dataclasses import dataclass

@dataclass
class Counter:
    count: int

    def increment(self: "Counter") -> None:
        self.count = self.count + 1

def bump(c: Counter) -> None:
    c.increment()

def main() -> None:
    obj: Counter = Counter(count=0)
    bump(obj)
    # CPython: obj.count == 1 (obj and c are the same object)
    # Laurel: obj.count == 0 (c was a copy; mutation to c.count
    #         is invisible to obj because ClassInstance is a value)
    print(obj.count)

main()
