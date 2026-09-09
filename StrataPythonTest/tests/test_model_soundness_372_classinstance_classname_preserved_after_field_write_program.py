# ClassInstance classname preserved after field write — reconstruction must
# keep same classname; isinstance/dispatch must still work
"""
ClassInstance CLASSNAME PRESERVED AFTER FIELD WRITE

CPython: type(obj) doesn't change when you write a field.
         obj.x = 99 → obj is still a Point, not something else.

Model:   Field write reconstructs:
           obj' = from_ClassInstance(classname(obj), new_attrs)

         The classname must be PRESERVED from the original object.
         If the translator uses a literal string, it's correct.
         But if it extracts classname(obj) and the extraction is
         uninterpreted, the solver can't prove classname(obj') == "Point".

         This matters for isinstance checks AFTER field writes:
           obj.x = 99
           isinstance(obj, Point)  # must still be True!

         And for method dispatch after field writes:
           obj.x = 99
           obj.method()  # must dispatch to Point.method, not Hole
"""
from dataclasses import dataclass


@dataclass
class Box:
    value: int
    label: str

    def describe(self: "Box") -> str:
        return self.label + ": " + str(self.value)


def modify_then_check_type() -> bool:
    """After field write, isinstance must still pass."""
    b: Box = Box(10, "test")
    b2: Box = Box(99, b.label)  # modify value, keep label
    # b2 is still a Box — classname must be "Box"
    return isinstance(b2, Box)


def modify_then_call_method() -> str:
    """After field write, method dispatch must still work."""
    b: Box = Box(5, "item")
    b2: Box = Box(100, "updated")
    # b2.describe() must dispatch to Box.describe
    # If classname(b2) is unconstrained, dispatch fails
    return b2.describe()


def chain_modifications() -> bool:
    """Multiple modifications — classname preserved through chain."""
    b: Box = Box(0, "start")
    b = Box(1, b.label)    # modify value
    b = Box(b.value, "mid")  # modify label
    b = Box(b.value + 1, b.label)  # modify value again
    # After all modifications: still a Box
    return isinstance(b, Box) and b.value == 2 and b.label == "mid"


def main() -> None:
    assert modify_then_check_type()
    assert modify_then_call_method() == "updated: 100"
    assert chain_modifications()

    print("all passed")


main()
