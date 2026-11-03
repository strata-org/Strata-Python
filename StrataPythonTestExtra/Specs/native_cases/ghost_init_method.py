# CPython runs the decorators of a method of a nested class when it imports the model.
class O:
    class I:
        @ghost(name="g", type=int, init=len("ab"))
        def m(self) -> int:
            ...
