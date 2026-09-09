# `super().process()` mutates `self.x` which was narrowed in the caller.
"""
a15_super_mutation.py — super().method() mutates the narrowed field.

isinstance narrows self.x to int. Then super().process() is called, which
mutates self.x to str. mypy doesn't consider super() calls as potential
narrowing invalidators.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Base:
    def __init__(self) -> None:
        self.x: int | str = 42

    def process(self) -> None:
        self.x = "processed"

class Child(Base):
    def do_work(self) -> int:
        if isinstance(self.x, int):
            super().process()  # calls Base.process which sets self.x = "processed"
            return self.x - 1  # mypy: int. Runtime: str - int → TypeError
        return 0

def main() -> None:
    Child().do_work()

if __name__ == "__main__":
    main()
