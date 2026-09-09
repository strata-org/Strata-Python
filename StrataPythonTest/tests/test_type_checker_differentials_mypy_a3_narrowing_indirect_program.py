# isinstance narrowing invalidated through indirect reference chain:
# `m.engine.run()` mutates `m.status` via `self.owner.status`.
"""
a3_narrowing_indirect.py — isinstance narrowing invalidated through indirect reference chain.

mypy --strict: Success (0 errors)
Runtime: AssertionError — variable is str where mypy says int
"""

class Engine:
    def __init__(self, owner: "Machine") -> None:
        self.owner = owner

    def run(self) -> None:
        self.owner.status = "finished"

class Machine:
    def __init__(self) -> None:
        self.status: int | str = 0
        self.engine: Engine = Engine(self)  # back-reference

def main() -> None:
    m = Machine()
    if isinstance(m.status, int):
        m.engine.run()  # mutates m.status via m.engine.owner.status
        code: int = m.status - 1  # mypy: int - int. Runtime: str - int → TypeError

if __name__ == "__main__":
    main()
