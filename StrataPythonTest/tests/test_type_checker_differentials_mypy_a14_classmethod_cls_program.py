# classmethod narrows `cls.data: int|str` via isinstance, then `cls.reset()`
# changes it to str.
"""
a14_classmethod_cls.py — classmethod narrows cls.data then mutates it.

isinstance narrowing works on class variables accessed via cls in a classmethod.
A subsequent classmethod call mutates the class variable.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Registry:
    data: int | str = 42

    @classmethod
    def reset(cls) -> None:
        cls.data = "reset"

    @classmethod
    def use_data(cls) -> int:
        if isinstance(cls.data, int):
            cls.reset()  # mutates cls.data to "reset" (str)
            return cls.data - 1  # mypy: int. Runtime: str - int → TypeError
        return 0

def main() -> None:
    Registry.use_data()

if __name__ == "__main__":
    main()
