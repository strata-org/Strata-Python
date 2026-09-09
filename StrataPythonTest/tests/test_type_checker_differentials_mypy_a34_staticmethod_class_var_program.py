# isinstance narrows `cls.data` to int inside a `@classmethod`. A
# `@staticmethod` mutates the class variable through the class name
# (`Registry.data = "reset"`). Mypy doesn't track that `cls.data` and
# `Registry.data` refer to the same storage.
"""
a34_staticmethod_class_var.py — @staticmethod mutates class variable after isinstance narrowing.

isinstance narrows cls.data (accessed via class name) to int.
A @staticmethod mutates the class variable through the class name.
mypy doesn't track that C.data and the narrowed reference are the same.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


class Registry:
    data: int | str = 42

    @staticmethod
    def reset() -> None:
        Registry.data = "reset"

    @classmethod
    def use_data(cls) -> int:
        if isinstance(cls.data, int):
            Registry.reset()  # mutates via class name
            return cls.data - 1  # mypy: int. Runtime: str - int → TypeError
        return 0


def main() -> None:
    Registry.use_data()


if __name__ == "__main__":
    main()
