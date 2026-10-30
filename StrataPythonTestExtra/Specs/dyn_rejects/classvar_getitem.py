# The class variable binds __getitem__, so the translation can't tell c.k from c["k"], which
# PySpec reads alike.
class C:
    k: int
    def get(self, k: str) -> int:
        ...
    __getitem__ = get

@admit(lambda c, result: c.k > 0)
def f(c: C) -> None:
    ...
