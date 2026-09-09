class Base:
    def inherited(self) -> str:
        return "base"


class Middle(Base):
    pass


class Leaf(Middle):
    def local(self) -> int:
        return 3


def use_leaf(value: Leaf) -> tuple[str, int]:
    return value.inherited(), value.local()
