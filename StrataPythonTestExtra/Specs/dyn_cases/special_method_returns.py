# A binary operator's or a comparison's special method, or __length_hint__, may return
# NotImplemented, whatever its declared type; another method may not.
class Money:
    def __add__(self, other: int) -> "Money":
        ...

    def __eq__(self, other: int) -> bool:
        ...

    def __length_hint__(self) -> int:
        ...

    def doubled(self) -> "Money":
        ...
