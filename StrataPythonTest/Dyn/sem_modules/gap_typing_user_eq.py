from typing import Optional
class U:
    def __eq__(self, other):
        print("eq")
        return False
    __hash__ = object.__hash__
Optional[U()]
