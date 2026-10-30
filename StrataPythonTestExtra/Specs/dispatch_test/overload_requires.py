from typing import Literal, overload


class S:
    def go(self) -> None:
        ...


# Wrong today: the @requires of this top-level @overload stub is dropped with a warning
# that is not fatal, so a call that breaks it verifies.
@overload
@requires(lambda service_name: len(service_name) > 100)
def connect(service_name: Literal["s"]) -> S:
    ...
