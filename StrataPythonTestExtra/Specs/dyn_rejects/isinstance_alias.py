# isinstance of a TypedDict alias rejects the model: CPython raises TypeError for it.
from typing import TypedDict

TD = TypedDict('TD', {'a': int})

@requires(lambda x: isinstance(x, TD))
def f(x: int) -> None:
    ...
