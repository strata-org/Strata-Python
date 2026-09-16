from typing import List


# Dynamic non-dict subscripts are dropped with a subject warning.
def index_into_list(Keys: List[str], I: int) -> None:
    assert len(Keys[I]) >= 1, 'this assertion is dropped'
