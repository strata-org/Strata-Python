# A contract may reference a ghost declared later in the file.
@admit(lambda result: result >= later)
def read_later() -> int:
    ...


ghost(name="later", type=int, init=0)
