# laundering via `relation.rs:1093`) and door 2 (flow/narrowing). No dynamic
# type (`Unknown`/`Todo`/`Any`) and no `todo_type!` site is involved.
def make() -> tuple[int, ...]:
    return (1,)        # returns 1 element
a, b = make()          # statically: tuple[int, ...] -> 2 targets
print(a + b)           # runtime: ValueError: not enough values to unpack
