# A frame target is not a post-state predicate.
@modifies(lambda x: OLD(x))
def f(x: int) -> int:
    ...
