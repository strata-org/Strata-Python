"""A body-less function must declare what it returns.

`...` marks a declaration with no implementation, so its annotations are its whole
specification. Without a return annotation there is nothing to answer a call
with; falling back to `any` would be sound and invisible, widening every caller
with nothing in the log saying why.

See ../../doc/RECURSION_CONTRACTS.md for what such a contract still lacks: it
states a result but no write set, so a stub that mutates its arguments is not yet
modelled.
"""


def annotated(x: int) -> str: ...


def unannotated(x: int): ...
