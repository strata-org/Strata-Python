"""`super-builtin-base`: `super()` may not delegate into a builtin base.

`ClassInfo.mro` holds user classes only, so once the chain enters a builtin base
there is no next definer to resolve to. Delegating to `ValueError.__init__` would
mean modelling what that constructor does to the instance, which is not modelled.

Measured before this rule existed: this program reported a `guaranteed-error`
abort on `super().__init__(..)` where CPython succeeds. That is sound -- an abort
is a refusal, not a claim -- but it is a confusing diagnosis for an idiomatic
program, so the reason is named instead.
"""


class MyErr(ValueError):
    def __init__(self) -> None:
        super().__init__("boom")
