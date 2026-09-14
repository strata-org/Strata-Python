"""`super-form`: `super()` needs a class to be relative to.

Outside a method body there is no owner, so there is no MRO suffix to search.
Also reports `banned-builtin`, because with no owner the callee is lowered
through the ordinary name path where `super` is refused.
"""


def free_function() -> int:
    super().__init__()
    return 1
