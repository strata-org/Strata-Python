# Copyright Strata Contributors
#
#  SPDX-License-Identifier: Apache-2.0 OR MIT

"""PyHard's loop-invariant markers (docs/PythonToDyn.md §6.11), which a program imports with
`from pyhard import loop_invariant, OLD`.

Both do nothing at run time: `loop_invariant` never calls its argument, and `OLD` appears only
inside the lambdas that `loop_invariant` receives, which nobody calls.
"""


def loop_invariant(p, /):
    """States `p`, a lambda with no parameters, as the invariant of the loop right after this
    call; never calls `p`."""


def OLD(x, /):
    """The value of `x` at the function's entry, inside a loop invariant."""
    return x
