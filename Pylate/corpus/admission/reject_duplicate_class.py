"""`duplicate-class`: two classes cannot share a name.

The class table is keyed by name and resolves to the first match, so a second
declaration is invisible. Measured before the rule existed, with these exact
bases: `raise E("x")` was routed to the `except KeyError` clause, where CPython
takes `except ValueError`.
"""


class E(KeyError):
    pass


class E(ValueError):
    pass


def which() -> int:
    try:
        raise E("x")
    except KeyError:
        return 1
    except ValueError:
        return 2
