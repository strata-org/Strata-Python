# `"@" in email` gives `containsKey`, which means CPython's `in` for any container;
# here it is a substring test on a `str`.
def f(email: str) -> None:
    assert "@" in email, "email must contain @"
