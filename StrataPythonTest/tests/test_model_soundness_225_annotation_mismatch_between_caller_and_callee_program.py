# Inter-procedural type contract — caller asserts arg types + assumes return
# type; callee asserts params + proves return; all 4 needed
"""
When function `f(x: int) -> str` is called with `f(my_var)`, the model
must verify TWO things:
1. At call site: my_var satisfies f's parameter type (isfrom_int)
2. After call: result satisfies f's return type (isfrom_str)

If (1) is missing: f might receive a non-int argument, violating its
precondition. The function body assumes isfrom_int(x) but it's not true.

If (2) is missing: the caller doesn't know the result is a string.
Subsequent operations on the result fall to Hole.

This is the INTER-PROCEDURAL type contract: caller guarantees argument
types, callee guarantees return type.

Uses ONLY confirmed-accepted constructs: function def, int, str, bool.
"""


def int_to_str(n: int) -> str:
    """Converts int to string representation."""
    if n == 0:
        return "zero"
    if n > 0:
        return "positive"
    return "negative"


def str_to_len(s: str) -> int:
    """Returns length of string."""
    return len(s)


def compose(n: int) -> int:
    """Calls int_to_str then str_to_len — types must chain."""
    s: str = int_to_str(n)  # caller gets str (from return type)
    return str_to_len(s)    # passes str to str_to_len (matches param type)


def wrong_arg_type_caught() -> int:
    """If we could pass str to int_to_str, model should catch it.
    But mypy catches this — Frontend adds defense in depth."""
    # int_to_str("hello")  ← would be caught by mypy AND Frontend
    # The model's assert isfrom_int(x) at function entry catches it
    return int_to_str(5) == "positive"


def return_type_flows_to_caller() -> bool:
    """Caller uses return type for subsequent operations."""
    result: str = int_to_str(42)
    # result is known to be str (from return type annotation)
    # So len(result) is valid (str has len)
    return len(result) > 0


def chain_multiple_calls() -> int:
    """Multiple function calls — each return type feeds next arg type."""
    a: str = int_to_str(5)       # str
    b: int = str_to_len(a)       # int
    c: str = int_to_str(b)       # str
    d: int = str_to_len(c)       # int
    return d


def main() -> None:
    assert compose(5) == 8  # "positive" has length 8
    assert compose(0) == 4  # "zero" has length 4
    assert compose(-1) == 8  # "negative" has length 8

    assert return_type_flows_to_caller() == True
    assert chain_multiple_calls() == 8  # "positive" → 8

    print(compose(5), return_type_flows_to_caller(),
          chain_multiple_calls())


main()
