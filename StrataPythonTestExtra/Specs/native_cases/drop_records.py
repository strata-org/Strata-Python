# PySpec records each clause that it drops, with its source text.
@requires(lambda x: x.bit_length() > 3)
@admit(lambda x, result: result.bit_length() > 0)
@modifies(lambda x: x.bit_length())
def f(x: int) -> int:
    assert x.bit_length() < 9, "small"
