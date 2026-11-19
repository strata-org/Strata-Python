# F1 (preamble) and F2 (postamble): a contract needs one entry block and one block that every
# return and raise reaches, carrying the completion.
# @requires   n >= 0
# @on_return  r: r == n * (n + 1) // 2
# @on_raise   e: isinstance(e, ValueError) and n > 1000
def total(n):
    if n > 1000:
        raise ValueError()
    if n == 0:
        return 0
    s = 0
    for i in range(n + 1):
        s += i
    return s
