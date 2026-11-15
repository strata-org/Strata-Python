# A dataclass's generated __eq__ at depth 896, the deepest where the model runs it below its
# limit of 900 Python frames (the module's frame included): the model answers, since the methods
# that recurse through their operands skip the 32-frame check that the other natives of
# dataclasses and typing make at entry.
from dataclasses import dataclass
@dataclass
class P:
    x: int
A = P(1)
B = P(1)
def op():
    return A == B
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    print(f(896))
except RecursionError:
    print('RecursionError')
