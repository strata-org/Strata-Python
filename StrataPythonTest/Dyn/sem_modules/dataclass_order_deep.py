# The generated orderings of two 150-deep dataclass chains, which compare their fields' tuples
# member by member down to the leaves.
from dataclasses import dataclass


@dataclass(order=True)
class D:
    x: object


A = 0
B = 1
for _ in range(150):
    A = D(A)
    B = D(B)
print(A < B, A <= B, A > B, A >= B, A == B)
