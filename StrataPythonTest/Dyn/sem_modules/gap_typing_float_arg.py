# A float is not one of the known values that a subscription takes.
from typing import List
print(List[1] is List[1])
List[1.0]
