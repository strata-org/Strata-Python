# The ports check the builtins that they use; changing one is itself not modelled yet.
import builtins
from typing import List
builtins.super = len
List[int]
