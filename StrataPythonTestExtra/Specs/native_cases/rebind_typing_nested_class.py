# A nested class body that binds a typing name rejects the model.
from typing import Dict


class Outer:
    class Inner:
        Dict = int
