# A declaration cannot reference a name bound only by a later import.
X = MyAlias
from typing import Any as MyAlias
