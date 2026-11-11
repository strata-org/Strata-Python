# A direct call of NamedTupleMeta.__new__ with a namespace that is not a dict.
import typing
M = typing.NamedTupleMeta
print(M.__new__(M, "X", (typing._NamedTuple,), {"__module__": "m"}))
M.__new__(M, "Y", (typing._NamedTuple,), [])
