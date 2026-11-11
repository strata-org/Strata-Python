# A field name that is not ASCII.
import typing
NT = typing._NamedTuple
M = typing.NamedTupleMeta
P = M.__new__(M, "P", (NT,), {"__module__": "m", "__annotations__": {"é": int}})
print(P._fields)
