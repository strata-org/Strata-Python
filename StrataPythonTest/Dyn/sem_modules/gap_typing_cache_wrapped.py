# typing's cached __getitem__ wrappers have CPython's functools.wraps __dict__, whose __wrapped__
# stops with a gap.
import typing
print(hasattr(typing._SpecialForm.__getitem__, "__wrapped__"))
print(hasattr(typing.List.__getitem__, "__wrapped__"))
print(hasattr(typing._TupleType.__getitem__, "__wrapped__"))
