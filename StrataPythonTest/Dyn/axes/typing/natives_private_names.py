import typing, dataclasses
from typing import List, Optional, Union, Any, Tuple
print(isinstance(List[int], typing._GenericAlias), isinstance(List, typing._SpecialGenericAlias), isinstance(Optional, typing._SpecialForm))
print(isinstance(Union[int, str], typing._UnionGenericAlias), isinstance(Tuple, typing._TupleType), isinstance(List, typing._BaseGenericAlias), isinstance(List, typing._Final))
print(type(Any) is typing._AnyMeta, typing._NotIterable.__iter__, typing._overload_dummy.__name__)
class TD(typing.TypedDict):
    a: int
class P(typing.NamedTuple):
    x: int
print(type(TD) is typing._TypedDictMeta, TD.__mro__[1] is dict, type(typing._NamedTuple).__name__, typing._TypedDict.__name__, typing.NamedTupleMeta.__name__)
print(typing._namedtuple_mro_entries.__name__)
print(type(dataclasses.MISSING) is dataclasses._MISSING_TYPE, dataclasses._HAS_DEFAULT_FACTORY.__class__ is dataclasses._HAS_DEFAULT_FACTORY_CLASS, repr(dataclasses._HAS_DEFAULT_FACTORY))
print(repr(dataclasses._FIELD), repr(dataclasses._FIELD_CLASSVAR), repr(dataclasses._FIELD_INITVAR), type(dataclasses._FIELD) is dataclasses._FIELD_BASE)
print(dataclasses._FIELDS, dataclasses._PARAMS, dataclasses._POST_INIT_NAME, dataclasses._DataclassParams.__name__)
