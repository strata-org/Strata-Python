# Generated from pyhard.analysis. Do not edit.
# Each inferred claim executes assert(P), then assume(P).
# A false assumption exits that execution successfully with SystemExit(0).
import builtins as _pyhard_runtime_builtins
_pyhard_runtime_shapes = {'Branch': {'kind': 'class', 'fields': {'b': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'int', 'variadic': False}}}}, 'Record': {'kind': 'class', 'fields': {'field': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'int', 'variadic': False}}}}, 'Records': {'kind': 'typed_dict', 'fields': {'key': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'Record', 'variadic': False}}}}, 'Root': {'kind': 'class', 'fields': {'a': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'Branch', 'variadic': False}}}}}

def _pyhard_runtime_shape(value, name, seen):
    shape = _pyhard_runtime_shapes.get(name)
    if shape is None:
        return False
    token = (id(value), name)
    if token in seen:
        return True
    seen = set(seen)
    seen.add(token)
    if shape['kind'] == 'typed_dict':
        if type(value) is not dict:
            return False
        for field_name, field in shape['fields'].items():
            if field['required'] and field_name not in value:
                return False
            if field_name in value and field['type'] is not None:
                if not _pyhard_runtime_conforms(value[field_name], field['type'], seen):
                    return False
        return True
    if name not in {item.__name__ for item in type(value).__mro__}:
        return False
    for field_name, field in shape['fields'].items():
        if not hasattr(value, field_name):
            return False
        if field['type'] is not None:
            if not _pyhard_runtime_conforms(getattr(value, field_name), field['type'], seen):
                return False
    return True

def _pyhard_runtime_tag(value, tag):
    if tag == 'NoneType':
        return value is None
    if tag == 'NotImplementedType':
        return value is NotImplemented
    if tag in _pyhard_runtime_shapes:
        shape = _pyhard_runtime_shapes[tag]
        if shape['kind'] == 'typed_dict':
            return _pyhard_runtime_shape(value, tag, set())
        return type(value).__name__ == tag
    candidate = getattr(_pyhard_runtime_builtins, tag, None)
    if isinstance(candidate, type):
        if candidate is object:
            return True
        return type(value) is candidate
    return type(value).__name__ == tag

def _pyhard_runtime_conforms(value, spec, seen=None):
    if seen is None:
        seen = set()
    kind = spec.get('kind')
    if kind == 'any':
        return True
    if kind == 'never':
        return False
    if kind == 'atomic':
        name = spec.get('name')
        if name in _pyhard_runtime_shapes:
            return _pyhard_runtime_shape(value, name, seen)
        if name in {'None', 'NoneType'}:
            return value is None
        if name == 'float':
            return type(value) in {bool, int, float}
        candidate = getattr(_pyhard_runtime_builtins, str(name), None)
        if isinstance(candidate, type):
            return isinstance(value, candidate)
        return str(name) in {item.__name__ for item in type(value).__mro__}
    if kind == 'literal':
        return any((type(value) is type(option) and value == option for option in spec.get('literals', [])))
    if kind == 'union':
        return any((_pyhard_runtime_conforms(value, option, seen) for option in spec.get('args', [])))
    if kind != 'generic':
        return False
    name = spec.get('name')
    args = spec.get('args', [])
    if name == 'Callable':
        return callable(value)
    if name == 'list':
        return type(value) is list and all((_pyhard_runtime_conforms(item, args[0], seen) for item in value))
    if name == 'set':
        return type(value) is set and all((_pyhard_runtime_conforms(item, args[0], seen) for item in value))
    if name == 'frozenset':
        return type(value) is frozenset and all((_pyhard_runtime_conforms(item, args[0], seen) for item in value))
    if name == 'dict':
        return type(value) is dict and all((_pyhard_runtime_conforms(key, args[0], seen) and _pyhard_runtime_conforms(item, args[1], seen) for key, item in value.items()))
    if name == 'tuple':
        if type(value) is not tuple:
            return False
        if spec.get('variadic'):
            return all((_pyhard_runtime_conforms(item, args[0], seen) for item in value))
        return len(value) == len(args) and all((_pyhard_runtime_conforms(item, item_spec, seen) for item, item_spec in zip(value, args)))
    return _pyhard_runtime_tag(value, str(name))

def _pyhard_runtime_state_predicate(namespace, claim):
    name = claim['name']
    status = claim['status']
    if status == 'definitely_unbound':
        return name not in namespace
    if status == 'definitely_bound' and name not in namespace:
        return False
    if name not in namespace:
        return status == 'maybe_bound'
    tags = claim['tags']
    return bool(tags) and any((_pyhard_runtime_tag(namespace[name], tag) for tag in tags))

def _pyhard_runtime_assert_state(namespace, claims, label):
    for claim in claims:
        assert _pyhard_runtime_state_predicate(namespace, claim), 'PyHard inferred-state assertion failed at ' + label + ': ' + claim['name']

def _pyhard_runtime_assume_state(namespace, claims, label):
    for claim in claims:
        if not _pyhard_runtime_state_predicate(namespace, claim):
            raise SystemExit(0)

def _pyhard_runtime_assert_value(value, spec, label):
    assert _pyhard_runtime_conforms(value, spec), 'PyHard type assertion failed at ' + label
    return value

def _pyhard_runtime_assume_value(value, spec, label):
    if not _pyhard_runtime_conforms(value, spec):
        raise SystemExit(0)
    return value

def _pyhard_runtime_checked_value(value, spec, label):
    _pyhard_runtime_assert_value(value, spec, label)
    _pyhard_runtime_assume_value(value, spec, label)
    return value
from typing import TypedDict

class Branch:
    b: int

    def __init__(self, b: int):
        _pyhard_runtime_assert_value(b, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Branch.__init__:parameter:L7:b')
        _pyhard_runtime_assume_value(b, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Branch.__init__:parameter:L7:b')
        _pyhard_runtime_assert_state(locals(), [{'name': 'b', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Branch']}], 'Branch.__init__:L8')
        _pyhard_runtime_assume_state(locals(), [{'name': 'b', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Branch']}], 'Branch.__init__:L8')
        self.b = _pyhard_runtime_checked_value(b, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Branch.__init__:field_write:L8:Branch.b')

class Root:
    a: Branch

    def __init__(self, a: Branch):
        _pyhard_runtime_assert_value(a, {'args': [], 'display': 'Branch', 'kind': 'atomic', 'literals': [], 'name': 'Branch', 'outer_tags': ['Branch'], 'variadic': False}, 'Root.__init__:parameter:L14:a')
        _pyhard_runtime_assume_value(a, {'args': [], 'display': 'Branch', 'kind': 'atomic', 'literals': [], 'name': 'Branch', 'outer_tags': ['Branch'], 'variadic': False}, 'Root.__init__:parameter:L14:a')
        _pyhard_runtime_assert_state(locals(), [{'name': 'a', 'status': 'definitely_bound', 'tags': ['Branch']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Root']}], 'Root.__init__:L15')
        _pyhard_runtime_assume_state(locals(), [{'name': 'a', 'status': 'definitely_bound', 'tags': ['Branch']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Root']}], 'Root.__init__:L15')
        self.a = _pyhard_runtime_checked_value(a, {'args': [], 'display': 'Branch', 'kind': 'atomic', 'literals': [], 'name': 'Branch', 'outer_tags': ['Branch'], 'variadic': False}, 'Root.__init__:field_write:L15:Root.a')

class Record:
    field: int

    def __init__(self, field: int):
        _pyhard_runtime_assert_value(field, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Record.__init__:parameter:L21:field')
        _pyhard_runtime_assume_value(field, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Record.__init__:parameter:L21:field')
        _pyhard_runtime_assert_state(locals(), [{'name': 'field', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Record']}], 'Record.__init__:L22')
        _pyhard_runtime_assume_state(locals(), [{'name': 'field', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Record']}], 'Record.__init__:L22')
        self.field = _pyhard_runtime_checked_value(field, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Record.__init__:field_write:L22:Record.field')

class Records(TypedDict):
    key: Record

def combine(x: Root, d: Records) -> int:
    _pyhard_runtime_assert_value(x, {'args': [], 'display': 'Root', 'kind': 'atomic', 'literals': [], 'name': 'Root', 'outer_tags': ['Root'], 'variadic': False}, 'combine:parameter:L29:x')
    _pyhard_runtime_assume_value(x, {'args': [], 'display': 'Root', 'kind': 'atomic', 'literals': [], 'name': 'Root', 'outer_tags': ['Root'], 'variadic': False}, 'combine:parameter:L29:x')
    _pyhard_runtime_assert_value(d, {'args': [], 'display': 'Records', 'kind': 'atomic', 'literals': [], 'name': 'Records', 'outer_tags': ['Records'], 'variadic': False}, 'combine:parameter:L29:d')
    _pyhard_runtime_assume_value(d, {'args': [], 'display': 'Records', 'kind': 'atomic', 'literals': [], 'name': 'Records', 'outer_tags': ['Records'], 'variadic': False}, 'combine:parameter:L29:d')
    _pyhard_runtime_assert_state(locals(), [{'name': 'd', 'status': 'definitely_bound', 'tags': ['Records']}, {'name': 'x', 'status': 'definitely_bound', 'tags': ['Root']}], 'combine:L30')
    _pyhard_runtime_assume_state(locals(), [{'name': 'd', 'status': 'definitely_bound', 'tags': ['Records']}, {'name': 'x', 'status': 'definitely_bound', 'tags': ['Root']}], 'combine:L30')
    return _pyhard_runtime_checked_value(x.a.b + d['key'].field, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'combine:return:L30:result')
