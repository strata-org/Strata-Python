# Generated from pyhard.analysis. Do not edit.
# Each inferred claim executes assert(P), then assume(P).
# A false assumption exits that execution successfully with SystemExit(0).
import builtins as _pyhard_runtime_builtins
_pyhard_runtime_shapes = {'Forward': {'kind': 'class', 'fields': {}}, 'Reflected': {'kind': 'class', 'fields': {}}}

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

class Forward:

    def __add__(self, other):
        _pyhard_runtime_assert_state(locals(), [{'name': 'other', 'status': 'definitely_bound', 'tags': ['Forward', 'NoneType', 'NotImplementedType', 'Reflected', 'bool', 'bytes', 'dict', 'float', 'frozenset', 'int', 'list', 'object', 'range', 'set', 'slice', 'str', 'tuple', 'type']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Forward']}], 'Forward.__add__:L3')
        _pyhard_runtime_assume_state(locals(), [{'name': 'other', 'status': 'definitely_bound', 'tags': ['Forward', 'NoneType', 'NotImplementedType', 'Reflected', 'bool', 'bytes', 'dict', 'float', 'frozenset', 'int', 'list', 'object', 'range', 'set', 'slice', 'str', 'tuple', 'type']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Forward']}], 'Forward.__add__:L3')
        return NotImplemented

class Reflected(Forward):

    def __radd__(self, other) -> int:
        _pyhard_runtime_assert_state(locals(), [{'name': 'other', 'status': 'definitely_bound', 'tags': ['Forward', 'NoneType', 'NotImplementedType', 'Reflected', 'bool', 'bytes', 'dict', 'float', 'frozenset', 'int', 'list', 'object', 'range', 'set', 'slice', 'str', 'tuple', 'type']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Reflected']}], 'Reflected.__radd__:L8')
        _pyhard_runtime_assume_state(locals(), [{'name': 'other', 'status': 'definitely_bound', 'tags': ['Forward', 'NoneType', 'NotImplementedType', 'Reflected', 'bool', 'bytes', 'dict', 'float', 'frozenset', 'int', 'list', 'object', 'range', 'set', 'slice', 'str', 'tuple', 'type']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Reflected']}], 'Reflected.__radd__:L8')
        return _pyhard_runtime_checked_value(7, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Reflected.__radd__:return:L8:result')

def custom(left: Forward, right: Reflected) -> int:
    _pyhard_runtime_assert_value(left, {'args': [], 'display': 'Forward', 'kind': 'atomic', 'literals': [], 'name': 'Forward', 'outer_tags': ['Forward'], 'variadic': False}, 'custom:parameter:L11:left')
    _pyhard_runtime_assume_value(left, {'args': [], 'display': 'Forward', 'kind': 'atomic', 'literals': [], 'name': 'Forward', 'outer_tags': ['Forward'], 'variadic': False}, 'custom:parameter:L11:left')
    _pyhard_runtime_assert_value(right, {'args': [], 'display': 'Reflected', 'kind': 'atomic', 'literals': [], 'name': 'Reflected', 'outer_tags': ['Reflected'], 'variadic': False}, 'custom:parameter:L11:right')
    _pyhard_runtime_assume_value(right, {'args': [], 'display': 'Reflected', 'kind': 'atomic', 'literals': [], 'name': 'Reflected', 'outer_tags': ['Reflected'], 'variadic': False}, 'custom:parameter:L11:right')
    _pyhard_runtime_assert_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['Forward', 'Reflected']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['Reflected']}], 'custom:L12')
    _pyhard_runtime_assume_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['Forward', 'Reflected']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['Reflected']}], 'custom:L12')
    return _pyhard_runtime_checked_value(left + right, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'custom:return:L12:result')

def correlated_builtin(flag: bool) -> int | str:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'correlated_builtin:parameter:L15:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'correlated_builtin:parameter:L15:flag')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L16')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L16')
    if flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L17')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L17')
        left = 1
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['int']}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L18')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['int']}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L18')
        right = 2
    else:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L20')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L20')
        left = 'a'
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['str']}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L21')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['str']}, {'name': 'right', 'status': 'definitely_unbound', 'tags': []}], 'correlated_builtin:L21')
        right = 'b'
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['int', 'str']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['int', 'str']}], 'correlated_builtin:L22')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['int', 'str']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['int', 'str']}], 'correlated_builtin:L22')
    return _pyhard_runtime_checked_value(left + right, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, {'args': [], 'display': 'str', 'kind': 'atomic', 'literals': [], 'name': 'str', 'outer_tags': ['str'], 'variadic': False}], 'display': 'int | str', 'kind': 'union', 'literals': [], 'name': None, 'outer_tags': ['int', 'str'], 'variadic': False}, 'correlated_builtin:return:L22:result')
