# Generated from pyhard.analysis. Do not edit.
# Each inferred claim executes assert(P), then assume(P).
# A false assumption exits that execution successfully with SystemExit(0).
import builtins as _pyhard_runtime_builtins
_pyhard_runtime_shapes = {}

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

def numeric_effects(left: int, right: int, scale: float, shift: int) -> tuple[float, float, int, bool]:
    _pyhard_runtime_assert_value(left, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'numeric_effects:parameter:L2:left')
    _pyhard_runtime_assume_value(left, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'numeric_effects:parameter:L2:left')
    _pyhard_runtime_assert_value(right, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'numeric_effects:parameter:L3:right')
    _pyhard_runtime_assume_value(right, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'numeric_effects:parameter:L3:right')
    _pyhard_runtime_assert_value(scale, {'args': [], 'display': 'float', 'kind': 'atomic', 'literals': [], 'name': 'float', 'outer_tags': ['float'], 'variadic': False}, 'numeric_effects:parameter:L4:scale')
    _pyhard_runtime_assume_value(scale, {'args': [], 'display': 'float', 'kind': 'atomic', 'literals': [], 'name': 'float', 'outer_tags': ['float'], 'variadic': False}, 'numeric_effects:parameter:L4:scale')
    _pyhard_runtime_assert_value(shift, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'numeric_effects:parameter:L5:shift')
    _pyhard_runtime_assume_value(shift, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'numeric_effects:parameter:L5:shift')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_unbound', 'tags': []}, {'name': 'quotient', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_unbound', 'tags': []}], 'numeric_effects:L7')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_unbound', 'tags': []}, {'name': 'quotient', 'status': 'definitely_unbound', 'tags': []}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_unbound', 'tags': []}], 'numeric_effects:L7')
    quotient = left / right
    _pyhard_runtime_assert_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_unbound', 'tags': []}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_unbound', 'tags': []}], 'numeric_effects:L8')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_unbound', 'tags': []}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_unbound', 'tags': []}], 'numeric_effects:L8')
    mixed = left + scale
    _pyhard_runtime_assert_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_bound', 'tags': ['float', 'int']}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_unbound', 'tags': []}], 'numeric_effects:L9')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_bound', 'tags': ['float', 'int']}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_unbound', 'tags': []}], 'numeric_effects:L9')
    shifted = left << shift
    _pyhard_runtime_assert_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_bound', 'tags': ['float', 'int']}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_bound', 'tags': ['int']}], 'numeric_effects:L10')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flags', 'status': 'definitely_unbound', 'tags': []}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_bound', 'tags': ['float', 'int']}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_bound', 'tags': ['int']}], 'numeric_effects:L10')
    flags = True & False
    _pyhard_runtime_assert_state(locals(), [{'name': 'flags', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_bound', 'tags': ['float', 'int']}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_bound', 'tags': ['int']}], 'numeric_effects:L11')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flags', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'mixed', 'status': 'definitely_bound', 'tags': ['float', 'int']}, {'name': 'quotient', 'status': 'definitely_bound', 'tags': ['float']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'scale', 'status': 'definitely_bound', 'tags': ['bool', 'float', 'int']}, {'name': 'shift', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'shifted', 'status': 'definitely_bound', 'tags': ['int']}], 'numeric_effects:L11')
    return _pyhard_runtime_checked_value((quotient, mixed, shifted, flags), {'args': [{'args': [], 'display': 'float', 'kind': 'atomic', 'literals': [], 'name': 'float', 'outer_tags': ['float'], 'variadic': False}, {'args': [], 'display': 'float', 'kind': 'atomic', 'literals': [], 'name': 'float', 'outer_tags': ['float'], 'variadic': False}, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}], 'display': 'tuple[float, float, int, bool]', 'kind': 'generic', 'literals': [], 'name': 'tuple', 'outer_tags': ['tuple'], 'variadic': False}, 'numeric_effects:return:L11:result')

def divide_or_zero(left: int, right: int) -> float:
    _pyhard_runtime_assert_value(left, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'divide_or_zero:parameter:L14:left')
    _pyhard_runtime_assume_value(left, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'divide_or_zero:parameter:L14:left')
    _pyhard_runtime_assert_value(right, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'divide_or_zero:parameter:L14:right')
    _pyhard_runtime_assume_value(right, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'divide_or_zero:parameter:L14:right')
    _pyhard_runtime_assert_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'zero', 'status': 'definitely_unbound', 'tags': []}], 'divide_or_zero:L15')
    _pyhard_runtime_assume_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'zero', 'status': 'definitely_unbound', 'tags': []}], 'divide_or_zero:L15')
    try:
        _pyhard_runtime_assert_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'zero', 'status': 'definitely_unbound', 'tags': []}], 'divide_or_zero:L16')
        _pyhard_runtime_assume_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'zero', 'status': 'definitely_unbound', 'tags': []}], 'divide_or_zero:L16')
        return _pyhard_runtime_checked_value(left / right, {'args': [], 'display': 'float', 'kind': 'atomic', 'literals': [], 'name': 'float', 'outer_tags': ['float'], 'variadic': False}, 'divide_or_zero:return:L16:result')
    except ZeroDivisionError as zero:
        _pyhard_runtime_assert_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'zero', 'status': 'definitely_bound', 'tags': ['ZeroDivisionError']}], 'divide_or_zero:L18')
        _pyhard_runtime_assume_state(locals(), [{'name': 'left', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'zero', 'status': 'definitely_bound', 'tags': ['ZeroDivisionError']}], 'divide_or_zero:L18')
        return _pyhard_runtime_checked_value(0.0, {'args': [], 'display': 'float', 'kind': 'atomic', 'literals': [], 'name': 'float', 'outer_tags': ['float'], 'variadic': False}, 'divide_or_zero:return:L18:result')
