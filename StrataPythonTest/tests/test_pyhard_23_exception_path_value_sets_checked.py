# Generated from pyhard.analysis. Do not edit.
# Each inferred claim executes assert(P), then assume(P).
# A false assumption exits that execution successfully with SystemExit(0).
import builtins as _pyhard_runtime_builtins
_pyhard_runtime_shapes = {'Early': {'kind': 'class', 'fields': {}}, 'Late': {'kind': 'class', 'fields': {}}, 'RouteError': {'kind': 'class', 'fields': {}}}

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

class Early:

    def marker(self) -> int:
        _pyhard_runtime_assert_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Early']}], 'Early.marker:L3')
        _pyhard_runtime_assume_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Early']}], 'Early.marker:L3')
        return _pyhard_runtime_checked_value(1, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Early.marker:return:L3:result')

class Late:

    def marker(self) -> str:
        _pyhard_runtime_assert_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Late']}], 'Late.marker:L8')
        _pyhard_runtime_assume_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Late']}], 'Late.marker:L8')
        return _pyhard_runtime_checked_value('late', {'args': [], 'display': 'str', 'kind': 'atomic', 'literals': [], 'name': 'str', 'outer_tags': ['str'], 'variadic': False}, 'Late.marker:return:L8:result')

class RouteError(Exception):
    pass

def split_at_handler(flag: bool) -> int | str:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'split_at_handler:parameter:L15:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'split_at_handler:parameter:L15:flag')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'split_at_handler:L16')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'split_at_handler:L16')
    value = Early()
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L17')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L17')
    try:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L18')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L18')
        if flag:
            _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L19')
            _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L19')
            raise RouteError()
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L20')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L20')
        value = Late()
    except RouteError as route_error:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_bound', 'tags': ['RouteError']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L22')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_bound', 'tags': ['RouteError']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'split_at_handler:L22')
        return _pyhard_runtime_checked_value(value.marker(), {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, {'args': [], 'display': 'str', 'kind': 'atomic', 'literals': [], 'name': 'str', 'outer_tags': ['str'], 'variadic': False}], 'display': 'int | str', 'kind': 'union', 'literals': [], 'name': None, 'outer_tags': ['int', 'str'], 'variadic': False}, 'split_at_handler:return:L22:result')
    else:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Late']}], 'split_at_handler:L24')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Late']}], 'split_at_handler:L24')
        return _pyhard_runtime_checked_value(value.marker(), {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, {'args': [], 'display': 'str', 'kind': 'atomic', 'literals': [], 'name': 'str', 'outer_tags': ['str'], 'variadic': False}], 'display': 'int | str', 'kind': 'union', 'literals': [], 'name': None, 'outer_tags': ['int', 'str'], 'variadic': False}, 'split_at_handler:return:L24:result')

def join_after_handler(flag: bool) -> int | str:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'join_after_handler:parameter:L27:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'join_after_handler:parameter:L27:flag')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'join_after_handler:L28')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'join_after_handler:L28')
    value = Early()
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L29')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L29')
    try:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L30')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L30')
        if flag:
            _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L31')
            _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L31')
            raise RouteError()
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L32')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L32')
        value = Late()
    except RouteError as route_error:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_bound', 'tags': ['RouteError']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L34')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_bound', 'tags': ['RouteError']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early']}], 'join_after_handler:L34')
        selected = value
    else:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Late']}], 'join_after_handler:L36')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Late']}], 'join_after_handler:L36')
        selected = value
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_bound', 'tags': ['Early', 'Late']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early', 'Late']}], 'join_after_handler:L37')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'route_error', 'status': 'definitely_unbound', 'tags': []}, {'name': 'selected', 'status': 'definitely_bound', 'tags': ['Early', 'Late']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['Early', 'Late']}], 'join_after_handler:L37')
    return _pyhard_runtime_checked_value(selected.marker(), {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, {'args': [], 'display': 'str', 'kind': 'atomic', 'literals': [], 'name': 'str', 'outer_tags': ['str'], 'variadic': False}], 'display': 'int | str', 'kind': 'union', 'literals': [], 'name': None, 'outer_tags': ['int', 'str'], 'variadic': False}, 'join_after_handler:return:L37:result')
