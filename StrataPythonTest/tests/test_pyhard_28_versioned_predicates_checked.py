# Generated from pyhard.analysis. Do not edit.
# Each inferred claim executes assert(P), then assume(P).
# A false assumption exits that execution successfully with SystemExit(0).
import builtins as _pyhard_runtime_builtins
_pyhard_runtime_shapes = {'A': {'kind': 'class', 'fields': {}}, 'B': {'kind': 'class', 'fields': {}}}

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

class A:

    def marker(self) -> int:
        _pyhard_runtime_assert_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['A']}], 'A.marker:L3')
        _pyhard_runtime_assume_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['A']}], 'A.marker:L3')
        return _pyhard_runtime_checked_value(1, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'A.marker:return:L3:result')

class B:

    def marker(self) -> int:
        _pyhard_runtime_assert_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['B']}], 'B.marker:L8')
        _pyhard_runtime_assume_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['B']}], 'B.marker:L8')
        return _pyhard_runtime_checked_value(2, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'B.marker:return:L8:result')

def reassigned_guard(flag: bool) -> int:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'reassigned_guard:parameter:L11:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'reassigned_guard:parameter:L11:flag')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'reassigned_guard:L12')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'reassigned_guard:L12')
    if flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'reassigned_guard:L13')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'reassigned_guard:L13')
        value = A()
    else:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'reassigned_guard:L15')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'reassigned_guard:L15')
        value = B()
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L17')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L17')
    flag = not flag
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L18')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L18')
    if flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L19')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L19')
        return _pyhard_runtime_checked_value(value.marker(), {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'reassigned_guard:return:L19:result')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L20')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'reassigned_guard:L20')
    return _pyhard_runtime_checked_value(value.marker(), {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'reassigned_guard:return:L20:result')

def unchanged_guard(flag: bool) -> int:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'unchanged_guard:parameter:L23:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'unchanged_guard:parameter:L23:flag')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'unchanged_guard:L24')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'unchanged_guard:L24')
    if flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'unchanged_guard:L25')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'unchanged_guard:L25')
        value = A()
    else:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'unchanged_guard:L27')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'unchanged_guard:L27')
        value = B()
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L29')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_unbound', 'tags': []}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L29')
    other = not flag
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L30')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L30')
    if flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L31')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L31')
        return _pyhard_runtime_checked_value(value.marker(), {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'unchanged_guard:return:L31:result')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L32')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'other', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['A', 'B']}], 'unchanged_guard:L32')
    return _pyhard_runtime_checked_value(value.marker(), {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'unchanged_guard:return:L32:result')

def killed_difference(flag: bool) -> int:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'killed_difference:parameter:L35:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'killed_difference:parameter:L35:flag')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'killed_difference:L36')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'killed_difference:L36')
    if flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'killed_difference:L37')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'killed_difference:L37')
        value = 1
    else:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'killed_difference:L39')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_unbound', 'tags': []}], 'killed_difference:L39')
        value = 'old'
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['int', 'str']}], 'killed_difference:L41')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['int', 'str']}], 'killed_difference:L41')
    value = 0
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['int']}], 'killed_difference:L42')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['int']}], 'killed_difference:L42')
    return _pyhard_runtime_checked_value(value + 1, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'killed_difference:return:L42:result')

def finite_loop(flag: bool) -> bool:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'finite_loop:parameter:L45:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'finite_loop:parameter:L45:flag')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}], 'finite_loop:L46')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}], 'finite_loop:L46')
    while flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}], 'finite_loop:L47')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}], 'finite_loop:L47')
        flag = not flag
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}], 'finite_loop:L48')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}], 'finite_loop:L48')
    return _pyhard_runtime_checked_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'finite_loop:return:L48:result')
