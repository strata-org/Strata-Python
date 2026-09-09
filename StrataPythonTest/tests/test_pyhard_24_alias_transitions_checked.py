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

def branch_alias(flag: bool, left: list[int], right: list[int]) -> list[int]:
    _pyhard_runtime_assert_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'branch_alias:parameter:L2:flag')
    _pyhard_runtime_assume_value(flag, {'args': [], 'display': 'bool', 'kind': 'atomic', 'literals': [], 'name': 'bool', 'outer_tags': ['bool'], 'variadic': False}, 'branch_alias:parameter:L2:flag')
    _pyhard_runtime_assert_value(left, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'list[int]', 'kind': 'generic', 'literals': [], 'name': 'list', 'outer_tags': ['list'], 'variadic': False}, 'branch_alias:parameter:L3:left')
    _pyhard_runtime_assume_value(left, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'list[int]', 'kind': 'generic', 'literals': [], 'name': 'list', 'outer_tags': ['list'], 'variadic': False}, 'branch_alias:parameter:L3:left')
    _pyhard_runtime_assert_value(right, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'list[int]', 'kind': 'generic', 'literals': [], 'name': 'list', 'outer_tags': ['list'], 'variadic': False}, 'branch_alias:parameter:L4:right')
    _pyhard_runtime_assume_value(right, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'list[int]', 'kind': 'generic', 'literals': [], 'name': 'list', 'outer_tags': ['list'], 'variadic': False}, 'branch_alias:parameter:L4:right')
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}], 'branch_alias:L6')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}], 'branch_alias:L6')
    if flag:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}], 'branch_alias:L7')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}], 'branch_alias:L7')
        selected = left
    else:
        _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}], 'branch_alias:L9')
        _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_unbound', 'tags': []}], 'branch_alias:L9')
        selected = right
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_bound', 'tags': ['list']}], 'branch_alias:L10')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_bound', 'tags': ['list']}], 'branch_alias:L10')
    selected.append(1)
    _pyhard_runtime_assert_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_bound', 'tags': ['list']}], 'branch_alias:L11')
    _pyhard_runtime_assume_state(locals(), [{'name': 'flag', 'status': 'definitely_bound', 'tags': ['bool']}, {'name': 'left', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'right', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'selected', 'status': 'definitely_bound', 'tags': ['list']}], 'branch_alias:L11')
    return _pyhard_runtime_checked_value(selected, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'list[int]', 'kind': 'generic', 'literals': [], 'name': 'list', 'outer_tags': ['list'], 'variadic': False}, 'branch_alias:return:L11:result')

def delete_one_name() -> list[int]:
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'delete_one_name:L15')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'delete_one_name:L15')
    original = []
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'delete_one_name:L16')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'delete_one_name:L16')
    alias = original
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'delete_one_name:L17')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'delete_one_name:L17')
    del original
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'delete_one_name:L18')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'delete_one_name:L18')
    alias.append(1)
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'delete_one_name:L19')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'delete_one_name:L19')
    return _pyhard_runtime_checked_value(alias, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'list[int]', 'kind': 'generic', 'literals': [], 'name': 'list', 'outer_tags': ['list'], 'variadic': False}, 'delete_one_name:return:L19:result')

def rebind_one_name() -> list[int]:
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'rebind_one_name:L23')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_unbound', 'tags': []}], 'rebind_one_name:L23')
    original = []
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'rebind_one_name:L24')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'rebind_one_name:L24')
    alias = original
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'rebind_one_name:L25')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['list']}], 'rebind_one_name:L25')
    original = {}
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['dict']}], 'rebind_one_name:L26')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['dict']}], 'rebind_one_name:L26')
    alias.append(1)
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['dict']}], 'rebind_one_name:L27')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['list']}, {'name': 'original', 'status': 'definitely_bound', 'tags': ['dict']}], 'rebind_one_name:L27')
    return _pyhard_runtime_checked_value(alias, {'args': [{'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'list[int]', 'kind': 'generic', 'literals': [], 'name': 'list', 'outer_tags': ['list'], 'variadic': False}, 'rebind_one_name:return:L27:result')
