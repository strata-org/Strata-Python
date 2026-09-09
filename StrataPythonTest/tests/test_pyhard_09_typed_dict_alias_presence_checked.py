# Generated from pyhard.analysis. Do not edit.
# Each inferred claim executes assert(P), then assume(P).
# A false assumption exits that execution successfully with SystemExit(0).
import builtins as _pyhard_runtime_builtins
_pyhard_runtime_shapes = {'Settings': {'kind': 'typed_dict', 'fields': {'retries': {'required': False, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'int', 'variadic': False}}, 'service': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'str', 'variadic': False}}}}}

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
from typing import NotRequired, TypedDict

class Settings(TypedDict):
    service: str
    retries: NotRequired[int]

def direct_update(settings: Settings, retries: int) -> int:
    _pyhard_runtime_assert_value(settings, {'args': [], 'display': 'Settings', 'kind': 'atomic', 'literals': [], 'name': 'Settings', 'outer_tags': ['Settings'], 'variadic': False}, 'direct_update:parameter:L9:settings')
    _pyhard_runtime_assume_value(settings, {'args': [], 'display': 'Settings', 'kind': 'atomic', 'literals': [], 'name': 'Settings', 'outer_tags': ['Settings'], 'variadic': False}, 'direct_update:parameter:L9:settings')
    _pyhard_runtime_assert_value(retries, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'direct_update:parameter:L9:retries')
    _pyhard_runtime_assume_value(retries, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'direct_update:parameter:L9:retries')
    _pyhard_runtime_assert_state(locals(), [{'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'direct_update:L10')
    _pyhard_runtime_assume_state(locals(), [{'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'direct_update:L10')
    settings['retries'] = _pyhard_runtime_checked_value(retries, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, "direct_update:typed_dict_field_write:L10:Settings['retries']")
    _pyhard_runtime_assert_state(locals(), [{'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'direct_update:L11')
    _pyhard_runtime_assume_state(locals(), [{'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'direct_update:L11')
    return _pyhard_runtime_checked_value(settings.get('retries'), {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'direct_update:return:L11:result')

def alias_update(settings: Settings, retries: int) -> int | None:
    _pyhard_runtime_assert_value(settings, {'args': [], 'display': 'Settings', 'kind': 'atomic', 'literals': [], 'name': 'Settings', 'outer_tags': ['Settings'], 'variadic': False}, 'alias_update:parameter:L14:settings')
    _pyhard_runtime_assume_value(settings, {'args': [], 'display': 'Settings', 'kind': 'atomic', 'literals': [], 'name': 'Settings', 'outer_tags': ['Settings'], 'variadic': False}, 'alias_update:parameter:L14:settings')
    _pyhard_runtime_assert_value(retries, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'alias_update:parameter:L14:retries')
    _pyhard_runtime_assume_value(retries, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'alias_update:parameter:L14:retries')
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'alias_update:L15')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_unbound', 'tags': []}, {'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'alias_update:L15')
    alias = settings
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['Settings']}, {'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'alias_update:L16')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['Settings']}, {'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'alias_update:L16')
    alias['retries'] = _pyhard_runtime_checked_value(retries, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, "alias_update:typed_dict_field_write:L16:Settings['retries']")
    _pyhard_runtime_assert_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['Settings']}, {'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'alias_update:L17')
    _pyhard_runtime_assume_state(locals(), [{'name': 'alias', 'status': 'definitely_bound', 'tags': ['Settings']}, {'name': 'retries', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'settings', 'status': 'definitely_bound', 'tags': ['Settings']}], 'alias_update:L17')
    return _pyhard_runtime_checked_value(settings.get('retries'), {'args': [{'args': [], 'display': 'NoneType', 'kind': 'atomic', 'literals': [], 'name': 'NoneType', 'outer_tags': ['NoneType'], 'variadic': False}, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}], 'display': 'NoneType | int', 'kind': 'union', 'literals': [], 'name': None, 'outer_tags': ['NoneType', 'int'], 'variadic': False}, 'alias_update:return:L17:result')
