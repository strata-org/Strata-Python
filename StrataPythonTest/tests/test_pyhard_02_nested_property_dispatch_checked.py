# Generated from pyhard.analysis. Do not edit.
# Each inferred claim executes assert(P), then assume(P).
# A false assumption exits that execution successfully with SystemExit(0).
import builtins as _pyhard_runtime_builtins
_pyhard_runtime_shapes = {'Console': {'kind': 'class', 'fields': {'panel': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'Panel', 'variadic': False}}}}, 'Gauge': {'kind': 'class', 'fields': {'_reading': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'int', 'variadic': False}}}}, 'Panel': {'kind': 'class', 'fields': {'gauge': {'required': True, 'type': {'args': [], 'kind': 'atomic', 'literals': [], 'name': 'Gauge', 'variadic': False}}}}}

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

class Gauge:
    _reading: int

    def __init__(self, reading: int):
        _pyhard_runtime_assert_value(reading, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Gauge.__init__:parameter:L4:reading')
        _pyhard_runtime_assume_value(reading, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Gauge.__init__:parameter:L4:reading')
        _pyhard_runtime_assert_state(locals(), [{'name': 'reading', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Gauge']}], 'Gauge.__init__:L5')
        _pyhard_runtime_assume_state(locals(), [{'name': 'reading', 'status': 'definitely_bound', 'tags': ['bool', 'int']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Gauge']}], 'Gauge.__init__:L5')
        self._reading = _pyhard_runtime_checked_value(reading, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Gauge.__init__:field_write:L5:Gauge._reading')

    @property
    def reading(self) -> int:
        _pyhard_runtime_assert_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Gauge']}], 'Gauge.reading:L9')
        _pyhard_runtime_assume_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Gauge']}], 'Gauge.reading:L9')
        return _pyhard_runtime_checked_value(self._reading, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Gauge.reading:return:L9:result')

    @reading.setter
    def reading(self, value: int) -> None:
        _pyhard_runtime_assert_value(value, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Gauge.reading$setter:parameter:L12:value')
        _pyhard_runtime_assume_value(value, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Gauge.reading$setter:parameter:L12:value')
        _pyhard_runtime_assert_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Gauge']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['bool', 'int']}], 'Gauge.reading$setter:L13')
        _pyhard_runtime_assume_state(locals(), [{'name': 'self', 'status': 'definitely_bound', 'tags': ['Gauge']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['bool', 'int']}], 'Gauge.reading$setter:L13')
        self._reading = _pyhard_runtime_checked_value(value, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'Gauge.reading$setter:field_write:L13:Gauge._reading')
        _pyhard_runtime_assert_value(None, {'args': [], 'display': 'NoneType', 'kind': 'atomic', 'literals': [], 'name': 'NoneType', 'outer_tags': ['NoneType'], 'variadic': False}, 'Gauge.reading$setter:implicit_return:L12')
        _pyhard_runtime_assume_value(None, {'args': [], 'display': 'NoneType', 'kind': 'atomic', 'literals': [], 'name': 'NoneType', 'outer_tags': ['NoneType'], 'variadic': False}, 'Gauge.reading$setter:implicit_return:L12')

class Panel:
    gauge: Gauge

    def __init__(self, gauge: Gauge):
        _pyhard_runtime_assert_value(gauge, {'args': [], 'display': 'Gauge', 'kind': 'atomic', 'literals': [], 'name': 'Gauge', 'outer_tags': ['Gauge'], 'variadic': False}, 'Panel.__init__:parameter:L19:gauge')
        _pyhard_runtime_assume_value(gauge, {'args': [], 'display': 'Gauge', 'kind': 'atomic', 'literals': [], 'name': 'Gauge', 'outer_tags': ['Gauge'], 'variadic': False}, 'Panel.__init__:parameter:L19:gauge')
        _pyhard_runtime_assert_state(locals(), [{'name': 'gauge', 'status': 'definitely_bound', 'tags': ['Gauge']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Panel']}], 'Panel.__init__:L20')
        _pyhard_runtime_assume_state(locals(), [{'name': 'gauge', 'status': 'definitely_bound', 'tags': ['Gauge']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Panel']}], 'Panel.__init__:L20')
        self.gauge = _pyhard_runtime_checked_value(gauge, {'args': [], 'display': 'Gauge', 'kind': 'atomic', 'literals': [], 'name': 'Gauge', 'outer_tags': ['Gauge'], 'variadic': False}, 'Panel.__init__:field_write:L20:Panel.gauge')

class Console:
    panel: Panel

    def __init__(self, panel: Panel):
        _pyhard_runtime_assert_value(panel, {'args': [], 'display': 'Panel', 'kind': 'atomic', 'literals': [], 'name': 'Panel', 'outer_tags': ['Panel'], 'variadic': False}, 'Console.__init__:parameter:L26:panel')
        _pyhard_runtime_assume_value(panel, {'args': [], 'display': 'Panel', 'kind': 'atomic', 'literals': [], 'name': 'Panel', 'outer_tags': ['Panel'], 'variadic': False}, 'Console.__init__:parameter:L26:panel')
        _pyhard_runtime_assert_state(locals(), [{'name': 'panel', 'status': 'definitely_bound', 'tags': ['Panel']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Console']}], 'Console.__init__:L27')
        _pyhard_runtime_assume_state(locals(), [{'name': 'panel', 'status': 'definitely_bound', 'tags': ['Panel']}, {'name': 'self', 'status': 'definitely_bound', 'tags': ['Console']}], 'Console.__init__:L27')
        self.panel = _pyhard_runtime_checked_value(panel, {'args': [], 'display': 'Panel', 'kind': 'atomic', 'literals': [], 'name': 'Panel', 'outer_tags': ['Panel'], 'variadic': False}, 'Console.__init__:field_write:L27:Console.panel')

def adjust(console: Console, value: int) -> int:
    _pyhard_runtime_assert_value(console, {'args': [], 'display': 'Console', 'kind': 'atomic', 'literals': [], 'name': 'Console', 'outer_tags': ['Console'], 'variadic': False}, 'adjust:parameter:L30:console')
    _pyhard_runtime_assume_value(console, {'args': [], 'display': 'Console', 'kind': 'atomic', 'literals': [], 'name': 'Console', 'outer_tags': ['Console'], 'variadic': False}, 'adjust:parameter:L30:console')
    _pyhard_runtime_assert_value(value, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'adjust:parameter:L30:value')
    _pyhard_runtime_assume_value(value, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'adjust:parameter:L30:value')
    _pyhard_runtime_assert_state(locals(), [{'name': 'console', 'status': 'definitely_bound', 'tags': ['Console']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['bool', 'int']}], 'adjust:L31')
    _pyhard_runtime_assume_state(locals(), [{'name': 'console', 'status': 'definitely_bound', 'tags': ['Console']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['bool', 'int']}], 'adjust:L31')
    console.panel.gauge.reading = _pyhard_runtime_checked_value(value, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'adjust:property_setter_argument:L31:value')
    _pyhard_runtime_assert_state(locals(), [{'name': 'console', 'status': 'definitely_bound', 'tags': ['Console']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['bool', 'int']}], 'adjust:L32')
    _pyhard_runtime_assume_state(locals(), [{'name': 'console', 'status': 'definitely_bound', 'tags': ['Console']}, {'name': 'value', 'status': 'definitely_bound', 'tags': ['bool', 'int']}], 'adjust:L32')
    return _pyhard_runtime_checked_value(console.panel.gauge.reading, {'args': [], 'display': 'int', 'kind': 'atomic', 'literals': [], 'name': 'int', 'outer_tags': ['int'], 'variadic': False}, 'adjust:return:L32:result')
