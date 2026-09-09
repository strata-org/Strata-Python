# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary increment] returns={int}; escapes={}
# L1 pyhard[type parameter] assert/assume conforms(value, int); boundary nondet over 16 closed tags
def increment(value: int) -> int:
    # L2 pyhard[flow increment in] value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
    # L2 pyhard[flow increment out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), value -> (binding=definitely_bound; tags={bool, int}; defs={param:value})
    # L2 pyhard[read increment.value@12] binding=definitely_bound
    # L2 pyhard[type return] assert/assume conforms(result, int); observed={int}
    # L2 pyhard[dispatch value + 1] assert/assume key in {(bool, int), (int, int)}
    # L2 pyhard[row {(bool, int), (int, int)}] binary_protocol; result={int}; terminal=certified_builtin_total
    return value + 1


# L5 pyhard[summary collect] returns={list}; escapes={}
# L5 pyhard[type parameter] assert/assume conforms(values, list[int]); boundary nondet over 16 closed tags
def collect(values: list[int]) -> list[int]:
    # L6 pyhard[flow collect in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment})
    # L6 pyhard[flow collect out] result -> (binding=definitely_bound; tags={list}; defs={assignment:L6:C5}; points-to={alloc:L6:C25}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment}); aliases may={result~values} must={}
    # L6 pyhard[type local_assignment] assert/assume conforms(result, list[int]); observed={list}
    result: list[int] = [
        # L7 pyhard[type call_argument] assert/assume conforms(value, int); observed={bool, int}
        increment(value)
        # L8 pyhard[read collect.values@22] binding=definitely_bound
        # L8 pyhard[dispatch values] assert/assume key in {list}
        # L8 pyhard[row {list}] call_iter; owner=list; label=builtins.list.__iter__; plan=[receiver.__iter__:builtins.list.__iter__]
        for value in values
        # L9 pyhard[dispatch value] assert/assume key in {bool, int}
        # L9 pyhard[row {bool, int}] exact_builtin_truth; result={bool}
        if value
    ]
    # L11 pyhard[flow collect in] result -> (binding=definitely_bound; tags={list}; defs={assignment:L6:C5}; points-to={alloc:L6:C25}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment}); aliases may={result~values} must={}
    # L11 pyhard[flow collect out:return] $result -> (binding=definitely_bound; tags={list}; defs={return}), result -> (binding=definitely_bound; tags={list}; defs={assignment:L6:C5}; points-to={alloc:L6:C25}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment}); aliases may={result~values} must={}
    # L11 pyhard[read collect.result@12] binding=definitely_bound
    # L11 pyhard[type return] assert/assume conforms(result, list[int]); observed={list}
    return result


# L14 pyhard[summary collect_unique] returns={set}; escapes={}
# L14 pyhard[type parameter] assert/assume conforms(values, list[int]); boundary nondet over 16 closed tags
def collect_unique(values: list[int]) -> set[int]:
    # L15 pyhard[flow collect_unique in] values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment})
    # L15 pyhard[flow collect_unique out:return] $result -> (binding=definitely_bound; tags={set}; defs={return}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment})
    # L15 pyhard[type return] assert/assume conforms(result, set[int]); observed={set}
    return {
        # L16 pyhard[type call_argument] assert/assume conforms(value, int); observed={bool, int}
        increment(value)
        # L17 pyhard[read collect_unique.values@22] binding=definitely_bound
        # L17 pyhard[dispatch values] assert/assume key in {list}
        # L17 pyhard[row {list}] call_iter; owner=list; label=builtins.list.__iter__; plan=[receiver.__iter__:builtins.list.__iter__]
        for value in values
        # L18 pyhard[dispatch value] assert/assume key in {bool, int}
        # L18 pyhard[row {bool, int}] exact_builtin_truth; result={bool}
        if value
    }


# L22 pyhard[summary copy_unordered] returns={list}; escapes={}
# L22 pyhard[type parameter] assert/assume conforms(values, set[int]); boundary nondet over 16 closed tags
def copy_unordered(values: set[int]) -> list[int]:
    # L23 pyhard[flow copy_unordered in] values -> (binding=definitely_bound; tags={set}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment})
    # L23 pyhard[flow copy_unordered out:return] $result -> (binding=definitely_bound; tags={list}; defs={return}), values -> (binding=definitely_bound; tags={set}; defs={param:values}; points-to={alloc:L15:C12, alloc:L23:C12, alloc:L6:C25, boundary:collect, boundary:collect_unique, boundary:copy_unordered, boundary:external, boundary:increment})
    # L23 pyhard[read copy_unordered.values@32] binding=definitely_bound
    # L23 pyhard[type return] assert/assume conforms(result, list[int]); observed={list}
    # L23 pyhard[dispatch values] assert/assume key in {set}
    # L23 pyhard[row {set}] call_iter; owner=set; label=builtins.set.__iter__; plan=[receiver.__iter__:builtins.set.__iter__]
    return [value for value in values]
