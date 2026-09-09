# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary find_or_default] returns={bool, int}; escapes={}
# L1 pyhard[type parameter] assert/assume conforms(values, list[int]); boundary nondet over 16 closed tags
# L1 pyhard[type parameter] assert/assume conforms(target, int); boundary nondet over 16 closed tags
def find_or_default(values: list[int], target: int) -> int:
    # L2 pyhard[flow find_or_default in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L2 pyhard[flow find_or_default out] result -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L4:C13, assignment:L7:C9}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L2:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L2 pyhard[read find_or_default.values@18] binding=definitely_bound
    # L2 pyhard[dispatch values] assert/assume key in {list}
    # L2 pyhard[row {list}] call_iter; owner=list; label=builtins.list.__iter__; plan=[receiver.__iter__:builtins.list.__iter__]
    for value in values:
        # L3 pyhard[flow find_or_default in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L2:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L3 pyhard[flow find_or_default out] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L2:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L3 pyhard[flow find_or_default out:break] result -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L4:C13}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L2:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L3 pyhard[read find_or_default.value@12] binding=definitely_bound
        # L3 pyhard[read find_or_default.target@21] binding=definitely_bound
        # L3 pyhard[dispatch value == target] assert/assume key in {(bool, bool), (bool, int), (int, bool), (int, int)}
        # L3 pyhard[row {(bool, bool), (bool, int), (int, bool), (int, int)}] binary_protocol; result={bool}; terminal=certified_builtin_total
        # L3 pyhard[dispatch value == target] assert/assume key in {bool}
        # L3 pyhard[row {bool}] exact_builtin_truth; result={bool}
        if value == target:
            # L4 pyhard[flow find_or_default in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L2:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
            # L4 pyhard[flow find_or_default out] result -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L4:C13}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L2:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
            # L4 pyhard[read find_or_default.value@22] binding=definitely_bound
            result = value
            # L5 pyhard[flow find_or_default in] result -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L4:C13}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L2:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
            # L5 pyhard[flow find_or_default out:break] result -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L4:C13}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L2:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
            break
    else:
        # L7 pyhard[flow find_or_default in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L2:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L7 pyhard[flow find_or_default out] result -> (binding=definitely_bound; tags={int}; defs={assignment:L7:C9}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L2:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L7 pyhard[dispatch 0 - 1] assert/assume key in {(int, int)}
        # L7 pyhard[row {(int, int)}] binary_protocol; result={int}; terminal=certified_builtin_total
        result = 0 - 1
    # L8 pyhard[flow find_or_default in] result -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L4:C13, assignment:L7:C9}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L2:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L8 pyhard[flow find_or_default out:return] $result -> (binding=definitely_bound; tags={bool, int}; defs={return}), result -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L4:C13, assignment:L7:C9}), target -> (binding=definitely_bound; tags={bool, int}; defs={param:target}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L2:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L8 pyhard[read find_or_default.result@12] binding=definitely_bound
    # L8 pyhard[type return] assert/assume conforms(result, int); observed={bool, int}
    return result


# L11 pyhard[summary else_only] returns={int}; escapes={UnboundLocalError}
# L11 pyhard[type parameter] assert/assume conforms(values, list[int]); boundary nondet over 16 closed tags
def else_only(values: list[int]) -> int:
    # L12 pyhard[flow else_only in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L12 pyhard[flow else_only out] result -> (binding=maybe_bound; tags={int}; defs={assignment:L16:C9, unbound:result}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L12:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L12 pyhard[read else_only.values@18] binding=definitely_bound
    # L12 pyhard[dispatch values] assert/assume key in {list}
    # L12 pyhard[row {list}] call_iter; owner=list; label=builtins.list.__iter__; plan=[receiver.__iter__:builtins.list.__iter__]
    for value in values:
        # L13 pyhard[flow else_only in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L12:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L13 pyhard[flow else_only out] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L12:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L13 pyhard[flow else_only out:break] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L12:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L13 pyhard[read else_only.value@12] binding=definitely_bound
        # L13 pyhard[dispatch value] assert/assume key in {bool, int}
        # L13 pyhard[row {bool, int}] exact_builtin_truth; result={bool}
        if value:
            # L14 pyhard[flow else_only in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L12:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
            # L14 pyhard[flow else_only out:break] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), value -> (binding=definitely_bound; tags={bool, int}; defs={iteration:L12:C9}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
            break
    else:
        # L16 pyhard[flow else_only in] result -> (binding=definitely_unbound; tags={}; defs={unbound:result}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L12:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        # L16 pyhard[flow else_only out] result -> (binding=definitely_bound; tags={int}; defs={assignment:L16:C9}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L12:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
        result = 0
    # L17 pyhard[flow else_only in] result -> (binding=maybe_bound; tags={int}; defs={assignment:L16:C9, unbound:result}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L12:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L17 pyhard[flow else_only out:raise:UnboundLocalError] $exception -> (binding=definitely_bound; tags={UnboundLocalError}; defs={raise:UnboundLocalError}), result -> (binding=maybe_bound; tags={int}; defs={assignment:L16:C9, unbound:result}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L12:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L17 pyhard[flow else_only out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), result -> (binding=maybe_bound; tags={int}; defs={assignment:L16:C9, unbound:result}), value -> (binding=maybe_bound; tags={bool, int}; defs={iteration:L12:C9, unbound:value}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:else_only, boundary:external, boundary:find_or_default})
    # L17 pyhard[read else_only.result@12] binding=maybe_bound; may raise UnboundLocalError
    # L17 pyhard[type return] assert/assume conforms(result, int); observed={int}; evaluation may raise={UnboundLocalError}
    return result
