# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary branch_alias] returns={list}; escapes={}
def branch_alias(
    # L2 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 16 closed tags
    flag: bool,
    # L3 pyhard[type parameter] assert/assume conforms(left, list[int]); boundary nondet over 16 closed tags
    left: list[int],
    # L4 pyhard[type parameter] assert/assume conforms(right, list[int]); boundary nondet over 16 closed tags
    right: list[int],
) -> list[int]:
    # L6 pyhard[flow branch_alias in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}); aliases may={left~right} must={}
    # L6 pyhard[flow branch_alias out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_bound; tags={list}; defs={assignment:L7:C9, assignment:L9:C9}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}); aliases may={left~right, left~selected, right~selected} must={}
    # L6 pyhard[read branch_alias.flag@8] binding=definitely_bound
    # L6 pyhard[dispatch flag] assert/assume key in {bool}
    # L6 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L7 pyhard[flow branch_alias in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}); aliases may={left~right} must={}
        # L7 pyhard[flow branch_alias out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_bound; tags={list}; defs={assignment:L7:C9}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}); aliases may={left~right, left~selected, right~selected} must={left~selected}
        # L7 pyhard[read branch_alias.left@20] binding=definitely_bound
        selected = left
    else:
        # L9 pyhard[flow branch_alias in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}); aliases may={left~right} must={}
        # L9 pyhard[flow branch_alias out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_bound; tags={list}; defs={assignment:L9:C9}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}); aliases may={left~right, left~selected, right~selected} must={right~selected}
        # L9 pyhard[read branch_alias.right@20] binding=definitely_bound
        selected = right
    # L10 pyhard[flow branch_alias in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_bound; tags={list}; defs={assignment:L7:C9, assignment:L9:C9}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}); aliases may={left~right, left~selected, right~selected} must={}
    # L10 pyhard[flow branch_alias out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_bound; tags={list}; defs={assignment:L7:C9, assignment:L9:C9}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}); aliases may={left~right, left~selected, right~selected} must={}
    # L10 pyhard[read branch_alias.selected@5] binding=definitely_bound
    # L10 pyhard[dispatch selected.append(1)] assert/assume key in {list}
    # L10 pyhard[row {list}] invoke_builtin_method; owner=list; label=builtins.list.append; result={NoneType}
    selected.append(1)
    # L11 pyhard[flow branch_alias in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_bound; tags={list}; defs={assignment:L7:C9, assignment:L9:C9}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}); aliases may={left~right, left~selected, right~selected} must={}
    # L11 pyhard[flow branch_alias out:return] $result -> (binding=definitely_bound; tags={list}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={list}; defs={param:left}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), right -> (binding=definitely_bound; tags={list}; defs={param:right}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}), selected -> (binding=definitely_bound; tags={list}; defs={assignment:L7:C9, assignment:L9:C9}; points-to={alloc:L15:C16, alloc:L23:C16, alloc:L25:C16, boundary:branch_alias, boundary:delete_one_name, boundary:external, boundary:rebind_one_name}); aliases may={left~right, left~selected, right~selected} must={}
    # L11 pyhard[read branch_alias.selected@12] binding=definitely_bound
    # L11 pyhard[type return] assert/assume conforms(result, list[int]); observed={list}
    return selected


# L14 pyhard[summary delete_one_name] returns={list}; escapes={}
def delete_one_name() -> list[int]:
    # L15 pyhard[flow delete_one_name in] alias -> (binding=definitely_unbound; tags={}; defs={unbound:alias}), original -> (binding=definitely_unbound; tags={}; defs={unbound:original})
    # L15 pyhard[flow delete_one_name out] alias -> (binding=definitely_unbound; tags={}; defs={unbound:alias}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L15:C5}; points-to={alloc:L15:C16})
    original = []
    # L16 pyhard[flow delete_one_name in] alias -> (binding=definitely_unbound; tags={}; defs={unbound:alias}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L15:C5}; points-to={alloc:L15:C16})
    # L16 pyhard[flow delete_one_name out] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L16:C5}; points-to={alloc:L15:C16}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L15:C5}; points-to={alloc:L15:C16}); aliases may={alias~original} must={alias~original}
    # L16 pyhard[read delete_one_name.original@13] binding=definitely_bound
    alias = original
    # L17 pyhard[flow delete_one_name in] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L16:C5}; points-to={alloc:L15:C16}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L15:C5}; points-to={alloc:L15:C16}); aliases may={alias~original} must={alias~original}
    # L17 pyhard[flow delete_one_name out] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L16:C5}; points-to={alloc:L15:C16}), original -> (binding=definitely_unbound; tags={}; defs={delete:L17:C9})
    # L17 pyhard[read delete_one_name.original@9] binding=definitely_bound
    del original
    # L18 pyhard[flow delete_one_name in] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L16:C5}; points-to={alloc:L15:C16}), original -> (binding=definitely_unbound; tags={}; defs={delete:L17:C9})
    # L18 pyhard[flow delete_one_name out] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L16:C5}; points-to={alloc:L15:C16}), original -> (binding=definitely_unbound; tags={}; defs={delete:L17:C9})
    # L18 pyhard[read delete_one_name.alias@5] binding=definitely_bound
    # L18 pyhard[dispatch alias.append(1)] assert/assume key in {list}
    # L18 pyhard[row {list}] invoke_builtin_method; owner=list; label=builtins.list.append; result={NoneType}
    alias.append(1)
    # L19 pyhard[flow delete_one_name in] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L16:C5}; points-to={alloc:L15:C16}), original -> (binding=definitely_unbound; tags={}; defs={delete:L17:C9})
    # L19 pyhard[flow delete_one_name out:return] $result -> (binding=definitely_bound; tags={list}; defs={return}), alias -> (binding=definitely_bound; tags={list}; defs={assignment:L16:C5}; points-to={alloc:L15:C16}), original -> (binding=definitely_unbound; tags={}; defs={delete:L17:C9})
    # L19 pyhard[read delete_one_name.alias@12] binding=definitely_bound
    # L19 pyhard[type return] assert/assume conforms(result, list[int]); observed={list}
    return alias


# L22 pyhard[summary rebind_one_name] returns={list}; escapes={}
def rebind_one_name() -> list[int]:
    # L23 pyhard[flow rebind_one_name in] alias -> (binding=definitely_unbound; tags={}; defs={unbound:alias}), original -> (binding=definitely_unbound; tags={}; defs={unbound:original})
    # L23 pyhard[flow rebind_one_name out] alias -> (binding=definitely_unbound; tags={}; defs={unbound:alias}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L23:C5}; points-to={alloc:L23:C16})
    original = []
    # L24 pyhard[flow rebind_one_name in] alias -> (binding=definitely_unbound; tags={}; defs={unbound:alias}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L23:C5}; points-to={alloc:L23:C16})
    # L24 pyhard[flow rebind_one_name out] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L24:C5}; points-to={alloc:L23:C16}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L23:C5}; points-to={alloc:L23:C16}); aliases may={alias~original} must={alias~original}
    # L24 pyhard[read rebind_one_name.original@13] binding=definitely_bound
    alias = original
    # L25 pyhard[flow rebind_one_name in] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L24:C5}; points-to={alloc:L23:C16}), original -> (binding=definitely_bound; tags={list}; defs={assignment:L23:C5}; points-to={alloc:L23:C16}); aliases may={alias~original} must={alias~original}
    # L25 pyhard[flow rebind_one_name out] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L24:C5}; points-to={alloc:L23:C16}), original -> (binding=definitely_bound; tags={dict}; defs={assignment:L25:C5}; points-to={alloc:L25:C16})
    original = {}
    # L26 pyhard[flow rebind_one_name in] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L24:C5}; points-to={alloc:L23:C16}), original -> (binding=definitely_bound; tags={dict}; defs={assignment:L25:C5}; points-to={alloc:L25:C16})
    # L26 pyhard[flow rebind_one_name out] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L24:C5}; points-to={alloc:L23:C16}), original -> (binding=definitely_bound; tags={dict}; defs={assignment:L25:C5}; points-to={alloc:L25:C16})
    # L26 pyhard[read rebind_one_name.alias@5] binding=definitely_bound
    # L26 pyhard[dispatch alias.append(1)] assert/assume key in {list}
    # L26 pyhard[row {list}] invoke_builtin_method; owner=list; label=builtins.list.append; result={NoneType}
    alias.append(1)
    # L27 pyhard[flow rebind_one_name in] alias -> (binding=definitely_bound; tags={list}; defs={assignment:L24:C5}; points-to={alloc:L23:C16}), original -> (binding=definitely_bound; tags={dict}; defs={assignment:L25:C5}; points-to={alloc:L25:C16})
    # L27 pyhard[flow rebind_one_name out:return] $result -> (binding=definitely_bound; tags={list}; defs={return}), alias -> (binding=definitely_bound; tags={list}; defs={assignment:L24:C5}; points-to={alloc:L23:C16}), original -> (binding=definitely_bound; tags={dict}; defs={assignment:L25:C5}; points-to={alloc:L25:C16})
    # L27 pyhard[read rebind_one_name.alias@12] binding=definitely_bound
    # L27 pyhard[type return] assert/assume conforms(result, list[int]); observed={list}
    return alias
