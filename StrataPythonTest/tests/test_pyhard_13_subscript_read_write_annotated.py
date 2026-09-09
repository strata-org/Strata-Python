# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary rewrite] returns={bool, int}; escapes={IndexError, KeyError}
def rewrite(
    # L2 pyhard[type parameter] assert/assume conforms(values, list[int]); boundary nondet over 16 closed tags
    values: list[int],
    # L3 pyhard[type parameter] assert/assume conforms(replacements, dict[str, int]); boundary nondet over 16 closed tags
    replacements: dict[str, int],
    # L4 pyhard[type parameter] assert/assume conforms(index, int); boundary nondet over 16 closed tags
    index: int,
) -> int:
    # L6 pyhard[flow rewrite in] index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L6 pyhard[flow rewrite out] index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L6:C5}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L6 pyhard[flow rewrite out:raise:KeyError] $exception -> (binding=definitely_bound; tags={KeyError}; defs={raise:KeyError}), index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L6 pyhard[read rewrite.replacements@19] binding=definitely_bound
    # L6 pyhard[type subscript_key] assert/assume conforms('value', str); observed={str}
    # L6 pyhard[dispatch replacements['value']] assert/assume key in {dict}
    # L6 pyhard[row {dict}] exact_dict; result={bool, int}; raises={KeyError}; specialized-by=index and recursive type contracts
    replacement = replacements["value"]
    # L7 pyhard[flow rewrite in] index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L6:C5}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L7 pyhard[flow rewrite out] index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L6:C5}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L7 pyhard[flow rewrite out:raise:IndexError] $exception -> (binding=definitely_bound; tags={IndexError}; defs={raise:IndexError}), index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L6:C5}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L7 pyhard[read rewrite.replacement@21] binding=definitely_bound
    # L7 pyhard[read rewrite.values@5] binding=definitely_bound
    # L7 pyhard[read rewrite.index@12] binding=definitely_bound
    # L7 pyhard[dispatch values[index]] assert/assume key in {list}
    # L7 pyhard[row {list}] exact_list; raises={IndexError}; specialized-by=index and recursive type contracts
    values[index] = replacement
    # L8 pyhard[flow rewrite in] index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L6:C5}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L8 pyhard[flow rewrite out:raise:IndexError] $exception -> (binding=definitely_bound; tags={IndexError}; defs={raise:IndexError}), index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L6:C5}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L8 pyhard[flow rewrite out:return] $result -> (binding=definitely_bound; tags={bool, int}; defs={return}), index -> (binding=definitely_bound; tags={bool, int}; defs={param:index}), replacement -> (binding=definitely_bound; tags={bool, int}; defs={assignment:L6:C5}), replacements -> (binding=definitely_bound; tags={dict}; defs={param:replacements}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite}); aliases may={replacements~values} must={}
    # L8 pyhard[read rewrite.values@12] binding=definitely_bound
    # L8 pyhard[read rewrite.index@19] binding=definitely_bound
    # L8 pyhard[type return] assert/assume conforms(result, int); observed={bool, int}; evaluation may raise={IndexError}
    # L8 pyhard[type subscript_key] assert/assume conforms(index, int | slice); observed={bool, int}
    # L8 pyhard[dispatch values[index]] assert/assume key in {list}
    # L8 pyhard[row {list}] exact_list; result={bool, int}; raises={IndexError}; specialized-by=index and recursive type contracts
    return values[index]


# L11 pyhard[summary fixed_tuple_read] returns={str}; escapes={}
# L11 pyhard[type parameter] assert/assume conforms(pair, tuple[int, str]); boundary nondet over 16 closed tags
def fixed_tuple_read(pair: tuple[int, str]) -> str:
    # L12 pyhard[flow fixed_tuple_read in] pair -> (binding=definitely_bound; tags={tuple}; defs={param:pair}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite})
    # L12 pyhard[flow fixed_tuple_read out:return] $result -> (binding=definitely_bound; tags={str}; defs={return}), pair -> (binding=definitely_bound; tags={tuple}; defs={param:pair}; points-to={alloc:L11:C34, alloc:L3:C24, boundary:external, boundary:fixed_tuple_read, boundary:rewrite})
    # L12 pyhard[read fixed_tuple_read.pair@12] binding=definitely_bound
    # L12 pyhard[type return] assert/assume conforms(result, str); observed={str}
    # L12 pyhard[type subscript_key] assert/assume conforms(1, int | slice); observed={int}
    # L12 pyhard[dispatch pair[1]] assert/assume key in {tuple}
    # L12 pyhard[row {tuple}] exact_tuple; result={str}; specialized-by=index and recursive type contracts
    return pair[1]
