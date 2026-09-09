# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary choose] returns={bool, int, str}; escapes={}
# L1 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 16 closed tags
# L1 pyhard[type parameter] assert/assume conforms(number, int); boundary nondet over 16 closed tags
# L1 pyhard[type parameter] assert/assume conforms(text, str); boundary nondet over 16 closed tags
def choose(flag: bool, number: int, text: str) -> int | str:
    # L2 pyhard[flow choose in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), number -> (binding=definitely_bound; tags={bool, int}; defs={param:number}), text -> (binding=definitely_bound; tags={str}; defs={param:text})
    # L2 pyhard[flow choose out:return] $result -> (binding=definitely_bound; tags={bool, int, str}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), number -> (binding=definitely_bound; tags={bool, int}; defs={param:number}), text -> (binding=definitely_bound; tags={str}; defs={param:text})
    # L2 pyhard[read choose.flag@22] binding=definitely_bound
    # L2 pyhard[read choose.number@12] binding=definitely_bound
    # L2 pyhard[read choose.text@32] binding=definitely_bound
    # L2 pyhard[type return] assert/assume conforms(result, int | str); observed={bool, int, str}
    # L2 pyhard[dispatch flag] assert/assume key in {bool}
    # L2 pyhard[row {bool}] exact_builtin_truth; result={bool}
    return number if flag else text


# L5 pyhard[summary guarded_head] returns={bool, int}; escapes={IndexError}
def guarded_head(
    # L6 pyhard[type parameter] assert/assume conforms(use_default, bool); boundary nondet over 16 closed tags
    use_default: bool,
    # L7 pyhard[type parameter] assert/assume conforms(values, list[int]); boundary nondet over 16 closed tags
    values: list[int],
) -> int:
    # L9 pyhard[flow guarded_head in] use_default -> (binding=definitely_bound; tags={bool}; defs={param:use_default}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:choose, boundary:external, boundary:guarded_head})
    # L9 pyhard[flow guarded_head out:raise:IndexError] $exception -> (binding=definitely_bound; tags={IndexError}; defs={raise:IndexError}), use_default -> (binding=definitely_bound; tags={bool}; defs={param:use_default}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:choose, boundary:external, boundary:guarded_head})
    # L9 pyhard[flow guarded_head out:return] $result -> (binding=definitely_bound; tags={bool, int}; defs={return}), use_default -> (binding=definitely_bound; tags={bool}; defs={param:use_default}), values -> (binding=definitely_bound; tags={list}; defs={param:values}; points-to={boundary:choose, boundary:external, boundary:guarded_head})
    # L9 pyhard[read guarded_head.use_default@17] binding=definitely_bound
    # L9 pyhard[read guarded_head.values@34] binding=definitely_bound
    # L9 pyhard[type return] assert/assume conforms(result, int); observed={bool, int}; evaluation may raise={IndexError}
    # L9 pyhard[type subscript_key] assert/assume conforms(0, int | slice); observed={int}
    # L9 pyhard[dispatch use_default] assert/assume key in {bool}
    # L9 pyhard[row {bool}] exact_builtin_truth; result={bool}
    # L9 pyhard[dispatch values[0]] assert/assume key in {list}
    # L9 pyhard[row {list}] exact_list; result={bool, int}; raises={IndexError}; specialized-by=index and recursive type contracts
    return 0 if use_default else values[0]
