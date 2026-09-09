# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary conditional] returns={int}; escapes={UnboundLocalError}
# L1 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 16 closed tags
def conditional(flag: bool) -> int:
    # L2 pyhard[flow conditional in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L2 pyhard[flow conditional out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=maybe_bound; tags={int}; defs={assignment:L3:C9, unbound:value})
    # L2 pyhard[read conditional.flag@8] binding=definitely_bound
    # L2 pyhard[dispatch flag] assert/assume key in {bool}
    # L2 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L3 pyhard[flow conditional in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L3 pyhard[flow conditional out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={int}; defs={assignment:L3:C9})
        value = 10
    # L4 pyhard[flow conditional in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=maybe_bound; tags={int}; defs={assignment:L3:C9, unbound:value})
    # L4 pyhard[flow conditional out:raise:UnboundLocalError] $exception -> (binding=definitely_bound; tags={UnboundLocalError}; defs={raise:UnboundLocalError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=maybe_bound; tags={int}; defs={assignment:L3:C9, unbound:value})
    # L4 pyhard[flow conditional out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=maybe_bound; tags={int}; defs={assignment:L3:C9, unbound:value})
    # L4 pyhard[read conditional.value@12] binding=maybe_bound; may raise UnboundLocalError
    # L4 pyhard[type return] assert/assume conforms(result, int); observed={int}; evaluation may raise={UnboundLocalError}
    return value


# L7 pyhard[summary loop_assignment] returns={int}; escapes={UnboundLocalError}
# L7 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 16 closed tags
def loop_assignment(flag: bool) -> int:
    # L8 pyhard[flow loop_assignment in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), result -> (binding=definitely_unbound; tags={}; defs={unbound:result})
    # L8 pyhard[flow loop_assignment out] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9, param:flag}), result -> (binding=maybe_bound; tags={int}; defs={assignment:L9:C9, unbound:result})
    # L8 pyhard[read loop_assignment.flag@11] binding=definitely_bound
    # L8 pyhard[dispatch flag] assert/assume key in {bool}
    # L8 pyhard[row {bool}] exact_builtin_truth; result={bool}
    while flag:
        # L9 pyhard[flow loop_assignment in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9, param:flag}), result -> (binding=maybe_bound; tags={int}; defs={assignment:L9:C9, unbound:result})
        # L9 pyhard[flow loop_assignment out] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9, param:flag}), result -> (binding=definitely_bound; tags={int}; defs={assignment:L9:C9})
        result = 1
        # L10 pyhard[flow loop_assignment in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9, param:flag}), result -> (binding=definitely_bound; tags={int}; defs={assignment:L9:C9})
        # L10 pyhard[flow loop_assignment out] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9}), result -> (binding=definitely_bound; tags={int}; defs={assignment:L9:C9})
        flag = False
    # L11 pyhard[flow loop_assignment in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9, param:flag}), result -> (binding=maybe_bound; tags={int}; defs={assignment:L9:C9, unbound:result})
    # L11 pyhard[flow loop_assignment out:raise:UnboundLocalError] $exception -> (binding=definitely_bound; tags={UnboundLocalError}; defs={raise:UnboundLocalError}), flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9, param:flag}), result -> (binding=maybe_bound; tags={int}; defs={assignment:L9:C9, unbound:result})
    # L11 pyhard[flow loop_assignment out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L10:C9, param:flag}), result -> (binding=maybe_bound; tags={int}; defs={assignment:L9:C9, unbound:result})
    # L11 pyhard[read loop_assignment.result@12] binding=maybe_bound; may raise UnboundLocalError
    # L11 pyhard[type return] assert/assume conforms(result, int); observed={int}; evaluation may raise={UnboundLocalError}
    return result


# L14 pyhard[summary both_branches] returns={int}; escapes={}
# L14 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 16 closed tags
def both_branches(flag: bool) -> int:
    # L15 pyhard[flow both_branches in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_unbound; tags={}; defs={unbound:stable})
    # L15 pyhard[flow both_branches out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_bound; tags={int}; defs={assignment:L16:C9, assignment:L18:C9})
    # L15 pyhard[read both_branches.flag@8] binding=definitely_bound
    # L15 pyhard[dispatch flag] assert/assume key in {bool}
    # L15 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L16 pyhard[flow both_branches in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_unbound; tags={}; defs={unbound:stable})
        # L16 pyhard[flow both_branches out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_bound; tags={int}; defs={assignment:L16:C9})
        stable = 1
    else:
        # L18 pyhard[flow both_branches in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_unbound; tags={}; defs={unbound:stable})
        # L18 pyhard[flow both_branches out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_bound; tags={int}; defs={assignment:L18:C9})
        stable = 2
    # L19 pyhard[flow both_branches in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_bound; tags={int}; defs={assignment:L16:C9, assignment:L18:C9})
    # L19 pyhard[flow both_branches out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), stable -> (binding=definitely_bound; tags={int}; defs={assignment:L16:C9, assignment:L18:C9})
    # L19 pyhard[read both_branches.stable@12] binding=definitely_bound
    # L19 pyhard[type return] assert/assume conforms(result, int); observed={int}
    return stable
