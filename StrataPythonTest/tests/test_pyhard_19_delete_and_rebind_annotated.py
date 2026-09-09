# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary delete_then_rebind] returns={int}; escapes={}
def delete_then_rebind() -> int:
    # L2 pyhard[flow delete_then_rebind in] value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L2 pyhard[flow delete_then_rebind out] value -> (binding=definitely_bound; tags={int}; defs={assignment:L2:C5})
    value = 1
    # L3 pyhard[flow delete_then_rebind in] value -> (binding=definitely_bound; tags={int}; defs={assignment:L2:C5})
    # L3 pyhard[flow delete_then_rebind out] value -> (binding=definitely_unbound; tags={}; defs={delete:L3:C9})
    # L3 pyhard[read delete_then_rebind.value@9] binding=definitely_bound
    del value
    # L4 pyhard[flow delete_then_rebind in] value -> (binding=definitely_unbound; tags={}; defs={delete:L3:C9})
    # L4 pyhard[flow delete_then_rebind out] value -> (binding=definitely_bound; tags={int}; defs={assignment:L4:C5})
    value = 2
    # L5 pyhard[flow delete_then_rebind in] value -> (binding=definitely_bound; tags={int}; defs={assignment:L4:C5})
    # L5 pyhard[flow delete_then_rebind out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), value -> (binding=definitely_bound; tags={int}; defs={assignment:L4:C5})
    # L5 pyhard[read delete_then_rebind.value@12] binding=definitely_bound
    # L5 pyhard[type return] assert/assume conforms(result, int); observed={int}
    return value


# L8 pyhard[summary delete_then_read] returns={}; escapes={UnboundLocalError}
def delete_then_read() -> int:
    # L9 pyhard[flow delete_then_read in] value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L9 pyhard[flow delete_then_read out] value -> (binding=definitely_bound; tags={int}; defs={assignment:L9:C5})
    value = 1
    # L10 pyhard[flow delete_then_read in] value -> (binding=definitely_bound; tags={int}; defs={assignment:L9:C5})
    # L10 pyhard[flow delete_then_read out] value -> (binding=definitely_unbound; tags={}; defs={delete:L10:C9})
    # L10 pyhard[read delete_then_read.value@9] binding=definitely_bound
    del value
    # L11 pyhard[flow delete_then_read in] value -> (binding=definitely_unbound; tags={}; defs={delete:L10:C9})
    # L11 pyhard[flow delete_then_read out:raise:UnboundLocalError] $exception -> (binding=definitely_bound; tags={UnboundLocalError}; defs={raise:UnboundLocalError}), value -> (binding=definitely_unbound; tags={}; defs={delete:L10:C9})
    # L11 pyhard[read delete_then_read.value@12] binding=definitely_unbound; may raise UnboundLocalError
    # L11 pyhard[type return] assert/assume conforms(result, int); observed={}; evaluation may raise={UnboundLocalError}
    return value
