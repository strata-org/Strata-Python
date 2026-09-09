# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary choose_mapping] returns={dict}; escapes={}
def choose_mapping(
    # L2 pyhard[type parameter] assert/assume conforms(primary, NoneType | dict[str, int]); boundary nondet over 16 closed tags
    primary: dict[str, int] | None,
    # L3 pyhard[type parameter] assert/assume conforms(fallback, dict[str, int]); boundary nondet over 16 closed tags
    fallback: dict[str, int],
) -> dict[str, int]:
    # L5 pyhard[flow choose_mapping in] fallback -> (binding=definitely_bound; tags={dict}; defs={param:fallback}; points-to={alloc:L2:C19, alloc:L3:C20, alloc:L4:C11, boundary:choose_mapping, boundary:choose_scalar, boundary:external}), primary -> (binding=definitely_bound; tags={NoneType, dict}; defs={param:primary}; points-to={alloc:L2:C19, alloc:L3:C20, alloc:L4:C11, boundary:choose_mapping, boundary:choose_scalar, boundary:external}); aliases may={fallback~primary} must={}
    # L5 pyhard[flow choose_mapping out:return] $result -> (binding=definitely_bound; tags={NoneType, dict}; defs={return}), fallback -> (binding=definitely_bound; tags={dict}; defs={param:fallback}; points-to={alloc:L2:C19, alloc:L3:C20, alloc:L4:C11, boundary:choose_mapping, boundary:choose_scalar, boundary:external}), primary -> (binding=definitely_bound; tags={NoneType, dict}; defs={param:primary}; points-to={alloc:L2:C19, alloc:L3:C20, alloc:L4:C11, boundary:choose_mapping, boundary:choose_scalar, boundary:external}); aliases may={fallback~primary} must={}
    # L5 pyhard[read choose_mapping.primary@12] binding=definitely_bound
    # L5 pyhard[read choose_mapping.fallback@23] binding=definitely_bound
    # L5 pyhard[type return] assert/assume conforms(result, dict[str, int]); observed={NoneType, dict}
    # L5 pyhard[dispatch primary] assert/assume key in {NoneType, dict}
    # L5 pyhard[row {NoneType, dict}] exact_builtin_truth; result={bool}
    return primary or fallback


# L8 pyhard[summary choose_scalar] returns={bool, int, str}; escapes={}
# L8 pyhard[type parameter] assert/assume conforms(primary, int); boundary nondet over 16 closed tags
# L8 pyhard[type parameter] assert/assume conforms(fallback, str); boundary nondet over 16 closed tags
def choose_scalar(primary: int, fallback: str) -> int | str:
    # L9 pyhard[flow choose_scalar in] fallback -> (binding=definitely_bound; tags={str}; defs={param:fallback}), primary -> (binding=definitely_bound; tags={bool, int}; defs={param:primary})
    # L9 pyhard[flow choose_scalar out:return] $result -> (binding=definitely_bound; tags={bool, int, str}; defs={return}), fallback -> (binding=definitely_bound; tags={str}; defs={param:fallback}), primary -> (binding=definitely_bound; tags={bool, int}; defs={param:primary})
    # L9 pyhard[read choose_scalar.primary@12] binding=definitely_bound
    # L9 pyhard[read choose_scalar.fallback@23] binding=definitely_bound
    # L9 pyhard[type return] assert/assume conforms(result, int | str); observed={bool, int, str}
    # L9 pyhard[dispatch primary] assert/assume key in {bool, int}
    # L9 pyhard[row {bool, int}] exact_builtin_truth; result={bool}
    return primary or fallback
