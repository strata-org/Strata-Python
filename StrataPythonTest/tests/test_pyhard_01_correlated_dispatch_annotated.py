# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class A:
    # L2 pyhard[summary A.only_a] returns={bool}; escapes={}
    def only_a(self) -> bool:
        # L3 pyhard[flow A.only_a in] self -> (binding=definitely_bound; tags={A}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, boundary:A.only_a, boundary:B.only_b, boundary:choose, boundary:external})
        # L3 pyhard[flow A.only_a out:return] $result -> (binding=definitely_bound; tags={bool}; defs={return}), self -> (binding=definitely_bound; tags={A}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, boundary:A.only_a, boundary:B.only_b, boundary:choose, boundary:external})
        # L3 pyhard[type return] assert/assume conforms(result, bool); observed={bool}
        return True


class B:
    # L7 pyhard[summary B.only_b] returns={int}; escapes={}
    def only_b(self) -> int:
        # L8 pyhard[flow B.only_b in] self -> (binding=definitely_bound; tags={B}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, boundary:A.only_a, boundary:B.only_b, boundary:choose, boundary:external})
        # L8 pyhard[flow B.only_b out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), self -> (binding=definitely_bound; tags={B}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, boundary:A.only_a, boundary:B.only_b, boundary:choose, boundary:external})
        # L8 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 5


# L11 pyhard[summary choose] returns={bool, int}; escapes={AttributeError}
# L11 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 18 closed tags
def choose(flag: bool) -> bool | int:
    # L12 pyhard[flow choose in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L12 pyhard[flow choose out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L12 pyhard[read choose.flag@8] binding=definitely_bound
    # L12 pyhard[dispatch flag] assert/assume key in {bool}
    # L12 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L13 pyhard[flow choose in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L13 pyhard[flow choose out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A}; defs={assignment:L13:C9}; points-to={alloc:L13:C17})
        value = A()
    else:
        # L15 pyhard[flow choose in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L15 pyhard[flow choose out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={B}; defs={assignment:L15:C9}; points-to={alloc:L15:C17})
        value = B()

    # L17 pyhard[flow choose in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L17 pyhard[flow choose out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L17 pyhard[flow choose out:raise:AttributeError] $exception -> (binding=definitely_bound; tags={AttributeError}; defs={raise:AttributeError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L17 pyhard[flow choose out:return] $result -> (binding=definitely_bound; tags={bool}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L17 pyhard[read choose.flag@8] binding=definitely_bound
    # L17 pyhard[dispatch flag] assert/assume key in {bool}
    # L17 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L18 pyhard[flow choose in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
        # L18 pyhard[flow choose out:raise:AttributeError] $exception -> (binding=definitely_bound; tags={AttributeError}; defs={raise:AttributeError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
        # L18 pyhard[flow choose out:return] $result -> (binding=definitely_bound; tags={bool}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
        # L18 pyhard[read choose.value@16] binding=definitely_bound
        # L18 pyhard[type return] assert/assume conforms(result, bool | int); observed={bool}; evaluation may raise={AttributeError}
        # L18 pyhard[dispatch value.only_a()] assert/assume key in {A, B}
        # L18 pyhard[row {A}] invoke_method; owner=A; label=A.only_a; result={bool}
        # L18 pyhard[row {B}] raise_attribute_error; raises={AttributeError}
        return value.only_a()
    # L19 pyhard[flow choose in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L19 pyhard[flow choose out:raise:AttributeError] $exception -> (binding=definitely_bound; tags={AttributeError}; defs={raise:AttributeError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L19 pyhard[flow choose out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L19 pyhard[read choose.value@12] binding=definitely_bound
    # L19 pyhard[type return] assert/assume conforms(result, bool | int); observed={int}; evaluation may raise={AttributeError}
    # L19 pyhard[dispatch value.only_b()] assert/assume key in {A, B}
    # L19 pyhard[row {A}] raise_attribute_error; raises={AttributeError}
    # L19 pyhard[row {B}] invoke_method; owner=B; label=B.only_b; result={int}
    return value.only_b()
