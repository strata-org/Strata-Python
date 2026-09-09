# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class A:
    # L2 pyhard[summary A.marker] returns={int}; escapes={}
    def marker(self) -> int:
        # L3 pyhard[flow A.marker in] self -> (binding=definitely_bound; tags={A}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, alloc:L25:C17, alloc:L27:C17, boundary:A.marker, boundary:B.marker, boundary:external, boundary:finite_loop, boundary:killed_difference, boundary:reassigned_guard, boundary:unchanged_guard})
        # L3 pyhard[flow A.marker out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), self -> (binding=definitely_bound; tags={A}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, alloc:L25:C17, alloc:L27:C17, boundary:A.marker, boundary:B.marker, boundary:external, boundary:finite_loop, boundary:killed_difference, boundary:reassigned_guard, boundary:unchanged_guard})
        # L3 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 1


class B:
    # L7 pyhard[summary B.marker] returns={int}; escapes={}
    def marker(self) -> int:
        # L8 pyhard[flow B.marker in] self -> (binding=definitely_bound; tags={B}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, alloc:L25:C17, alloc:L27:C17, boundary:A.marker, boundary:B.marker, boundary:external, boundary:finite_loop, boundary:killed_difference, boundary:reassigned_guard, boundary:unchanged_guard})
        # L8 pyhard[flow B.marker out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), self -> (binding=definitely_bound; tags={B}; defs={param:self}; points-to={alloc:L13:C17, alloc:L15:C17, alloc:L25:C17, alloc:L27:C17, boundary:A.marker, boundary:B.marker, boundary:external, boundary:finite_loop, boundary:killed_difference, boundary:reassigned_guard, boundary:unchanged_guard})
        # L8 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 2


# L11 pyhard[summary reassigned_guard] returns={int}; escapes={}
# L11 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 18 closed tags
def reassigned_guard(flag: bool) -> int:
    # L12 pyhard[flow reassigned_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L12 pyhard[flow reassigned_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L12 pyhard[read reassigned_guard.flag@8] binding=definitely_bound
    # L12 pyhard[dispatch flag] assert/assume key in {bool}
    # L12 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L13 pyhard[flow reassigned_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L13 pyhard[flow reassigned_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A}; defs={assignment:L13:C9}; points-to={alloc:L13:C17})
        value = A()
    else:
        # L15 pyhard[flow reassigned_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L15 pyhard[flow reassigned_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={B}; defs={assignment:L15:C9}; points-to={alloc:L15:C17})
        value = B()

    # L17 pyhard[flow reassigned_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L17 pyhard[flow reassigned_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L17 pyhard[read reassigned_guard.flag@16] binding=definitely_bound
    # L17 pyhard[dispatch flag] assert/assume key in {bool}
    # L17 pyhard[row {bool}] exact_builtin_truth; result={bool}
    flag = not flag
    # L18 pyhard[flow reassigned_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L18 pyhard[flow reassigned_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L18 pyhard[flow reassigned_guard out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L18 pyhard[read reassigned_guard.flag@8] binding=definitely_bound
    # L18 pyhard[dispatch flag] assert/assume key in {bool}
    # L18 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L19 pyhard[flow reassigned_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
        # L19 pyhard[flow reassigned_guard out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
        # L19 pyhard[read reassigned_guard.value@16] binding=definitely_bound
        # L19 pyhard[type return] assert/assume conforms(result, int); observed={int}
        # L19 pyhard[dispatch value.marker()] assert/assume key in {A, B}
        # L19 pyhard[row {A}] invoke_method; owner=A; label=A.marker; result={int}
        # L19 pyhard[row {B}] invoke_method; owner=B; label=B.marker; result={int}
        return value.marker()
    # L20 pyhard[flow reassigned_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L20 pyhard[flow reassigned_guard out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L17:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L13:C9, assignment:L15:C9}; points-to={alloc:L13:C17, alloc:L15:C17})
    # L20 pyhard[read reassigned_guard.value@12] binding=definitely_bound
    # L20 pyhard[type return] assert/assume conforms(result, int); observed={int}
    # L20 pyhard[dispatch value.marker()] assert/assume key in {A, B}
    # L20 pyhard[row {A}] invoke_method; owner=A; label=A.marker; result={int}
    # L20 pyhard[row {B}] invoke_method; owner=B; label=B.marker; result={int}
    return value.marker()


# L23 pyhard[summary unchanged_guard] returns={int}; escapes={}
# L23 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 18 closed tags
def unchanged_guard(flag: bool) -> int:
    # L24 pyhard[flow unchanged_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_unbound; tags={}; defs={unbound:other}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L24 pyhard[flow unchanged_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_unbound; tags={}; defs={unbound:other}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L24 pyhard[read unchanged_guard.flag@8] binding=definitely_bound
    # L24 pyhard[dispatch flag] assert/assume key in {bool}
    # L24 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L25 pyhard[flow unchanged_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_unbound; tags={}; defs={unbound:other}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L25 pyhard[flow unchanged_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_unbound; tags={}; defs={unbound:other}), value -> (binding=definitely_bound; tags={A}; defs={assignment:L25:C9}; points-to={alloc:L25:C17})
        value = A()
    else:
        # L27 pyhard[flow unchanged_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_unbound; tags={}; defs={unbound:other}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L27 pyhard[flow unchanged_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_unbound; tags={}; defs={unbound:other}), value -> (binding=definitely_bound; tags={B}; defs={assignment:L27:C9}; points-to={alloc:L27:C17})
        value = B()

    # L29 pyhard[flow unchanged_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_unbound; tags={}; defs={unbound:other}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L29 pyhard[flow unchanged_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L29 pyhard[read unchanged_guard.flag@17] binding=definitely_bound
    # L29 pyhard[dispatch flag] assert/assume key in {bool}
    # L29 pyhard[row {bool}] exact_builtin_truth; result={bool}
    other = not flag
    # L30 pyhard[flow unchanged_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L30 pyhard[flow unchanged_guard out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L30 pyhard[flow unchanged_guard out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L30 pyhard[read unchanged_guard.flag@8] binding=definitely_bound
    # L30 pyhard[dispatch flag] assert/assume key in {bool}
    # L30 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L31 pyhard[flow unchanged_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
        # L31 pyhard[flow unchanged_guard out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
        # L31 pyhard[read unchanged_guard.value@16] binding=definitely_bound
        # L31 pyhard[type return] assert/assume conforms(result, int); observed={int}
        # L31 pyhard[dispatch value.marker()] assert/assume key in {A, B}
        # L31 pyhard[row {A}] invoke_method; owner=A; label=A.marker; result={int}
        # L31 pyhard[row {B}] invoke_method; owner=B; label=B.marker; result={int}
        return value.marker()
    # L32 pyhard[flow unchanged_guard in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L32 pyhard[flow unchanged_guard out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), other -> (binding=definitely_bound; tags={bool}; defs={assignment:L29:C5}), value -> (binding=definitely_bound; tags={A, B}; defs={assignment:L25:C9, assignment:L27:C9}; points-to={alloc:L25:C17, alloc:L27:C17})
    # L32 pyhard[read unchanged_guard.value@12] binding=definitely_bound
    # L32 pyhard[type return] assert/assume conforms(result, int); observed={int}
    # L32 pyhard[dispatch value.marker()] assert/assume key in {A, B}
    # L32 pyhard[row {A}] invoke_method; owner=A; label=A.marker; result={int}
    # L32 pyhard[row {B}] invoke_method; owner=B; label=B.marker; result={int}
    return value.marker()


# L35 pyhard[summary killed_difference] returns={int}; escapes={}
# L35 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 18 closed tags
def killed_difference(flag: bool) -> int:
    # L36 pyhard[flow killed_difference in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L36 pyhard[flow killed_difference out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={int, str}; defs={assignment:L37:C9, assignment:L39:C9})
    # L36 pyhard[read killed_difference.flag@8] binding=definitely_bound
    # L36 pyhard[dispatch flag] assert/assume key in {bool}
    # L36 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L37 pyhard[flow killed_difference in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L37 pyhard[flow killed_difference out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={int}; defs={assignment:L37:C9})
        value = 1
    else:
        # L39 pyhard[flow killed_difference in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
        # L39 pyhard[flow killed_difference out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={str}; defs={assignment:L39:C9})
        value = "old"

    # L41 pyhard[flow killed_difference in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={int, str}; defs={assignment:L37:C9, assignment:L39:C9})
    # L41 pyhard[flow killed_difference out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={int}; defs={assignment:L41:C5})
    value = 0
    # L42 pyhard[flow killed_difference in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={int}; defs={assignment:L41:C5})
    # L42 pyhard[flow killed_difference out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), value -> (binding=definitely_bound; tags={int}; defs={assignment:L41:C5})
    # L42 pyhard[read killed_difference.value@12] binding=definitely_bound
    # L42 pyhard[type return] assert/assume conforms(result, int); observed={int}
    # L42 pyhard[dispatch value + 1] assert/assume key in {(int, int)}
    # L42 pyhard[row {(int, int)}] binary_protocol; result={int}; terminal=certified_builtin_total
    return value + 1


# L45 pyhard[summary finite_loop] returns={bool}; escapes={}
# L45 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 18 closed tags
def finite_loop(flag: bool) -> bool:
    # L46 pyhard[flow finite_loop in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag})
    # L46 pyhard[flow finite_loop out] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L47:C9, param:flag})
    # L46 pyhard[read finite_loop.flag@11] binding=definitely_bound
    # L46 pyhard[dispatch flag] assert/assume key in {bool}
    # L46 pyhard[row {bool}] exact_builtin_truth; result={bool}
    while flag:
        # L47 pyhard[flow finite_loop in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L47:C9, param:flag})
        # L47 pyhard[flow finite_loop out] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L47:C9})
        # L47 pyhard[read finite_loop.flag@20] binding=definitely_bound
        # L47 pyhard[dispatch flag] assert/assume key in {bool}
        # L47 pyhard[row {bool}] exact_builtin_truth; result={bool}
        flag = not flag
    # L48 pyhard[flow finite_loop in] flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L47:C9, param:flag})
    # L48 pyhard[flow finite_loop out:return] $result -> (binding=definitely_bound; tags={bool}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={assignment:L47:C9, param:flag})
    # L48 pyhard[read finite_loop.flag@12] binding=definitely_bound
    # L48 pyhard[type return] assert/assume conforms(result, bool); observed={bool}
    return flag
