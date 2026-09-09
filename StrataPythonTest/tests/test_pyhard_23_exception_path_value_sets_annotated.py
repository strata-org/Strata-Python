# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class Early:
    # L2 pyhard[summary Early.marker] returns={int}; escapes={}
    def marker(self) -> int:
        # L3 pyhard[flow Early.marker in] self -> (binding=definitely_bound; tags={Early}; defs={param:self}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler})
        # L3 pyhard[flow Early.marker out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), self -> (binding=definitely_bound; tags={Early}; defs={param:self}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler})
        # L3 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 1


class Late:
    # L7 pyhard[summary Late.marker] returns={str}; escapes={}
    def marker(self) -> str:
        # L8 pyhard[flow Late.marker in] self -> (binding=definitely_bound; tags={Late}; defs={param:self}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler})
        # L8 pyhard[flow Late.marker out:return] $result -> (binding=definitely_bound; tags={str}; defs={return}), self -> (binding=definitely_bound; tags={Late}; defs={param:self}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler})
        # L8 pyhard[type return] assert/assume conforms(result, str); observed={str}
        return "late"


class RouteError(Exception):
    pass


# L15 pyhard[summary split_at_handler] returns={int, str}; escapes={}
# L15 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 19 closed tags
def split_at_handler(flag: bool) -> int | str:
    # L16 pyhard[flow split_at_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L16 pyhard[flow split_at_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
    value = Early()
    # L17 pyhard[flow split_at_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
    # L17 pyhard[flow split_at_handler out:return] $result -> (binding=definitely_bound; tags={int, str}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L21:C5, unbound:route_error}), value -> (binding=definitely_bound; tags={Early, Late}; defs={assignment:L16:C5, assignment:L20:C9}; points-to={alloc:L16:C13, alloc:L20:C17})
    try:
        # L18 pyhard[flow split_at_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
        # L18 pyhard[flow split_at_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
        # L18 pyhard[flow split_at_handler out:raise:RouteError] $exception -> (binding=definitely_bound; tags={RouteError}; defs={raise:RouteError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
        # L18 pyhard[read split_at_handler.flag@12] binding=definitely_bound
        # L18 pyhard[dispatch flag] assert/assume key in {bool}
        # L18 pyhard[row {bool}] exact_builtin_truth; result={bool}
        if flag:
            # L19 pyhard[flow split_at_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
            # L19 pyhard[flow split_at_handler out:raise:RouteError] $exception -> (binding=definitely_bound; tags={RouteError}; defs={raise:RouteError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
            raise RouteError()
        # L20 pyhard[flow split_at_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13})
        # L20 pyhard[flow split_at_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Late}; defs={assignment:L20:C9}; points-to={alloc:L20:C17})
        value = Late()
    except RouteError as route_error:
        # L22 pyhard[flow split_at_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_bound; tags={RouteError}; defs={handler:L21:C5}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13}); aliases may={route_error~value} must={}
        # L22 pyhard[flow split_at_handler out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_bound; tags={RouteError}; defs={handler:L21:C5}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L16:C5}; points-to={alloc:L16:C13}); aliases may={route_error~value} must={}
        # L22 pyhard[read split_at_handler.value@16] binding=definitely_bound
        # L22 pyhard[type return] assert/assume conforms(result, int | str); observed={int}
        # L22 pyhard[dispatch value.marker()] assert/assume key in {Early}
        # L22 pyhard[row {Early}] invoke_method; owner=Early; label=Early.marker; result={int}
        return value.marker()
    else:
        # L24 pyhard[flow split_at_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Late}; defs={assignment:L20:C9}; points-to={alloc:L20:C17})
        # L24 pyhard[flow split_at_handler out:return] $result -> (binding=definitely_bound; tags={str}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), value -> (binding=definitely_bound; tags={Late}; defs={assignment:L20:C9}; points-to={alloc:L20:C17})
        # L24 pyhard[read split_at_handler.value@16] binding=definitely_bound
        # L24 pyhard[type return] assert/assume conforms(result, int | str); observed={str}
        # L24 pyhard[dispatch value.marker()] assert/assume key in {Late}
        # L24 pyhard[row {Late}] invoke_method; owner=Late; label=Late.marker; result={str}
        return value.marker()


# L27 pyhard[summary join_after_handler] returns={int, str}; escapes={}
# L27 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 19 closed tags
def join_after_handler(flag: bool) -> int | str:
    # L28 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_unbound; tags={}; defs={unbound:value})
    # L28 pyhard[flow join_after_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
    value = Early()
    # L29 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
    # L29 pyhard[flow join_after_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L33:C5, unbound:route_error}), selected -> (binding=definitely_bound; tags={Early, Late}; defs={assignment:L34:C9, assignment:L36:C9}; points-to={alloc:L28:C13, alloc:L32:C17}), value -> (binding=definitely_bound; tags={Early, Late}; defs={assignment:L28:C5, assignment:L32:C9}; points-to={alloc:L28:C13, alloc:L32:C17}); aliases may={selected~value} must={selected~value}
    try:
        # L30 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
        # L30 pyhard[flow join_after_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
        # L30 pyhard[flow join_after_handler out:raise:RouteError] $exception -> (binding=definitely_bound; tags={RouteError}; defs={raise:RouteError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
        # L30 pyhard[read join_after_handler.flag@12] binding=definitely_bound
        # L30 pyhard[dispatch flag] assert/assume key in {bool}
        # L30 pyhard[row {bool}] exact_builtin_truth; result={bool}
        if flag:
            # L31 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
            # L31 pyhard[flow join_after_handler out:raise:RouteError] $exception -> (binding=definitely_bound; tags={RouteError}; defs={raise:RouteError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
            raise RouteError()
        # L32 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13})
        # L32 pyhard[flow join_after_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Late}; defs={assignment:L32:C9}; points-to={alloc:L32:C17})
        value = Late()
    except RouteError as route_error:
        # L34 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_bound; tags={RouteError}; defs={handler:L33:C5}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13}); aliases may={route_error~value} must={}
        # L34 pyhard[flow join_after_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_bound; tags={RouteError}; defs={handler:L33:C5}; points-to={alloc:L16:C13, alloc:L19:C19, alloc:L20:C17, alloc:L28:C13, alloc:L31:C19, alloc:L32:C17, boundary:Early.marker, boundary:Late.marker, boundary:external, boundary:join_after_handler, boundary:split_at_handler}), selected -> (binding=definitely_bound; tags={Early}; defs={assignment:L34:C9}; points-to={alloc:L28:C13}), value -> (binding=definitely_bound; tags={Early}; defs={assignment:L28:C5}; points-to={alloc:L28:C13}); aliases may={route_error~selected, route_error~value, selected~value} must={selected~value}
        # L34 pyhard[read join_after_handler.value@20] binding=definitely_bound
        selected = value
    else:
        # L36 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_unbound; tags={}; defs={unbound:selected}), value -> (binding=definitely_bound; tags={Late}; defs={assignment:L32:C9}; points-to={alloc:L32:C17})
        # L36 pyhard[flow join_after_handler out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={unbound:route_error}), selected -> (binding=definitely_bound; tags={Late}; defs={assignment:L36:C9}; points-to={alloc:L32:C17}), value -> (binding=definitely_bound; tags={Late}; defs={assignment:L32:C9}; points-to={alloc:L32:C17}); aliases may={selected~value} must={selected~value}
        # L36 pyhard[read join_after_handler.value@20] binding=definitely_bound
        selected = value
    # L37 pyhard[flow join_after_handler in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L33:C5, unbound:route_error}), selected -> (binding=definitely_bound; tags={Early, Late}; defs={assignment:L34:C9, assignment:L36:C9}; points-to={alloc:L28:C13, alloc:L32:C17}), value -> (binding=definitely_bound; tags={Early, Late}; defs={assignment:L28:C5, assignment:L32:C9}; points-to={alloc:L28:C13, alloc:L32:C17}); aliases may={selected~value} must={selected~value}
    # L37 pyhard[flow join_after_handler out:return] $result -> (binding=definitely_bound; tags={int, str}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), route_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L33:C5, unbound:route_error}), selected -> (binding=definitely_bound; tags={Early, Late}; defs={assignment:L34:C9, assignment:L36:C9}; points-to={alloc:L28:C13, alloc:L32:C17}), value -> (binding=definitely_bound; tags={Early, Late}; defs={assignment:L28:C5, assignment:L32:C9}; points-to={alloc:L28:C13, alloc:L32:C17}); aliases may={selected~value} must={selected~value}
    # L37 pyhard[read join_after_handler.selected@12] binding=definitely_bound
    # L37 pyhard[type return] assert/assume conforms(result, int | str); observed={int, str}
    # L37 pyhard[dispatch selected.marker()] assert/assume key in {Early, Late}
    # L37 pyhard[row {Early}] invoke_method; owner=Early; label=Early.marker; result={int}
    # L37 pyhard[row {Late}] invoke_method; owner=Late; label=Late.marker; result={str}
    return selected.marker()
