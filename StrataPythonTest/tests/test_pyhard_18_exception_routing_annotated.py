# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class LocalLookupError(KeyError):
    pass


# L5 pyhard[summary ordered_handlers] returns={int}; escapes={}
# L5 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 19 closed tags
def ordered_handlers(flag: bool) -> int:
    # L6 pyhard[flow ordered_handlers in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
    # L6 pyhard[flow ordered_handlers out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L10:C5, unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L12:C5, unbound:value_error})
    try:
        # L7 pyhard[flow ordered_handlers in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
        # L7 pyhard[flow ordered_handlers out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
        # L7 pyhard[flow ordered_handlers out:raise:LocalLookupError] $exception -> (binding=definitely_bound; tags={LocalLookupError}; defs={raise:LocalLookupError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
        # L7 pyhard[read ordered_handlers.flag@12] binding=definitely_bound
        # L7 pyhard[dispatch flag] assert/assume key in {bool}
        # L7 pyhard[row {bool}] exact_builtin_truth; result={bool}
        if flag:
            # L8 pyhard[flow ordered_handlers in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
            # L8 pyhard[flow ordered_handlers out:raise:LocalLookupError] $exception -> (binding=definitely_bound; tags={LocalLookupError}; defs={raise:LocalLookupError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
            raise LocalLookupError()
        # L9 pyhard[flow ordered_handlers in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
        # L9 pyhard[flow ordered_handlers out:raise:ValueError] $exception -> (binding=definitely_bound; tags={ValueError}; defs={raise:ValueError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
        raise ValueError()
    except LookupError as lookup_error:
        # L11 pyhard[flow ordered_handlers in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L10:C5}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
        # L11 pyhard[flow ordered_handlers out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L10:C5}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer}), value_error -> (binding=definitely_unbound; tags={}; defs={unbound:value_error})
        # L11 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 1
    except ValueError as value_error:
        # L13 pyhard[flow ordered_handlers in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_bound; tags={ValueError}; defs={handler:L12:C5})
        # L13 pyhard[flow ordered_handlers out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), value_error -> (binding=definitely_bound; tags={ValueError}; defs={handler:L12:C5})
        # L13 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 2


# L16 pyhard[summary unmatched_reaches_outer] returns={int}; escapes={}
def unmatched_reaches_outer() -> int:
    # L17 pyhard[flow unmatched_reaches_outer in] outer_error -> (binding=definitely_unbound; tags={}; defs={unbound:outer_error}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
    # L17 pyhard[flow unmatched_reaches_outer out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), outer_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L22:C5}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
    try:
        # L18 pyhard[flow unmatched_reaches_outer in] outer_error -> (binding=definitely_unbound; tags={}; defs={unbound:outer_error}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
        # L18 pyhard[flow unmatched_reaches_outer out:raise:LocalLookupError] $exception -> (binding=definitely_bound; tags={LocalLookupError}; defs={raise:LocalLookupError}), outer_error -> (binding=definitely_unbound; tags={}; defs={unbound:outer_error}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
        try:
            # L19 pyhard[flow unmatched_reaches_outer in] outer_error -> (binding=definitely_unbound; tags={}; defs={unbound:outer_error}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
            # L19 pyhard[flow unmatched_reaches_outer out:raise:LocalLookupError] $exception -> (binding=definitely_bound; tags={LocalLookupError}; defs={raise:LocalLookupError}), outer_error -> (binding=definitely_unbound; tags={}; defs={unbound:outer_error}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
            raise LocalLookupError()
        except ValueError as wrong_error:
            return 0
    except LookupError as outer_error:
        # L23 pyhard[flow unmatched_reaches_outer in] outer_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L22:C5}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
        # L23 pyhard[flow unmatched_reaches_outer out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), outer_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L22:C5}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer}), wrong_error -> (binding=definitely_unbound; tags={}; defs={unbound:wrong_error})
        # L23 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 3


# L26 pyhard[summary bare_reraise] returns={int}; escapes={}
def bare_reraise() -> int:
    # L27 pyhard[flow bare_reraise in] active_error -> (binding=definitely_unbound; tags={}; defs={unbound:active_error}), reraised_error -> (binding=definitely_unbound; tags={}; defs={unbound:reraised_error})
    # L27 pyhard[flow bare_reraise out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), active_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L30:C9}), reraised_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L32:C5})
    try:
        # L28 pyhard[flow bare_reraise in] active_error -> (binding=definitely_unbound; tags={}; defs={unbound:active_error}), reraised_error -> (binding=definitely_unbound; tags={}; defs={unbound:reraised_error})
        # L28 pyhard[flow bare_reraise out:raise:LocalLookupError] $exception -> (binding=definitely_bound; tags={LocalLookupError}; defs={raise:LocalLookupError}), active_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L30:C9}), reraised_error -> (binding=definitely_unbound; tags={}; defs={unbound:reraised_error})
        try:
            # L29 pyhard[flow bare_reraise in] active_error -> (binding=definitely_unbound; tags={}; defs={unbound:active_error}), reraised_error -> (binding=definitely_unbound; tags={}; defs={unbound:reraised_error})
            # L29 pyhard[flow bare_reraise out:raise:LocalLookupError] $exception -> (binding=definitely_bound; tags={LocalLookupError}; defs={raise:LocalLookupError}), active_error -> (binding=definitely_unbound; tags={}; defs={unbound:active_error}), reraised_error -> (binding=definitely_unbound; tags={}; defs={unbound:reraised_error})
            raise LocalLookupError()
        except LookupError as active_error:
            # L31 pyhard[flow bare_reraise in] active_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L30:C9}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer}), reraised_error -> (binding=definitely_unbound; tags={}; defs={unbound:reraised_error})
            # L31 pyhard[flow bare_reraise out:raise:LocalLookupError] $exception -> (binding=definitely_bound; tags={LocalLookupError}; defs={raise:LocalLookupError}), active_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L30:C9}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer}), reraised_error -> (binding=definitely_unbound; tags={}; defs={unbound:reraised_error})
            raise
    except LocalLookupError as reraised_error:
        # L33 pyhard[flow bare_reraise in] active_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L30:C9}), reraised_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L32:C5}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer})
        # L33 pyhard[flow bare_reraise out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), active_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L30:C9}), reraised_error -> (binding=definitely_bound; tags={LocalLookupError}; defs={handler:L32:C5}; points-to={alloc:L19:C19, alloc:L29:C19, alloc:L8:C19, boundary:bare_reraise, boundary:external, boundary:ordered_handlers, boundary:unmatched_reaches_outer})
        # L33 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 4
