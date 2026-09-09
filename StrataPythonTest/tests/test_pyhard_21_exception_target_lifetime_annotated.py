# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class CapturedError(Exception):
    pass


class ReplacementError(Exception):
    pass


# L9 pyhard[summary return_target] returns={CapturedError}; escapes={}
def return_target() -> CapturedError:
    # L10 pyhard[flow return_target in] caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught})
    # L10 pyhard[flow return_target out:return] $result -> (binding=definitely_bound; tags={CapturedError}; defs={return}), caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L12:C5})
    try:
        # L11 pyhard[flow return_target in] caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught})
        # L11 pyhard[flow return_target out:raise:CapturedError] $exception -> (binding=definitely_bound; tags={CapturedError}; defs={raise:CapturedError}), caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught})
        raise CapturedError("returned")
    except CapturedError as caught:
        # L13 pyhard[flow return_target in] caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L12:C5}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
        # L13 pyhard[flow return_target out:return] $result -> (binding=definitely_bound; tags={CapturedError}; defs={return}), caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L12:C5}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
        # L13 pyhard[read return_target.caught@16] binding=definitely_bound
        # L13 pyhard[type return] assert/assume conforms(result, CapturedError); observed={CapturedError}
        return caught


# L16 pyhard[summary save_then_fallthrough] returns={CapturedError}; escapes={}
def save_then_fallthrough() -> CapturedError:
    # L17 pyhard[flow save_then_fallthrough in] caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
    # L17 pyhard[flow save_then_fallthrough out] caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L19:C5}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L20:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
    try:
        # L18 pyhard[flow save_then_fallthrough in] caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
        # L18 pyhard[flow save_then_fallthrough out:raise:CapturedError] $exception -> (binding=definitely_bound; tags={CapturedError}; defs={raise:CapturedError}), caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
        raise CapturedError("saved")
    except CapturedError as caught:
        # L20 pyhard[flow save_then_fallthrough in] caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L19:C5}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
        # L20 pyhard[flow save_then_fallthrough out] caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L19:C5}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L20:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}); aliases may={caught~saved} must={caught~saved}
        # L20 pyhard[read save_then_fallthrough.caught@17] binding=definitely_bound
        saved = caught
    # L21 pyhard[flow save_then_fallthrough in] caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L19:C5}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L20:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
    # L21 pyhard[flow save_then_fallthrough out:return] $result -> (binding=definitely_bound; tags={CapturedError}; defs={return}), caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L19:C5}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L20:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
    # L21 pyhard[read save_then_fallthrough.saved@12] binding=definitely_bound
    # L21 pyhard[type return] assert/assume conforms(result, CapturedError); observed={CapturedError}
    return saved


# L24 pyhard[summary save_then_replacement] returns={CapturedError}; escapes={}
def save_then_replacement() -> CapturedError:
    # L25 pyhard[flow save_then_replacement in] caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
    # L25 pyhard[flow save_then_replacement out] caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L28:C9}), replacement -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L31:C5}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
    try:
        # L26 pyhard[flow save_then_replacement in] caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
        # L26 pyhard[flow save_then_replacement out:raise:ReplacementError] $exception -> (binding=definitely_bound; tags={ReplacementError}; defs={raise:ReplacementError}), caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L28:C9}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
        try:
            # L27 pyhard[flow save_then_replacement in] caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
            # L27 pyhard[flow save_then_replacement out:raise:CapturedError] $exception -> (binding=definitely_bound; tags={CapturedError}; defs={raise:CapturedError}), caught -> (binding=definitely_unbound; tags={}; defs={unbound:caught}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
            raise CapturedError("survives replacement")
        except CapturedError as caught:
            # L29 pyhard[flow save_then_replacement in] caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L28:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_unbound; tags={}; defs={unbound:saved})
            # L29 pyhard[flow save_then_replacement out] caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L28:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}); aliases may={caught~saved} must={caught~saved}
            # L29 pyhard[read save_then_replacement.caught@21] binding=definitely_bound
            saved = caught
            # L30 pyhard[flow save_then_replacement in] caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L28:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}); aliases may={caught~saved} must={caught~saved}
            # L30 pyhard[flow save_then_replacement out:raise:ReplacementError] $exception -> (binding=definitely_bound; tags={ReplacementError}; defs={raise:ReplacementError}), caught -> (binding=definitely_bound; tags={CapturedError}; defs={handler:L28:C9}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), replacement -> (binding=definitely_unbound; tags={}; defs={unbound:replacement}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}); aliases may={caught~saved} must={caught~saved}
            raise ReplacementError("replacement")
    except ReplacementError as replacement:
        # L32 pyhard[flow save_then_replacement in] caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L28:C9}), replacement -> (binding=definitely_bound; tags={ReplacementError}; defs={handler:L31:C5}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}); aliases may={replacement~saved} must={}
        # L32 pyhard[flow save_then_replacement out] caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L28:C9}), replacement -> (binding=definitely_bound; tags={ReplacementError}; defs={handler:L31:C5}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement}); aliases may={replacement~saved} must={}
        pass
    # L33 pyhard[flow save_then_replacement in] caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L28:C9}), replacement -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L31:C5}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
    # L33 pyhard[flow save_then_replacement out:return] $result -> (binding=definitely_bound; tags={CapturedError}; defs={return}), caught -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L28:C9}), replacement -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L31:C5}), saved -> (binding=definitely_bound; tags={CapturedError}; defs={assignment:L29:C13}; points-to={alloc:L11:C15, alloc:L18:C15, alloc:L27:C19, alloc:L30:C19, boundary:external, boundary:return_target, boundary:save_then_fallthrough, boundary:save_then_replacement})
    # L33 pyhard[read save_then_replacement.saved@12] binding=maybe_bound; may raise UnboundLocalError
    # L33 pyhard[type return] assert/assume conforms(result, CapturedError); observed={CapturedError}
    return saved
