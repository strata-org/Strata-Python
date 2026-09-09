# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary combine] returns={tuple}; escapes={OverflowError}
def combine(
    # L2 pyhard[type parameter] assert/assume conforms(left, int); boundary nondet over 16 closed tags
    left: int,
    # L3 pyhard[type parameter] assert/assume conforms(right, int); boundary nondet over 16 closed tags
    right: int,
    # L4 pyhard[type parameter] assert/assume conforms(scale, float); boundary nondet over 16 closed tags
    scale: float,
    # L5 pyhard[type parameter] assert/assume conforms(prefix, str); boundary nondet over 16 closed tags
    prefix: str,
    # L6 pyhard[type parameter] assert/assume conforms(suffix, str); boundary nondet over 16 closed tags
    suffix: str,
) -> tuple[int, float, str]:
    # L8 pyhard[flow combine in] left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_unbound; tags={}; defs={unbound:mixed}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_unbound; tags={}; defs={unbound:text}), whole -> (binding=definitely_unbound; tags={}; defs={unbound:whole})
    # L8 pyhard[flow combine out] left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_unbound; tags={}; defs={unbound:mixed}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_unbound; tags={}; defs={unbound:text}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L8 pyhard[read combine.left@13] binding=definitely_bound
    # L8 pyhard[read combine.right@20] binding=definitely_bound
    # L8 pyhard[dispatch left + right] assert/assume key in {(bool, bool), (bool, int), (int, bool), (int, int)}
    # L8 pyhard[row {(bool, bool), (bool, int), (int, bool), (int, int)}] binary_protocol; result={int}; terminal=certified_builtin_total
    whole = left + right
    # L9 pyhard[flow combine in] left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_unbound; tags={}; defs={unbound:mixed}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_unbound; tags={}; defs={unbound:text}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L9 pyhard[flow combine out] left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_bound; tags={float, int}; defs={assignment:L9:C5}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_unbound; tags={}; defs={unbound:text}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L9 pyhard[flow combine out:raise:OverflowError] $exception -> (binding=definitely_bound; tags={OverflowError}; defs={raise:OverflowError}), left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_unbound; tags={}; defs={unbound:mixed}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_unbound; tags={}; defs={unbound:text}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L9 pyhard[read combine.whole@13] binding=definitely_bound
    # L9 pyhard[read combine.scale@21] binding=definitely_bound
    # L9 pyhard[dispatch whole * scale] assert/assume key in {(int, bool), (int, float), (int, int)}
    # L9 pyhard[row {(int, bool), (int, int)}] binary_protocol; result={int}; terminal=certified_builtin_total
    # L9 pyhard[row {(int, float)}] binary_protocol; result={float}; raises={OverflowError}; terminal=certified_builtin_partial
    mixed = whole * scale
    # L10 pyhard[flow combine in] left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_bound; tags={float, int}; defs={assignment:L9:C5}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_unbound; tags={}; defs={unbound:text}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L10 pyhard[flow combine out] left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_bound; tags={float, int}; defs={assignment:L9:C5}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_bound; tags={str}; defs={assignment:L10:C5}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L10 pyhard[read combine.prefix@12] binding=definitely_bound
    # L10 pyhard[read combine.suffix@21] binding=definitely_bound
    # L10 pyhard[dispatch prefix + suffix] assert/assume key in {(str, str)}
    # L10 pyhard[row {(str, str)}] binary_protocol; result={str}; terminal=certified_builtin_total
    text = prefix + suffix
    # L11 pyhard[flow combine in] left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_bound; tags={float, int}; defs={assignment:L9:C5}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_bound; tags={str}; defs={assignment:L10:C5}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L11 pyhard[flow combine out:return] $result -> (binding=definitely_bound; tags={tuple}; defs={return}), left -> (binding=definitely_bound; tags={bool, int}; defs={param:left}), mixed -> (binding=definitely_bound; tags={float, int}; defs={assignment:L9:C5}), prefix -> (binding=definitely_bound; tags={str}; defs={param:prefix}), right -> (binding=definitely_bound; tags={bool, int}; defs={param:right}), scale -> (binding=definitely_bound; tags={bool, float, int}; defs={param:scale}), suffix -> (binding=definitely_bound; tags={str}; defs={param:suffix}), text -> (binding=definitely_bound; tags={str}; defs={assignment:L10:C5}), whole -> (binding=definitely_bound; tags={int}; defs={assignment:L8:C5})
    # L11 pyhard[read combine.whole@12] binding=definitely_bound
    # L11 pyhard[read combine.mixed@19] binding=definitely_bound
    # L11 pyhard[read combine.text@26] binding=definitely_bound
    # L11 pyhard[type return] assert/assume conforms(result, tuple[int, float, str]); observed={tuple}
    return whole, mixed, text
