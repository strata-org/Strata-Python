# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class Forward:
    # L2 pyhard[summary Forward.__add__] returns={NotImplementedType}; escapes={}
    def __add__(self, other):
        # L3 pyhard[flow Forward.__add__ in] other -> (binding=definitely_bound; tags={Forward, NoneType, NotImplementedType, Reflected, bool, bytes, dict, float, frozenset, int, list, object, range, set, slice, str, tuple, type}; defs={param:other}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}), self -> (binding=definitely_bound; tags={Forward}; defs={param:self}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}); aliases may={other~self} must={}
        # L3 pyhard[flow Forward.__add__ out:return] $result -> (binding=definitely_bound; tags={NotImplementedType}; defs={return}), other -> (binding=definitely_bound; tags={Forward, NoneType, NotImplementedType, Reflected, bool, bytes, dict, float, frozenset, int, list, object, range, set, slice, str, tuple, type}; defs={param:other}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}), self -> (binding=definitely_bound; tags={Forward}; defs={param:self}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}); aliases may={other~self} must={}
        return NotImplemented


class Reflected(Forward):
    # L7 pyhard[summary Reflected.__radd__] returns={int}; escapes={}
    def __radd__(self, other) -> int:
        # L8 pyhard[flow Reflected.__radd__ in] other -> (binding=definitely_bound; tags={Forward, NoneType, NotImplementedType, Reflected, bool, bytes, dict, float, frozenset, int, list, object, range, set, slice, str, tuple, type}; defs={param:other}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}), self -> (binding=definitely_bound; tags={Reflected}; defs={param:self}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}); aliases may={other~self} must={}
        # L8 pyhard[flow Reflected.__radd__ out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), other -> (binding=definitely_bound; tags={Forward, NoneType, NotImplementedType, Reflected, bool, bytes, dict, float, frozenset, int, list, object, range, set, slice, str, tuple, type}; defs={param:other}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}), self -> (binding=definitely_bound; tags={Reflected}; defs={param:self}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}); aliases may={other~self} must={}
        # L8 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 7


# L11 pyhard[summary custom] returns={int}; escapes={TypeError}
# L11 pyhard[type parameter] assert/assume conforms(left, Forward); boundary nondet over 18 closed tags
# L11 pyhard[type parameter] assert/assume conforms(right, Reflected); boundary nondet over 18 closed tags
def custom(left: Forward, right: Reflected) -> int:
    # L12 pyhard[flow custom in] left -> (binding=definitely_bound; tags={Forward, Reflected}; defs={param:left}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}), right -> (binding=definitely_bound; tags={Reflected}; defs={param:right}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}); aliases may={left~right} must={}
    # L12 pyhard[flow custom out:raise:TypeError] $exception -> (binding=definitely_bound; tags={TypeError}; defs={raise:TypeError}), left -> (binding=definitely_bound; tags={Forward, Reflected}; defs={param:left}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}), right -> (binding=definitely_bound; tags={Reflected}; defs={param:right}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}); aliases may={left~right} must={}
    # L12 pyhard[flow custom out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), left -> (binding=definitely_bound; tags={Forward, Reflected}; defs={param:left}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}), right -> (binding=definitely_bound; tags={Reflected}; defs={param:right}; points-to={boundary:Forward.__add__, boundary:Reflected.__radd__, boundary:correlated_builtin, boundary:custom, boundary:external}); aliases may={left~right} must={}
    # L12 pyhard[read custom.left@12] binding=definitely_bound
    # L12 pyhard[read custom.right@19] binding=definitely_bound
    # L12 pyhard[type return] assert/assume conforms(result, int); observed={int}; evaluation may raise={TypeError}
    # L12 pyhard[dispatch left + right] assert/assume key in {(Forward, Reflected), (Reflected, Reflected)}
    # L12 pyhard[row {(Forward, Reflected)}] binary_protocol; plan=[right.__radd__:Reflected.__radd__]; result={int}; terminal=candidate_contract_total; specialized-by=candidate return contracts
    # L12 pyhard[row {(Reflected, Reflected)}] binary_protocol; plan=[left.__add__:Forward.__add__]; raises={TypeError}; terminal=not_implemented_then_type_error; specialized-by=candidate return contracts
    return left + right


# L15 pyhard[summary correlated_builtin] returns={int, str}; escapes={TypeError}
# L15 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 18 closed tags
def correlated_builtin(flag: bool) -> int | str:
    # L16 pyhard[flow correlated_builtin in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_unbound; tags={}; defs={unbound:left}), right -> (binding=definitely_unbound; tags={}; defs={unbound:right})
    # L16 pyhard[flow correlated_builtin out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={int, str}; defs={assignment:L17:C9, assignment:L20:C9}), right -> (binding=definitely_bound; tags={int, str}; defs={assignment:L18:C9, assignment:L21:C9})
    # L16 pyhard[read correlated_builtin.flag@8] binding=definitely_bound
    # L16 pyhard[dispatch flag] assert/assume key in {bool}
    # L16 pyhard[row {bool}] exact_builtin_truth; result={bool}
    if flag:
        # L17 pyhard[flow correlated_builtin in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_unbound; tags={}; defs={unbound:left}), right -> (binding=definitely_unbound; tags={}; defs={unbound:right})
        # L17 pyhard[flow correlated_builtin out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={int}; defs={assignment:L17:C9}), right -> (binding=definitely_unbound; tags={}; defs={unbound:right})
        left = 1
        # L18 pyhard[flow correlated_builtin in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={int}; defs={assignment:L17:C9}), right -> (binding=definitely_unbound; tags={}; defs={unbound:right})
        # L18 pyhard[flow correlated_builtin out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={int}; defs={assignment:L17:C9}), right -> (binding=definitely_bound; tags={int}; defs={assignment:L18:C9})
        right = 2
    else:
        # L20 pyhard[flow correlated_builtin in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_unbound; tags={}; defs={unbound:left}), right -> (binding=definitely_unbound; tags={}; defs={unbound:right})
        # L20 pyhard[flow correlated_builtin out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={str}; defs={assignment:L20:C9}), right -> (binding=definitely_unbound; tags={}; defs={unbound:right})
        left = "a"
        # L21 pyhard[flow correlated_builtin in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={str}; defs={assignment:L20:C9}), right -> (binding=definitely_unbound; tags={}; defs={unbound:right})
        # L21 pyhard[flow correlated_builtin out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={str}; defs={assignment:L20:C9}), right -> (binding=definitely_bound; tags={str}; defs={assignment:L21:C9})
        right = "b"
    # L22 pyhard[flow correlated_builtin in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={int, str}; defs={assignment:L17:C9, assignment:L20:C9}), right -> (binding=definitely_bound; tags={int, str}; defs={assignment:L18:C9, assignment:L21:C9})
    # L22 pyhard[flow correlated_builtin out:raise:TypeError] $exception -> (binding=definitely_bound; tags={TypeError}; defs={raise:TypeError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={int, str}; defs={assignment:L17:C9, assignment:L20:C9}), right -> (binding=definitely_bound; tags={int, str}; defs={assignment:L18:C9, assignment:L21:C9})
    # L22 pyhard[flow correlated_builtin out:return] $result -> (binding=definitely_bound; tags={int, str}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), left -> (binding=definitely_bound; tags={int, str}; defs={assignment:L17:C9, assignment:L20:C9}), right -> (binding=definitely_bound; tags={int, str}; defs={assignment:L18:C9, assignment:L21:C9})
    # L22 pyhard[read correlated_builtin.left@12] binding=definitely_bound
    # L22 pyhard[read correlated_builtin.right@19] binding=definitely_bound
    # L22 pyhard[type return] assert/assume conforms(result, int | str); observed={int, str}; evaluation may raise={TypeError}
    # L22 pyhard[dispatch left + right] assert/assume key in {(int, int), (int, str), (str, int), (str, str)}
    # L22 pyhard[row {(int, int)}] binary_protocol; result={int}; terminal=certified_builtin_total
    # L22 pyhard[row {(int, str), (str, int)}] binary_protocol; raises={TypeError}; terminal=raise_type_error; specialized-by=candidate return contracts
    # L22 pyhard[row {(str, str)}] binary_protocol; result={str}; terminal=certified_builtin_total
    return left + right
