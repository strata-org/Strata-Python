# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
# L1 pyhard[summary ordered] returns={bool}; escapes={}
# L1 pyhard[type parameter] assert/assume conforms(first, int); boundary nondet over 16 closed tags
# L1 pyhard[type parameter] assert/assume conforms(second, int); boundary nondet over 16 closed tags
# L1 pyhard[type parameter] assert/assume conforms(third, int); boundary nondet over 16 closed tags
def ordered(first: int, second: int, third: int) -> bool:
    # L2 pyhard[flow ordered in] first -> (binding=definitely_bound; tags={bool, int}; defs={param:first}), second -> (binding=definitely_bound; tags={bool, int}; defs={param:second}), third -> (binding=definitely_bound; tags={bool, int}; defs={param:third})
    # L2 pyhard[flow ordered out:return] $result -> (binding=definitely_bound; tags={bool}; defs={return}), first -> (binding=definitely_bound; tags={bool, int}; defs={param:first}), second -> (binding=definitely_bound; tags={bool, int}; defs={param:second}), third -> (binding=definitely_bound; tags={bool, int}; defs={param:third})
    # L2 pyhard[read ordered.first@12] binding=definitely_bound
    # L2 pyhard[read ordered.second@20] binding=definitely_bound
    # L2 pyhard[read ordered.third@29] binding=definitely_bound
    # L2 pyhard[type return] assert/assume conforms(result, bool); observed={bool}
    # L2 pyhard[dispatch first < second < third] assert/assume key in {(bool, bool), (bool, int), (int, bool), (int, int)}
    # L2 pyhard[row {(bool, bool), (bool, int), (int, bool), (int, int)}] binary_protocol; result={bool}; terminal=certified_builtin_total
    return first < second < third


# L5 pyhard[summary cross_type_equal] returns={bool}; escapes={}
# L5 pyhard[type parameter] assert/assume conforms(number, int); boundary nondet over 16 closed tags
# L5 pyhard[type parameter] assert/assume conforms(text, str); boundary nondet over 16 closed tags
def cross_type_equal(number: int, text: str) -> bool:
    # L6 pyhard[flow cross_type_equal in] number -> (binding=definitely_bound; tags={bool, int}; defs={param:number}), text -> (binding=definitely_bound; tags={str}; defs={param:text})
    # L6 pyhard[flow cross_type_equal out:return] $result -> (binding=definitely_bound; tags={bool}; defs={return}), number -> (binding=definitely_bound; tags={bool, int}; defs={param:number}), text -> (binding=definitely_bound; tags={str}; defs={param:text})
    # L6 pyhard[read cross_type_equal.number@12] binding=definitely_bound
    # L6 pyhard[read cross_type_equal.text@22] binding=definitely_bound
    # L6 pyhard[type return] assert/assume conforms(result, bool); observed={bool}
    # L6 pyhard[dispatch number == text] assert/assume key in {(bool, str), (int, str)}
    # L6 pyhard[row {(bool, str), (int, str)}] binary_protocol; plan=[left.__eq__:builtins.int.__eq__ -> right.__eq__:builtins.str.__eq__]; result={bool}; terminal=identity_comparison
    return number == text
