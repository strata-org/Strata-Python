# Witness: Python floor-division and modulo SIGN on negative operands.
# CPython: // floors toward -inf; % takes the sign of the DIVISOR.
#   -7 // 2 == -4   (not -3)
#   -7 % 3  ==  2   (not -1)
# Strata:  uses SMT-LIB div/mod (truncates toward zero; mod sign = dividend)
#          -> computes -3 and -1 -> WRONG VALUE (laurel 273, 266/291/433,
#          267/292/434). This is active unsoundness (wrong number, not a Hole).
def fdiv(a: int, b: int) -> int:
    return a // b

def fmod(a: int, b: int) -> int:
    return a % b

assert fdiv(-7, 2) == -4
assert fmod(-7, 3) == 2
