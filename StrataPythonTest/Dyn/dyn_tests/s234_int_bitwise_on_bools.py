# Test: int's own &, | and ^ on two bools give ints, and bool's give bools
a = int.__and__(True, True)
b = int.__or__(False, True)
c = int.__xor__(True, False)
d = bool.__and__(True, True)
