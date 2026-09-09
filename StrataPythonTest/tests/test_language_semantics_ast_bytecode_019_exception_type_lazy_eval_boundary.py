# NAIVE MODEL WOULD GET WRONG: evaluates all exception types eagerly
trace = []
def Exc1(): trace.append("E1"); return ValueError
def Exc2(): trace.append("E2"); return TypeError
try:
    raise ValueError("x")
except Exc1():
    pass
except Exc2():
    pass
# Naive (eager): both Exc1() and Exc2() called. CPython: only Exc1() (first match)
assert trace == ["E1"]
print("BOUNDARY: naive model evaluates all handler types; CPython stops at first match")
