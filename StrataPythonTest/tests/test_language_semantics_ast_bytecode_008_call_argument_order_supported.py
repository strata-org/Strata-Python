# Program relying on L→R argument evaluation
state = {"n": 0}
def next_id():
    state["n"] += 1
    return state["n"]
def record(a, b, c): return (a, b, c)
result = record(next_id(), next_id(), next_id())
assert result == (1, 2, 3)  # guaranteed L→R
print("OK: call argument order — deterministic L→R")
