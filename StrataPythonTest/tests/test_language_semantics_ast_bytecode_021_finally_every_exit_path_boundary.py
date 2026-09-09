# NAIVE MODEL WOULD GET WRONG: skips finally on break
trace = []
for i in range(5):
    try:
        if i == 2: break
        trace.append(f"body{i}")
    finally:
        trace.append(f"fin{i}")
# Naive (finally skipped on break): no fin2. CPython: fin2 present
assert "fin2" in trace
print("BOUNDARY: naive model skips finally on break; CPython always runs it")
