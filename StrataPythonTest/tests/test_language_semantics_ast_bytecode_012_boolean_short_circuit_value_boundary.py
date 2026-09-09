# NAIVE MODEL WOULD GET WRONG: assumes and/or return bool
config = {"debug": True}
# Naive: (config or {}) returns True. CPython: returns config itself
result = config or {}
assert result is config  # the dict, not True
assert type(result) is dict
print("BOUNDARY: naive model returns True; CPython returns the dict object")
