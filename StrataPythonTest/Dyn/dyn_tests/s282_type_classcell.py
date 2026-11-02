# Test: type() with a __classcell__ in the namespace
X = type("X", (), {"__classcell__": 1})
