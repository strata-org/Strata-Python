# Test: type() with a name that holds a null character raises ValueError
X = type("a\x00b", (), {"__module__": "m"})
