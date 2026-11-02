# Test: type() checks __slots__ before the null character of the name
X = type("a\x00b", (), {"__module__": "m", "__slots__": (1,)})
