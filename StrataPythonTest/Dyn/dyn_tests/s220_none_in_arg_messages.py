# Test: the converters' TypeError names None as None, not NoneType
try:
    ExceptionGroup(None, [ValueError()])
except TypeError as e:
    msg = e.args[0]
try:
    type(None, (), {})
except TypeError as e:
    msg1 = e.args[0]
try:
    type("A", None, {})
except TypeError as e:
    msg2 = e.args[0]
try:
    type("A", (), None)
except TypeError as e:
    msg3 = e.args[0]
