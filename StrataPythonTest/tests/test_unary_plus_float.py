# Unary plus on a float. Verification proves this; the interpreter cannot
# reduce unary operators on floats, so expected_interpret/ pins that failure.
# Kept separate from test_unary_plus.py so the int/bool cases stay interpretable.
def test_unary_plus_float():
    f: float = 3.5
    assert +f > 3.0, "unary plus on float"

test_unary_plus_float()
