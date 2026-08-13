def test_unary_plus():
    a: int = 5
    b: int = +a
    assert b == 5, "unary plus on int"
    assert +(-3) == -3, "unary plus preserves sign"
    assert +0 == 0, "unary plus on zero"
    assert + +a == 5, "double unary plus"
    # Python's unary plus applies numeric coercion, so +True is the int 1
    flag: bool = True
    assert +flag == 1, "unary plus on bool yields 1"

test_unary_plus()
