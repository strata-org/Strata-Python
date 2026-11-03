# Test: a write of a unicode error's start, a C integer in CPython
e = ValueError.__new__(UnicodeEncodeError)
e.start = "x"
