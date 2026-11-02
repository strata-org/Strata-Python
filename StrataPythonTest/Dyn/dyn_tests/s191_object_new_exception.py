# Test: object.__new__ of an exception class, whose static base has another tp_new
object.__new__(ValueError, 1)
