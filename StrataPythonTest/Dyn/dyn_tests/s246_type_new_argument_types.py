# Test: type.__new__ with a name that is not a str names the argument's type
type.__new__(type, 1, (), {})
