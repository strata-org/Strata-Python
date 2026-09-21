# A ghost's `type=` may name a module-local alias of a builtin type.
MyInt = int
ghost(name="counter", type=MyInt, init=0)
