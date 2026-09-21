# A ghost's `type=` sees only bindings declared before it.
ghost(name="counter", type=MyInt, init=0)
MyInt = int
