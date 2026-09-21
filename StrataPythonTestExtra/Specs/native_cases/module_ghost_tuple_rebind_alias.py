# A tuple assignment rebinding a type alias invalidates it for later ghost types.
MyInt = int
MyInt, other = str, str
ghost(name="g", type=MyInt, init=0)
