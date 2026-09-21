# A walrus rebinding a type alias invalidates it for later ghost types.
MyInt = int
(MyInt := str)
ghost(name="g", type=MyInt, init=0)
