# A rebind after the ghost does not change the binding the ghost resolved.
MyInt = int
ghost(name="counter", type=MyInt, init=0)
MyInt = 0
