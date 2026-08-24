for never_bound in range(0):
    pass

assert never_bound is None, "unsound: Python raises NameError"
