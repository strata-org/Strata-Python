if False:
    dead_branch_value = 1

assert dead_branch_value is None, "unsound: Python raises NameError"
