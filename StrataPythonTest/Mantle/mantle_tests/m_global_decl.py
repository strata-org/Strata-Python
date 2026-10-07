# `global x` makes a function's write go to the module.
def set_counter():
    global counter
    counter = 1

def get_counter():
    return counter
