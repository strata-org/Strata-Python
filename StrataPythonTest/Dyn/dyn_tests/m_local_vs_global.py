# A local and a module global with the same name.
x = 1

def reads_global():
    return x

def shadows_global():
    x = 2
    return x
