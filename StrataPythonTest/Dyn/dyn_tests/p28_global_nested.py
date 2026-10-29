# A name declared `global` in a function is global to the functions nested in it, even if
# an outer function binds it.  A `def` whose name is declared `global` has a top-level
# qualified name.
def outer():
    x = 1

    def mid():
        global x

        def inner():
            return x
        return inner

    def g():
        global helper

        def helper():
            return x
    return mid, g
