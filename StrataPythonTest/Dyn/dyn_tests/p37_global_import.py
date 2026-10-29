# A function that declares a name `global` and imports it binds the module global.
def f():
    global json
    import json
    return json
