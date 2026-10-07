# Imports under `try` and `if` are recorded and bind module globals.
try:
    import simplejson as json
except ImportError:
    import json

if json:
    from os import path
else:
    path = None


def f(x):
    return json.dumps(x), path
