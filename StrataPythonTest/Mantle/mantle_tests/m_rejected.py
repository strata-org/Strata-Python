# Constructs the translator rejects.
from . import sibling
from os import *

def outer():
    def inner():
        pass
    return inner

def bad_default(x=[]):
    return x

y = 1
for i in y:
    pass
