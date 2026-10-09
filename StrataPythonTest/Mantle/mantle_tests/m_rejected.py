# Constructs the translator rejects.
from . import sibling
from os import *

def outer():
    def inner():
        pass
    return inner

def bad_default(x=[]):
    return x
