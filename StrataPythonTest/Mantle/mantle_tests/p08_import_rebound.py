# A module name rebound by assignment is an ordinary module global.
import os

os = None


def f():
    return os
