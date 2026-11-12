# from dataclasses import of a name CPython lacks.
try:
    from dataclasses import nothing
except ImportError as e:
    print("ImportError")
