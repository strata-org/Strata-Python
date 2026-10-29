# A bare `except:` must be the last clause; CPython reports only the first one that is not.
try:
    pass
except:
    pass
except:
    pass
except KeyError:
    pass
