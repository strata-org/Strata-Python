# Test: an uncaught ImportError prints its msg
e = ImportError("a")
e.msg = "zzz"
raise e
