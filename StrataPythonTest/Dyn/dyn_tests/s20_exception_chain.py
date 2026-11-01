# Test: the trace of an exception with a cause
raise ValueError("outer") from KeyError("inner")
