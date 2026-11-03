# A subclass of zip made by type() stops with a gap.
print("before")
print(type(type("T", (zip,), {"__module__": "m"})([1])).__name__)
