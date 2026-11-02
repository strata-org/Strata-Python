# Test: a global whose render holds a line break stops the trace with a gap, after the globals before it
a = 1
z = type("x\ny", (), {'__module__': '__main__'})
