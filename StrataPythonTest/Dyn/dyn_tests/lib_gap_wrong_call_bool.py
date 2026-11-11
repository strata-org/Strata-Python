# A bound method object names the class of self in its message, an immediate call the defining
# type: the model can't tell them apart, so a wrong call on a bool stops with a gap.
try:
    (True).__trunc__(1)
except TypeError as e:
    print(e.args[0])
