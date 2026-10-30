# A program that reads, assigns or deletes a function's __defaults__ is not admitted
# (docs/PythonToDyn.md, §5.4). CPython 3.12 reads __defaults__ at each call, so h() below
# returns [10]; the translated h keeps the default of its def, which its prologue reads from
# the default cell. This program pins that translation: the assignment is a py.setAttr.
def h(a=[]):
    return a

h.__defaults__ = ([10],)
print(h())
