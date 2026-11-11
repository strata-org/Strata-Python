# A list argument's items are read when each is written, so a repr that changes the list is seen.
class A:
    def __repr__(self):
        lst[1] = str
        return "A"
lst = [A(), int]
print(dict[lst, str])
# A repr that shrinks the list makes CPython read past its end.
class S:
    def __repr__(self):
        del lst2[1]
        return "S"
lst2 = [S(), int]
print(dict[lst2, str])
