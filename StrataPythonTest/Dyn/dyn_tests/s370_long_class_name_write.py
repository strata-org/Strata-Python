# An attribute write to an instance of a class whose name is long: the write needs no message.
class AVeryLongClassNameThatIsMuchLongerThanFiftyBytesInTotalLength:
    pass
o = AVeryLongClassNameThatIsMuchLongerThanFiftyBytesInTotalLength()
o.x = 1
print(o.x)
