# Test: a class that defines __eq__ but not __hash__ is unhashable, so a set display of it raises TypeError
class C:
    def __eq__(self, o):
        return True
{C()}
