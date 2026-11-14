from typing import List
first = List[int]
names = [type('C%d' % i, (), {'__module__': '__main__'}) for i in range(129)]
for c in names:
    List[c]
print("129:", List[int] == first, List[int] is first)
first = List[str]
names = [type('D%d' % i, (), {'__module__': '__main__'}) for i in range(126)]
for c in names:
    List[c]
print("126:", List[str] is first)
