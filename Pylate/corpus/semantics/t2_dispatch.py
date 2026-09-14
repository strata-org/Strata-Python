class Animal:
    def __init__(self, name):
        self.name = name

    def speak(self):
        return "..."


class Dog(Animal):
    def speak(self):
        return "woof"


class Cat(Animal):
    def speak(self):
        return "meow"


class Robot:
    def __init__(self):
        self.serial = 42


def noise(a):
    return a.speak()


zoo = [Dog("rex"), Cat("tom")]
for a in zoo:
    s = a.speak()
    if isinstance(a, Dog):
        t = a.speak()

flag = len(zoo) > 1
klass = Dog if flag else Cat
x = klass("spot")
u = x.speak()

r = Robot()
v = noise(r)
