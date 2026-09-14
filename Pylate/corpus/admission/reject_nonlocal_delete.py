class Box:
    def __init__(self):
        self.value = 1


box = Box()
del box.value

mapping = {"value": 1}
del mapping["value"]
