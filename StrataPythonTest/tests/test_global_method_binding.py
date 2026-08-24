method_value: int = 0


class Setter:
    def set_value(self):
        global method_value
        method_value = 9


setter: Setter = Setter()
setter.set_value()
assert method_value == 9, "method global assignment"
