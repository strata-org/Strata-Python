class Base:
    pass


class Child(Base):
    def set_value(self):
        global inherited_value
        inherited_value = 1
