state: int = 0


class Base:
    pass


class Child(Base):
    def run(self):
        def update():
            global state
            state = 1

        update()
