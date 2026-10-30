class Base:
    pass

class Outer(Base):
    class In(Outer):
        pass
