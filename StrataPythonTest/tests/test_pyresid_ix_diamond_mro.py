# Interaction: diamond inheritance: C3 puts Left before Right, so
# ping resolves to Left.ping for Bottom; isinstance against the shared
# Base admits the whole closure.
class Base:
    def ping(self) -> str:
        return "base"


class Left(Base):
    def ping(self) -> str:
        return "left"


class Right(Base):
    pass


class Bottom(Left, Right):
    pass


def which(o) -> str:
    if isinstance(o, Base):
        return o.ping()
    return "none"


r1 = which(Bottom())
r2 = which(Right())
