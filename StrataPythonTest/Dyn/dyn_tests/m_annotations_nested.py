# Each class body has one annotated assignment inside a compound statement.
class TryBody:
    try:
        a: int = 1
    except KeyError:
        pass


class TryHandler:
    try:
        pass
    except KeyError:
        a: int = 1


class TryElse:
    try:
        pass
    except KeyError:
        pass
    else:
        a: int = 1


class TryFinally:
    try:
        pass
    finally:
        a: int = 1


class MatchCase:
    match 1:
        case 1:
            a: int = 1


class WithBody:
    with open("f") as fh:
        a: int = 1


class WhileElse:
    while False:
        pass
    else:
        a: int = 1


class ForElse:
    for i in ():
        pass
    else:
        a: int = 1


class IfElse:
    if False:
        pass
    else:
        a: int = 1


class InMethod:
    def m(self):
        a: int = 1


class TryStar:
    try:
        pass
    except* KeyError:
        a: int = 1
