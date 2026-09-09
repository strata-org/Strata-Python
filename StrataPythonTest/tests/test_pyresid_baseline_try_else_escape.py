def route_else_exception() -> str:
    try:
        try:
            pass
        except ValueError:
            return "wrong-inner-handler"
        else:
            raise ValueError()
    except ValueError:
        return "correct-outer-handler"


result = route_else_exception()
