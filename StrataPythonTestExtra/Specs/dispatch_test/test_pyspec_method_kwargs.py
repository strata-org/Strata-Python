from servicelib.Messaging import Messaging


def check_send(m: Messaging) -> None:
    m.send(Topic="t", Body="b")
