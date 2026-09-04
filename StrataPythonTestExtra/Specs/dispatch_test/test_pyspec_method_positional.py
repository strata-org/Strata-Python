from servicelib.Messaging import Messaging


def check_receive(m: Messaging) -> None:
    m.receive("t")
