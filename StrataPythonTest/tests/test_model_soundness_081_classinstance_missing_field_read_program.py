# ClassInstance missing field read — `DictStrAny_get` on absent key returns
# Hole; no constructor postconditions establish field presence
"""
Reading a field from a ClassInstance that doesn't have that field in its
DictStrAny should raise AttributeError. In the model, DictStrAny_get on
a missing key either returns Hole (unconstrained) or has a precondition
that the key exists. If neither, the model silently returns garbage for
non-existent attributes.

This matters when:
1. A field is conditionally initialized (only on some __init__ paths)
2. A subclass is accessed through a parent type that declares fewer fields
3. A typo in field name goes undetected
"""
from dataclasses import dataclass


@dataclass
class Config:
    host: str
    port: int
    timeout: int


def get_host(c: Config) -> str:
    return c.host


def get_timeout(c: Config) -> int:
    return c.timeout


class Server:
    def __init__(self: "Server", name: str, debug: bool) -> None:
        self.name = name
        if debug:
            self.log_level = "DEBUG"
        else:
            self.log_level = "INFO"
        # Note: self.log_level is always set (both branches)
        # But what if one branch didn't set it?


def get_name(s: Server) -> str:
    return s.name


def get_log_level(s: Server) -> str:
    return s.log_level


def main() -> None:
    # Dataclass: all fields guaranteed present
    cfg: Config = Config(host="localhost", port=8080, timeout=30)
    assert get_host(cfg) == "localhost"
    assert get_timeout(cfg) == 30

    # Regular class: fields set in __init__
    srv: Server = Server(name="web", debug=True)
    assert get_name(srv) == "web"
    assert get_log_level(srv) == "DEBUG"

    srv2: Server = Server(name="api", debug=False)
    assert get_log_level(srv2) == "INFO"

    # Access non-existent field raises AttributeError in CPython
    raised: bool = False
    try:
        x = getattr(cfg, "nonexistent")  # type: ignore
    except AttributeError:
        raised = True
    assert raised == True

    print(get_host(cfg), get_name(srv), get_log_level(srv2))


main()
