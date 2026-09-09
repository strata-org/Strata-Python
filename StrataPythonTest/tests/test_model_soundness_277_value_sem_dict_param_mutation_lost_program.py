# Value sem: dict param mutation lost — `f(d); d["k"]=v` inside f invisible to
# caller; CPython has key, Model doesn't
"""
VALUE SEMANTICS WHERE CPYTHON HAS REFERENCE SEMANTICS:
Dict passed to function — function adds key, caller sees change in CPython.

CPython: dict param is a reference. d[k]=v mutates the SAME dict.
Model: dict param is a COPY. d[k]=v mutates the copy. Caller unchanged.

CPython result: config == {"host": "x", "port": 8080}
Model result:  config == {"host": "x"}
"""


def add_default_port(d: dict[str, str], port: str) -> None:
    d["port"] = port


def main() -> None:
    config: dict[str, str] = {"host": "localhost"}
    add_default_port(config, "8080")

    # CPython: config has "port" key — function mutated the SAME dict
    # Model:  config has NO "port" key — function mutated a COPY
    assert "port" in config  # True in CPython
    assert config["port"] == "8080"

    print(config)


main()
