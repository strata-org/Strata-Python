# Method call on function return value — pure methods on temporaries work;
# mutating methods lose changes
"""
Calling a method on a function's return value: `get_obj().method()`.
The returned ClassInstance is a temporary — the method is called on it,
and under value semantics, any mutations inside the method are lost
(no variable holds the modified value).

This is fine for PURE methods (that return a value without modifying
self). But for methods that modify self and return None, the mutation
is completely lost — there's no variable to rebind.
"""
from dataclasses import dataclass


@dataclass
class Builder:
    parts: list[str]

    def add(self: "Builder", part: str) -> "Builder":
        self.parts = self.parts + [part]
        return self

    def build(self: "Builder") -> str:
        result: str = ""
        for p in self.parts:
            result = result + p
        return result


def create_builder() -> Builder:
    return Builder(parts=[])


def get_length_of_built() -> int:
    # Method on return value: create_builder().add("x").build()
    # Under value semantics with self-threading, this works IF
    # each .add() returns the modified self and the chain threads it
    b: Builder = create_builder()
    b = b.add("hello")
    b = b.add(" ")
    b = b.add("world")
    return len(b.build())


@dataclass
class Config:
    host: str
    port: int

    def get_url(self: "Config") -> str:
        return self.host + ":" + str(self.port)


def make_config() -> Config:
    return Config(host="localhost", port=8080)


def main() -> None:
    # Pure method on return value: works
    url: str = make_config().get_url()
    assert url == "localhost:8080"

    # Builder pattern with explicit reassignment
    assert get_length_of_built() == 11  # "hello world"

    # Direct method on fresh construction
    greeting: str = Builder(parts=["hi", " ", "there"]).build()
    assert greeting == "hi there"

    print(url, get_length_of_built(), greeting)


main()
