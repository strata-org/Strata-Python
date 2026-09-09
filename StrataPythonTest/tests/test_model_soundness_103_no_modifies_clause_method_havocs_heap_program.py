# No `modifies` clause on methods — after call, entire heap is havoc'd;
# unmodified fields become unprovable
"""
If user classes are modeled as Composite (heap semantics), every method
that modifies self needs a `modifies` clause declaring which fields it
changes. Without it, the verifier must assume the method could modify
ANYTHING on the heap (havoc), making all subsequent reads unprovable.

This program shows methods that modify specific fields — the verifier
needs to know which fields are modified to preserve knowledge about
unmodified fields.
"""
from dataclasses import dataclass


@dataclass
class Player:
    name: str
    health: int
    score: int

    def take_damage(self: "Player", amount: int) -> None:
        # Modifies: self.health only
        # Does NOT modify: self.name, self.score
        self.health = self.health - amount

    def add_score(self: "Player", points: int) -> None:
        # Modifies: self.score only
        # Does NOT modify: self.name, self.health
        self.score = self.score + points

    def reset(self: "Player") -> None:
        # Modifies: self.health, self.score
        # Does NOT modify: self.name
        self.health = 100
        self.score = 0


def main() -> None:
    p: Player = Player(name="Alice", health=100, score=0)

    # After take_damage: health changes, name and score preserved
    p.take_damage(30)
    assert p.health == 70
    assert p.name == "Alice"  # must still be provable
    assert p.score == 0       # must still be provable

    # After add_score: score changes, name and health preserved
    p.add_score(50)
    assert p.score == 50
    assert p.health == 70     # must still be provable (not havoc'd)
    assert p.name == "Alice"  # must still be provable

    # After reset: health and score change, name preserved
    p.reset()
    assert p.health == 100
    assert p.score == 0
    assert p.name == "Alice"  # must still be provable

    print(p.name, p.health, p.score)


main()
