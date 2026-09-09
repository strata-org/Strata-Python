# Object stored in container then modified — container holds stale copy;
# modifications invisible through container
"""
Storing a class instance in a dict or list, then modifying the instance,
creates a divergence: CPython's dict/list holds a reference (sees the
change), but the value model's dict/list holds a copy (doesn't see it).

This combines findings 001/002 (container aliasing) with ClassInstance
value semantics in a pattern that's common in registries and caches.
"""
from dataclasses import dataclass


@dataclass
class User:
    name: str
    score: int


def register_and_update(registry: dict[str, User]) -> None:
    u: User = User(name="alice", score=0)
    registry["alice"] = u
    # Now modify u
    u.score = 100
    # CPython: registry["alice"].score == 100 (same object)
    # Model: registry["alice"].score == 0 (stored a copy)


def build_team() -> list[User]:
    members: list[User] = []
    alice: User = User(name="alice", score=0)
    bob: User = User(name="bob", score=0)
    members = members + [alice, bob]

    # Update scores after adding to list
    alice.score = 50
    bob.score = 75

    # CPython: members[0].score == 50, members[1].score == 75
    # Model: members[0].score == 0, members[1].score == 0
    return members


def main() -> None:
    # Registry pattern
    reg: dict[str, User] = {}
    register_and_update(reg)
    # CPython: reg["alice"].score == 100
    assert reg["alice"].score == 100

    # Team building
    team: list[User] = build_team()
    # CPython: modifications visible through list
    assert team[0].score == 50
    assert team[1].score == 75

    print(reg["alice"].score, team[0].score, team[1].score)


main()
