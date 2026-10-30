# Two classes whose code breaks their declarations: Account, whose __init__ stores a str
# into the int field balance and leaves the field limit unset on one path, and the TypedDict
# Movie, built without its required key year, which one path then sets to a str.  Each class
# body's attributes state the declarations as written.
import random
from typing import TypedDict


def coin():
    return random.random() < 0.5


class Account:
    owner: str
    balance: int
    limit: int

    def __init__(self, owner: str, vip: bool):
        self.owner = owner
        if vip:
            self.balance = 0
            self.limit = 1000
        else:
            self.balance = "pending"


a = Account("ann", coin())


class Movie(TypedDict):
    title: str
    year: int


m = Movie(title="Alien")
if coin():
    m["year"] = 1979
else:
    m["year"] = "unknown"
