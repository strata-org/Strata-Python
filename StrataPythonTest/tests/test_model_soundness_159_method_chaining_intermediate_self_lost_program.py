# Method chaining on temporaries — `q.where("x").where("y")` requires ANF for
# intermediate receivers; expression-as-receiver not just variables
"""
Method chaining pattern: `obj.method1().method2()` where each method
returns `self` (or a new instance). Under value semantics, the intermediate
result of method1() is a NEW ClassInstance. If method2() mutates fields,
those mutations apply to the intermediate copy, not the original.

But the deeper issue: if method1() returns self (the pattern for builders),
the Laurel model creates a COPY. The caller's reference to the original
object never sees the changes from method2().

This is related to finding 086 (builder pattern) but focuses on the
CHAINING aspect: `obj.a().b().c()` where intermediate results are lost.

Uses ONLY confirmed-accepted constructs: @dataclass, method def, int, str.
"""
from dataclasses import dataclass


@dataclass
class QueryBuilder:
    table: str
    conditions: int  # count of conditions (simplified)
    limit_val: int

    def where(self: "QueryBuilder", condition: str) -> "QueryBuilder":
        # Returns new instance with incremented condition count
        return QueryBuilder(
            table=self.table,
            conditions=self.conditions + 1,
            limit_val=self.limit_val
        )

    def limit(self: "QueryBuilder", n: int) -> "QueryBuilder":
        return QueryBuilder(
            table=self.table,
            conditions=self.conditions,
            limit_val=n
        )

    def get_conditions(self: "QueryBuilder") -> int:
        return self.conditions

    def get_limit(self: "QueryBuilder") -> int:
        return self.limit_val


def chained_build() -> int:
    # Method chaining: each call returns a new QueryBuilder
    q: QueryBuilder = QueryBuilder(table="users", conditions=0, limit_val=0)
    result: QueryBuilder = q.where("age > 18").where("active = true").limit(10)
    # result should have conditions=2, limit_val=10
    return result.get_conditions()


def intermediate_lost() -> int:
    """The intermediate results of chaining are temporaries."""
    q: QueryBuilder = QueryBuilder(table="orders", conditions=0, limit_val=0)
    # q.where("x") returns a NEW QueryBuilder — q itself is unchanged
    q2: QueryBuilder = q.where("status = pending")
    # q still has conditions=0
    # q2 has conditions=1
    return q.get_conditions() + q2.get_conditions()  # 0 + 1 = 1


def reassign_chain() -> int:
    """Correct pattern: reassign to capture chain result."""
    q: QueryBuilder = QueryBuilder(table="items", conditions=0, limit_val=100)
    q = q.where("price > 0")
    q = q.where("stock > 0")
    q = q.limit(50)
    return q.get_conditions() + q.get_limit()  # 2 + 50 = 52


def main() -> None:
    # Chained method calls
    assert chained_build() == 2

    # Intermediate values are independent copies
    assert intermediate_lost() == 1  # 0 + 1

    # Reassignment pattern
    assert reassign_chain() == 52  # 2 + 50

    print(chained_build(), intermediate_lost(), reassign_chain())


main()
