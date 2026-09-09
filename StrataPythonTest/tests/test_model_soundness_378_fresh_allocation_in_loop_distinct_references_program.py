# Fresh allocation in loop — N iterations need N distinct Composite refs;
# requires monotonic counter + inductive freshness reasoning
"""
FRESH ALLOCATION IN LOOP — EACH ITERATION MUST PRODUCE DISTINCT REFERENCE

CPython: for i in range(3): objs.append(MyClass(i))
         Creates 3 DISTINCT objects. objs[0] is not objs[1].

Model (Composite/heap):
  Each MyClass() call must produce a FRESH Composite reference.
  fresh(ref) means: ref ≠ all previously-allocated references.

  Without freshness: solver can't prove objs[0] ≠ objs[1].
  Modifying objs[0].field might affect objs[1].field (same ref!).

  The heap model uses nextReference counter:
    alloc(heap) → (MkComposite(heap.nextReference), heap{nextReference += 1})

  In a loop, each iteration must increment the counter.
  The solver needs: ref_i ≠ ref_j for all i ≠ j.

Finding 104 covers two allocations. This finding covers N allocations
in a LOOP — requiring inductive freshness reasoning.
"""
from dataclasses import dataclass


@dataclass
class Task:
    id: int
    done: bool


def create_tasks(n: int) -> list[Task]:
    """Create n independent tasks in a loop."""
    tasks: list[Task] = []
    i: int = 0
    while i < n:
        tasks.append(Task(i, False))
        i += 1
    return tasks


def modify_one_task(tasks: list[Task], idx: int) -> list[Task]:
    """Modify one task — others must be unaffected."""
    modified: Task = Task(tasks[idx].id, True)
    tasks[idx] = modified
    return tasks


def all_independent() -> bool:
    """Verify each task is independent after creation."""
    tasks: list[Task] = create_tasks(3)
    # Modify task 0
    tasks = modify_one_task(tasks, 0)
    # Tasks 1 and 2 must be unaffected
    # Under heap semantics: requires freshness (distinct refs)
    # Under value semantics: trivially independent (no refs)
    return tasks[0].done and not tasks[1].done and not tasks[2].done


def factory_in_loop() -> bool:
    """Factory function called in loop — each call returns fresh object."""
    items: list[Task] = []
    items.append(Task(1, False))
    items.append(Task(2, False))
    items.append(Task(3, False))
    # All three are independent
    items[1] = Task(items[1].id, True)
    return not items[0].done and items[1].done and not items[2].done


def main() -> None:
    # Test 1: create in loop, verify independence
    assert all_independent()

    # Test 2: factory pattern
    assert factory_in_loop()

    # Test 3: verify distinct IDs
    tasks: list[Task] = create_tasks(5)
    assert tasks[0].id == 0
    assert tasks[4].id == 4
    assert tasks[0].id != tasks[1].id

    print("all passed")


main()
