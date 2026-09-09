# List of ClassInstances element mutation (`tasks[i].done = True`) — compound
# read-modify-write not modeled; changes invisible
"""
A list of class instances (`list[MyClass]`) stores ClassInstance values
in a ListAny. Accessing an element and modifying its field creates a
divergence: in CPython the list element IS the object (reference), so
mutations through the extracted reference are visible in the list. In
the value model, extracting an element gives a COPY — mutations to the
copy don't affect the list.

This combines findings 001 (list aliasing) and 011 (class field mutation)
into a single pattern that's extremely common: iterating over a list of
objects and modifying each one.
"""
from dataclasses import dataclass


@dataclass
class Task:
    name: str
    done: bool


def mark_done(tasks: list[Task], index: int) -> None:
    tasks[index].done = True
    # CPython: modifies the Task object IN the list
    # Model: extracts a copy, modifies the copy, copy is discarded


def mark_all_done(tasks: list[Task]) -> None:
    for t in tasks:
        t.done = True
    # CPython: each t is a reference to the list element; mutation visible
    # Model: each t is a copy; mutations are discarded after each iteration


def count_done(tasks: list[Task]) -> int:
    count: int = 0
    for t in tasks:
        if t.done:
            count = count + 1
    return count


def main() -> None:
    tasks: list[Task] = [
        Task(name="write", done=False),
        Task(name="review", done=False),
        Task(name="deploy", done=False),
    ]

    # Mark one task done via index
    mark_done(tasks, 0)
    # CPython: tasks[0].done == True
    # Model: tasks unchanged (copy was modified, not the list element)
    assert tasks[0].done == True

    # Mark all done via iteration
    mark_all_done(tasks)
    # CPython: all tasks have done=True
    # Model: tasks unchanged (loop variable copies were modified)
    assert count_done(tasks) == 3

    print(tasks[0].done, count_done(tasks))


main()
