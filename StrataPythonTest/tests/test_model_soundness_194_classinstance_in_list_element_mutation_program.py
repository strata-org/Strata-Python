# ClassInstance in list element mutation — `tasks[i].field = v` requires read-
# modify-write-back (4 steps); compound expression must decompose
"""
When ClassInstances are stored in a list, modifying an element requires:
1. Read the element from the list (List_get)
2. Modify the ClassInstance (reconstruct with new attrs)
3. Write the modified element back (List_set)
4. Rebind the list variable

In CPython, `items[i].field = value` modifies in place (reference).
Under value semantics, the element in the list is a COPY. Modifying
the copy doesn't affect the list unless you write it back.

Finding 087 identified this. This finding provides the COMPLETE
translation pattern showing all 4 steps.

Uses ONLY confirmed-accepted constructs: @dataclass, list, int.
"""
from dataclasses import dataclass


@dataclass
class Task:
    name: str
    done: bool
    priority: int


def mark_done(tasks: list[Task], index: int) -> list[Task]:
    """Mark task at index as done — must write back to list."""
    task: Task = tasks[index]  # step 1: read
    task = Task(name=task.name, done=True, priority=task.priority)  # step 2: modify
    tasks[index] = task  # step 3: write back
    return tasks  # step 4: return modified list


def increment_priority(tasks: list[Task], index: int) -> list[Task]:
    task: Task = tasks[index]
    task = Task(name=task.name, done=task.done, priority=task.priority + 1)
    tasks[index] = task
    return tasks


def mark_all_done(tasks: list[Task]) -> list[Task]:
    i: int = 0
    while i < len(tasks):
        task: Task = tasks[i]
        task = Task(name=task.name, done=True, priority=task.priority)
        tasks[i] = task
        i = i + 1
    return tasks


def count_done(tasks: list[Task]) -> int:
    count: int = 0
    for t in tasks:
        if t.done:
            count = count + 1
    return count


def main() -> None:
    tasks: list[Task] = [
        Task(name="a", done=False, priority=1),
        Task(name="b", done=False, priority=2),
        Task(name="c", done=False, priority=3),
    ]

    # Mark first task done
    tasks = mark_done(tasks, 0)
    assert tasks[0].done == True
    assert tasks[1].done == False  # others unchanged

    # Increment priority
    tasks = increment_priority(tasks, 1)
    assert tasks[1].priority == 3

    # Mark all done
    tasks = mark_all_done(tasks)
    assert count_done(tasks) == 3

    print(tasks[0].done, tasks[1].priority, count_done(tasks))


main()
