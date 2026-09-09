# `continue`/`break` inside `try`/`finally` — finally must execute before
# control transfer; model may skip finally on continue/break path
"""
CONTINUE/BREAK INSIDE TRY/FINALLY — FINALLY EXECUTES BEFORE CONTROL TRANSFER

The subset allows:
  - for/while loops with break/continue (IN)
  - try/except/finally (IN)

CPython behavior:
  for x in items:
      try:
          if x < 0:
              continue  # finally STILL executes before continuing!
          process(x)
      finally:
          cleanup()  # ALWAYS runs, even on continue/break

  This means: `continue` inside a `try` block does NOT skip the `finally`.
  The `finally` executes, THEN the continue takes effect.

  Similarly for `break`:
  for x in items:
      try:
          if x == sentinel:
              break  # finally executes before breaking!
      finally:
          cleanup()  # runs before the break takes effect

Model behavior:
  The exception-as-value model translates `continue` and `break` as
  control flow jumps. `finally` is translated as code that runs after
  the try body. The interaction between these two is complex:

  If `continue` is translated as a jump to loop-head:
    → finally block is SKIPPED (wrong)
  If `continue` is translated as setting a flag + falling through:
    → finally block executes, then flag checked → correct but complex

  The model likely handles `finally` for the exception path (finding 063)
  and the return path (finding 160), but the CONTINUE/BREAK path through
  finally is a third case that may not be modeled.

ROOT CAUSE: The model has three control-flow mechanisms that interact:
  1. Exception propagation (exception-as-value)
  2. Return (function exit)
  3. Break/continue (loop control)

  Finding 063 covers: finally + exception
  Finding 160 covers: finally + return
  This finding covers: finally + continue/break (NOVEL)

  Each requires finally to execute before the control transfer.
  If the model only handles (1) and (2), break/continue skip finally.

This is distinct from:
  - Finding 063 (finally always executes) — covers exception path only
  - Finding 160 (finally return override) — covers return path only
  - Finding 249 (try/except in loop) — no finally, no continue/break
  - Finding 054 (break/continue not modeled) — doesn't mention finally
"""


def continue_executes_finally(items: list[int]) -> list[int]:
    """Continue inside try — finally must execute before continuing.
    
    CPython: finally runs for EVERY iteration, including those that continue.
    Model: if continue skips finally, cleanup effects are lost.
    """
    processed: list[int] = []
    cleanup_count: int = 0
    for x in items:
        try:
            if x < 0:
                continue  # skip negative items, BUT finally still runs
            processed.append(x)
        finally:
            cleanup_count = cleanup_count + 1
    # cleanup_count should equal len(items) — finally runs every iteration
    # Even iterations that hit continue!
    processed.append(cleanup_count)
    return processed


def break_executes_finally(items: list[int], sentinel: int) -> list[int]:
    """Break inside try — finally must execute before breaking.
    
    CPython: finally runs on the iteration that breaks.
    Model: if break skips finally, the cleanup for that iteration is lost.
    """
    processed: list[int] = []
    final_ran: bool = False
    for x in items:
        try:
            if x == sentinel:
                break  # stop at sentinel, BUT finally still runs
            processed.append(x)
        finally:
            final_ran = True
    # final_ran should be True (finally ran on the break iteration)
    if final_ran:
        processed.append(-999)  # marker that finally ran
    return processed


def continue_with_accumulator(items: list[int]) -> int:
    """Accumulate in finally, even for skipped items.
    
    CPython: total_seen counts ALL items (finally always runs).
    Model: if continue skips finally, total_seen only counts non-skipped.
    """
    total_processed: int = 0
    total_seen: int = 0
    for x in items:
        try:
            if x % 2 == 0:
                continue  # skip even numbers
            total_processed = total_processed + x
        finally:
            total_seen = total_seen + 1  # counts ALL items, even skipped
    return total_seen


def nested_try_continue(items: list[int]) -> int:
    """Nested try with continue — both finally blocks execute.
    
    CPython: inner finally runs, then outer finally runs, then continue.
    Model: must execute BOTH finally blocks before continuing.
    """
    outer_count: int = 0
    inner_count: int = 0
    for x in items:
        try:
            try:
                if x < 0:
                    continue
            finally:
                inner_count = inner_count + 1
        finally:
            outer_count = outer_count + 1
    return inner_count + outer_count  # should be 2 * len(items)


def main() -> None:
    # continue_executes_finally
    result1: list[int] = continue_executes_finally([1, -2, 3, -4, 5])
    # processed: [1, 3, 5] + cleanup_count
    # cleanup_count = 5 (finally ran for ALL 5 iterations)
    assert result1 == [1, 3, 5, 5]

    # break_executes_finally
    result2: list[int] = break_executes_finally([10, 20, 0, 30], 0)
    # processed: [10, 20] + marker -999 (finally ran on break iteration)
    assert result2 == [10, 20, -999]

    # continue_with_accumulator
    # items: [1, 2, 3, 4, 5] — evens (2,4) skipped, odds (1,3,5) processed
    # total_seen = 5 (finally counts ALL items)
    assert continue_with_accumulator([1, 2, 3, 4, 5]) == 5

    # nested_try_continue
    # items: [1, -1, 2] — 3 items, both finally blocks run each iteration
    # inner_count = 3, outer_count = 3, total = 6
    assert nested_try_continue([1, -1, 2]) == 6

    print("all passed")


main()
