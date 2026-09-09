# `except (ValueError, KeyError) as e:` tuple-of-types handler — translator
# only handles single-type except; tuple form requires OR-semantics in
# exception type check
"""
EXCEPT WITH TUPLE OF EXCEPTION TYPES — NO TRANSLATION

The subset allows:
  - try / except SomeError as e: for built-in exceptions
  - ValueError, TypeError, IndexError, KeyError, RuntimeError

CPython also supports (and it's standard Python):
  except (ValueError, KeyError) as e:
This catches EITHER exception type in a single handler.

CPython behavior:
  try:
      d = {}
      d["missing"]  # raises KeyError
  except (ValueError, KeyError) as e:
      result = "caught"
  # result == "caught"

Model behavior:
  The translator likely handles `except ValueError:` by checking
  if the exception tag matches ValueError. But the tuple form
  `except (ValueError, KeyError):` requires checking if the tag
  matches ANY of the types in the tuple.

  If the translator only handles single-type except clauses:
    except (ValueError, KeyError): → translation error or Hole
  
  If it treats the tuple as a single type name "(ValueError, KeyError)":
    → never matches → exception propagates → UNSOUND (reports unhandled
      exception for a program that handles it correctly)

This is distinct from:
  - Finding 115 (multiple except CLAUSES — separate handlers)
  - Finding 302 (isinstance with tuple of types)
  - Finding 208 (except must match error type)

The tuple-in-except form is syntactically different from multiple
except clauses. It's ONE handler that catches MULTIPLE types.
This is extremely common in real code:
  except (OSError, IOError) as e:
  except (ValueError, TypeError) as e:

ROOT CAUSE: The except-clause translation assumes a single type name.
The tuple form requires OR-semantics in the exception type check.
"""


def catch_either_error(x: int) -> str:
    """Catch ValueError OR KeyError in one handler.
    
    CPython: catches whichever is raised.
    Model: if tuple form not translated, exception propagates.
    """
    try:
        if x == 0:
            raise ValueError("zero")
        elif x < 0:
            raise KeyError("negative")
        return "ok"
    except (ValueError, KeyError) as e:
        return "caught"


def catch_with_message(s: str) -> str:
    """Catch multiple types and use the error message.
    
    CPython: e holds whichever exception was raised.
    Model: if handler never activates, str(e) is never reached.
    """
    try:
        n: int = int(s)
        if n < 0:
            raise KeyError("negative")
        return str(n)
    except (ValueError, KeyError) as e:
        return "error"


def nested_tuple_except(x: int, y: int) -> int:
    """Multiple try blocks with tuple-of-types handlers.
    
    CPython: each handler catches its set of exceptions.
    Model: if tuple form fails, both handlers are dead code.
    """
    result: int = 0
    try:
        result = x // y  # may raise ZeroDivisionError... but that's not in our tuple
    except (ValueError, RuntimeError):
        result = -1

    try:
        if result < 0:
            raise ValueError("negative result")
        if result > 100:
            raise KeyError("too large")
    except (ValueError, KeyError):
        result = 0

    return result


def first_matching_type(x: int) -> str:
    """The tuple form catches the FIRST matching type (order irrelevant).
    
    Unlike multiple except clauses where order matters (finding 115),
    the tuple form is a SET — any match triggers the handler.
    
    CPython: (ValueError, KeyError) catches either, no priority.
    Model: must check tag against ALL types in tuple.
    """
    try:
        if x == 1:
            raise ValueError("val")
        if x == 2:
            raise KeyError("key")
        if x == 3:
            raise RuntimeError("runtime")
        return "no error"
    except (ValueError, KeyError):
        return "val_or_key"
    except RuntimeError:
        return "runtime"


def main() -> None:
    # catch_either_error
    assert catch_either_error(0) == "caught"   # ValueError caught
    assert catch_either_error(-1) == "caught"  # KeyError caught
    assert catch_either_error(5) == "ok"       # no exception

    # catch_with_message
    assert catch_with_message("abc") == "error"  # ValueError from int()
    assert catch_with_message("-5") == "error"   # KeyError from negative
    assert catch_with_message("42") == "42"      # no exception

    # nested_tuple_except
    assert nested_tuple_except(10, 2) == 5
    assert nested_tuple_except(200, 1) == 0  # 200 > 100, KeyError caught

    # first_matching_type
    assert first_matching_type(1) == "val_or_key"
    assert first_matching_type(2) == "val_or_key"
    assert first_matching_type(3) == "runtime"
    assert first_matching_type(4) == "no error"

    print("all passed")


main()
