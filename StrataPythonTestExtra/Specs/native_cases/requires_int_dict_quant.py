from typing import Dict

# Dict[int, _] quantifier inside a @requires contract: the clause must be
# dropped (preconditions.size == 0) and the warning must carry the
# .pySpecDroppedAssertion kind, not the generic pySpecParsingWarning.
@requires(lambda D: all(len(v) >= 1 for v in D.values()))
def f(D: Dict[int, str]) -> None:
    ...
