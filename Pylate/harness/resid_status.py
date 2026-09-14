"""The one derivation of a residual site's status and of what counts as a
dispatch site (RENDER_SPEC.md section 4).

Status is derived, never stored, so every consumer must derive it the same
way. This module is the single implementation: the analyzer's text report,
the log renderer, and the summary counters all import it. It depends on
nothing but the log record shape, so importing it does not pull the
analyzer into the renderer.

The Lean emitter carries its own copy of these rules (Emit.lean:
`residStatus`, `isDispatchSite`). `tests/test_status_agreement.py` pins the
two together by recomputing the summary from the emitted residuals.
"""

#: Kinds that pose no dispatch question: a store resolves a target but is
#: excluded by convention, and a name read or an identity test is not
#: dispatched at all. Everything else -- the four value operations plus the
#: protocol operations, which resolve `__bool__`, `__contains__`, `__eq__` and
#: the unary duals -- is counted, so the `deferred` headline agrees with the
#: derived `deferred-dispatch` and `case-split` obligations.
NON_DISPATCH_KINDS = ("setattr", "setitem", "name", "identity",
                      "contract")


def is_dispatch_site(r):
    return r["kind"] not in NON_DISPATCH_KINDS


def residual_status(r):
    """RESOLVED (one target, no error edge, so it compiles to a direct call or
    field access), SPLIT(n) (n targets, a case split for the solver), UNKNOWN
    (an unknown tag reaches the site), MUST_RAISE (every live tag is an error
    row), or empty (one target that can also raise, or a store)."""
    cases = r["cases"]
    tgts = set(cases.values())
    if "deferred" in tgts:
        return "UNKNOWN"
    if not cases and r["errors"]:
        return "MUST_RAISE"
    if len(tgts) == 1 and not r["errors"]:
        return "RESOLVED"
    if len(tgts) > 1:
        return f"SPLIT({len(tgts)})"
    return ""


#: Stores resolve no target, so a dispatch verdict would say nothing about
#: them; they are labelled by what they are instead.
STORE_KINDS = ("setattr", "setitem")


def render_status(r):
    """The label a page or report shows for a site.

    Adds three cases the bare derivation has no room for: a site whose own
    operation never ran (an operand raised first) is UNREACHABLE, a store is
    labelled by its kind, and a site that resolves exactly one target but
    keeps an exception edge is MAY_RAISE -- it needs no type test but does need
    the guard, so calling it devirtualized would overstate the result."""
    status = residual_status(r)
    # A contract row is a verification boundary, not an operation. Its `cases`
    # are structurally empty, so the ladder would read MUST_RAISE for any
    # function that can raise at all -- which would claim the function always
    # raises. Its `errors` still list what escapes.
    if r["kind"] == "contract":
        return "contract"
    if not r.get("reached", True) and not r["cases"] and not r["errors"]:
        return "UNREACHABLE"
    if r["kind"] in STORE_KINDS:
        return status if status == "MUST_RAISE" else r["kind"]
    if not status and r["cases"] and r["errors"]:
        return "MAY_RAISE"
    return status


def summary_counts(residuals):
    """`(sites, devirt, deferred)` over the dispatch sites only."""
    sites = devirt = deferred = 0
    for r in residuals:
        if not is_dispatch_site(r):
            continue
        sites += 1
        status = residual_status(r)
        if status == "RESOLVED":
            devirt += 1
        elif status == "UNKNOWN" or status.startswith("SPLIT"):
            deferred += 1
    return sites, devirt, deferred
