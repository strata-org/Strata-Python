# Generated PyHard analysis. Original source line numbers are shown as L<n>.
# Every dispatch/type/shape claim lowers to assert followed by the same assume.
# Canonical machine-readable input: pyhard.analysis schema v1.
class LocalFileError(FileNotFoundError):
    pass


class HasOperation:
    # L6 pyhard[summary HasOperation.operation] returns={int}; escapes={}
    def operation(self) -> int:
        # L7 pyhard[flow HasOperation.operation in] self -> (binding=definitely_bound; tags={HasOperation}; defs={param:self}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L7 pyhard[flow HasOperation.operation out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), self -> (binding=definitely_bound; tags={HasOperation}; defs={param:self}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L7 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 7


class MissingOperation:
    pass


# L14 pyhard[summary caught_dispatch] returns={int}; escapes={}
# L14 pyhard[type parameter] assert/assume conforms(value, HasOperation | MissingOperation); boundary nondet over 24 closed tags
def caught_dispatch(value: HasOperation | MissingOperation) -> int:
    # L15 pyhard[flow caught_dispatch in] attribute_error -> (binding=definitely_unbound; tags={}; defs={unbound:attribute_error}), value -> (binding=definitely_bound; tags={HasOperation, MissingOperation}; defs={param:value}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
    # L15 pyhard[flow caught_dispatch out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), attribute_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L17:C5, unbound:attribute_error}), value -> (binding=definitely_bound; tags={HasOperation, MissingOperation}; defs={param:value}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
    try:
        # L16 pyhard[flow caught_dispatch in] attribute_error -> (binding=definitely_unbound; tags={}; defs={unbound:attribute_error}), value -> (binding=definitely_bound; tags={HasOperation, MissingOperation}; defs={param:value}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L16 pyhard[flow caught_dispatch out:raise:AttributeError] $exception -> (binding=definitely_bound; tags={AttributeError}; defs={raise:AttributeError}), attribute_error -> (binding=definitely_unbound; tags={}; defs={unbound:attribute_error}), value -> (binding=definitely_bound; tags={HasOperation, MissingOperation}; defs={param:value}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L16 pyhard[flow caught_dispatch out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), attribute_error -> (binding=definitely_unbound; tags={}; defs={unbound:attribute_error}), value -> (binding=definitely_bound; tags={HasOperation, MissingOperation}; defs={param:value}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L16 pyhard[read caught_dispatch.value@16] binding=definitely_bound
        # L16 pyhard[type return] assert/assume conforms(result, int); observed={int}; evaluation may raise={AttributeError}
        # L16 pyhard[dispatch value.operation()] assert/assume key in {HasOperation, MissingOperation}
        # L16 pyhard[row {HasOperation}] invoke_method; owner=HasOperation; label=HasOperation.operation; result={int}
        # L16 pyhard[row {MissingOperation}] raise_attribute_error; raises={AttributeError}
        return value.operation()
    except AttributeError as attribute_error:
        # L18 pyhard[flow caught_dispatch in] attribute_error -> (binding=definitely_bound; tags={AttributeError}; defs={handler:L17:C5}), value -> (binding=definitely_bound; tags={HasOperation, MissingOperation}; defs={param:value}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L18 pyhard[flow caught_dispatch out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), attribute_error -> (binding=definitely_bound; tags={AttributeError}; defs={handler:L17:C5}), value -> (binding=definitely_bound; tags={HasOperation, MissingOperation}; defs={param:value}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L18 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 0


# L21 pyhard[summary routed_exception] returns={int}; escapes={ValueError}
# L21 pyhard[type parameter] assert/assume conforms(flag, bool); boundary nondet over 24 closed tags
def routed_exception(flag: bool) -> int:
    # L22 pyhard[flow routed_exception in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
    # L22 pyhard[flow routed_exception out:raise:ValueError] $exception -> (binding=definitely_bound; tags={ValueError}; defs={raise:ValueError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L28:C5}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
    # L22 pyhard[flow routed_exception out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={handler-cleanup:L26:C5})
    try:
        # L23 pyhard[flow routed_exception in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
        # L23 pyhard[flow routed_exception out] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
        # L23 pyhard[flow routed_exception out:raise:LocalFileError] $exception -> (binding=definitely_bound; tags={LocalFileError}; defs={raise:LocalFileError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
        # L23 pyhard[read routed_exception.flag@12] binding=definitely_bound
        # L23 pyhard[dispatch flag] assert/assume key in {bool}
        # L23 pyhard[row {bool}] exact_builtin_truth; result={bool}
        if flag:
            # L24 pyhard[flow routed_exception in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
            # L24 pyhard[flow routed_exception out:raise:LocalFileError] $exception -> (binding=definitely_bound; tags={LocalFileError}; defs={raise:LocalFileError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
            raise LocalFileError()
        # L25 pyhard[flow routed_exception in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
        # L25 pyhard[flow routed_exception out:raise:KeyError] $exception -> (binding=definitely_bound; tags={KeyError}; defs={raise:KeyError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
        raise KeyError()
    except OSError as os_error:
        # L27 pyhard[flow routed_exception in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_bound; tags={LocalFileError}; defs={handler:L26:C5}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L27 pyhard[flow routed_exception out:return] $result -> (binding=definitely_bound; tags={int}; defs={return}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_unbound; tags={}; defs={unbound:lookup_error}), os_error -> (binding=definitely_bound; tags={LocalFileError}; defs={handler:L26:C5}; points-to={alloc:L24:C19, boundary:HasOperation.operation, boundary:caught_dispatch, boundary:external, boundary:routed_exception})
        # L27 pyhard[type return] assert/assume conforms(result, int); observed={int}
        return 1
    except LookupError as lookup_error:
        # L29 pyhard[flow routed_exception in] flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_bound; tags={KeyError}; defs={handler:L28:C5}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
        # L29 pyhard[flow routed_exception out:raise:ValueError] $exception -> (binding=definitely_bound; tags={ValueError}; defs={raise:ValueError}), flag -> (binding=definitely_bound; tags={bool}; defs={param:flag}), lookup_error -> (binding=definitely_bound; tags={KeyError}; defs={handler:L28:C5}), os_error -> (binding=definitely_unbound; tags={}; defs={unbound:os_error})
        raise ValueError()
