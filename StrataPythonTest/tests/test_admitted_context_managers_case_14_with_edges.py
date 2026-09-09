class EnterError(Exception):
    pass


class BodyError(Exception):
    pass


class ExitError(Exception):
    pass


class TruthError(Exception):
    pass


class RaisingTruth:
    def __bool__(self):
        raise TruthError("truth test")


class EnterFails:
    def __enter__(self):
        raise EnterError("enter")

    def __exit__(self, exception_type, exception, traceback):
        raise ExitError("exit should not run")


class NormalExitRaises:
    def __enter__(self):
        return 1

    def __exit__(self, exception_type, exception, traceback):
        if exception_type is None:
            raise ExitError("normal")
        raise ExitError("unexpected")


class FalseExit:
    def __enter__(self):
        return 1

    def __exit__(self, exception_type, exception, traceback):
        return False


class TrueExit:
    def __enter__(self):
        return 1

    def __exit__(self, exception_type, exception, traceback):
        return True


class ReplacementExit:
    def __enter__(self):
        return 1

    def __exit__(self, exception_type, exception, traceback):
        raise ExitError("replacement")


class BindingExit:
    def __enter__(self):
        return 1

    def __exit__(self, exception_type, exception, traceback):
        raise ExitError(exception_type.__name__)


class TruthinessExit:
    def __enter__(self):
        return 1

    def __exit__(self, exception_type, exception, traceback):
        return RaisingTruth()


def enter_failure_does_not_call_exit():
    try:
        with EnterFails():
            pass
    except EnterError:
        return "EnterError"


def normal_completion_calls_exit():
    try:
        with NormalExitRaises():
            pass
    except ExitError as error:
        return str(error)


def false_exit_propagates():
    try:
        with FalseExit():
            raise BodyError("body")
    except BodyError:
        return "BodyError"


def true_exit_suppresses():
    with TrueExit():
        raise BodyError("body")
    return "suppressed"


def exit_exception_replaces_body_exception():
    try:
        with ReplacementExit():
            raise BodyError("body")
    except ExitError as error:
        return str(error), type(error.__context__).__name__


def target_binding_failure_is_sent_to_exit():
    try:
        with BindingExit() as (left, right):
            pass
    except ExitError as error:
        return str(error), type(error.__context__).__name__


def exit_exception_replaces_return():
    try:
        with ReplacementExit():
            return "pending return"
    except ExitError:
        return "exit replaced return"


def truthiness_error_replaces_body_exception():
    try:
        with TruthinessExit():
            raise BodyError("body")
    except TruthError as error:
        return str(error), type(error.__context__).__name__


def with_target_survives_exit():
    with FalseExit() as value:
        inside = value
    return inside, value


RESULT = (
    enter_failure_does_not_call_exit(),
    normal_completion_calls_exit(),
    false_exit_propagates(),
    true_exit_suppresses(),
    exit_exception_replaces_body_exception(),
    target_binding_failure_is_sent_to_exit(),
    exit_exception_replaces_return(),
    truthiness_error_replaces_body_exception(),
    with_target_survives_exit(),
)
