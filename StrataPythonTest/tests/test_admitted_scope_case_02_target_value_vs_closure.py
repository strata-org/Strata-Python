class E(Exception):
    pass


def return_exception_value():
    try:
        raise E("direct")
    except E as error:
        return error


def return_readers():
    try:
        raise E("saved")
    except E as error:
        saved = error

        def read_target():
            return error

        def read_saved():
            return saved

        return read_target, read_saved


returned_exception = return_exception_value()
target_reader, saved_reader = return_readers()

try:
    target_reader()
except NameError:
    target_reader_result = "NameError"
else:
    target_reader_result = "still bound"

RESULT = (
    type(returned_exception).__name__,
    str(returned_exception),
    target_reader_result,
    str(saved_reader()),
)
