from dataclasses import FrozenInstanceError, dataclass, replace


@dataclass(frozen=True)
class Key:
    value: int


def frozen_write_and_replace():
    original = Key(1)
    try:
        original.value = 2
    except AttributeError as error:
        write_result = (
            type(error).__name__,
            isinstance(error, FrozenInstanceError),
        )

    replacement = replace(original, value=2)
    return (
        write_result,
        original.value,
        replacement.value,
        original == Key(1),
        original == replacement,
    )


RESULT = frozen_write_and_replace()
