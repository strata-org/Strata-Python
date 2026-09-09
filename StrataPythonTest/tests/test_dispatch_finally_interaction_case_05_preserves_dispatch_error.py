"""A normal finally completion resumes the pending dispatch exception."""


EVENTS = []

try:
    try:
        object().missing
    finally:
        EVENTS.append("finally")
except Exception as error:
    RESULT = (type(error).__name__, EVENTS)
else:
    RESULT = ("not raised", EVENTS)
