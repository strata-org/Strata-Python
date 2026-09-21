from typing import Dict, Literal

# Literal string keys are str at runtime, so the string-key map model applies.
@requires(lambda D: all(len(v) >= 1 for k, v in D.items()))
def f(D: Dict[Literal["JPEGQuality"], str]) -> None:
    ...
