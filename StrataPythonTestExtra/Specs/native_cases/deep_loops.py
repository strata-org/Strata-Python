# A nest of d loops reads its innermost body d + 1 times, not about 2^d times.
from typing import List

def deep(xs: List[int]) -> None:
    for v0 in xs:
        for v1 in xs:
            for v2 in xs:
                for v3 in xs:
                    for v4 in xs:
                        for v5 in xs:
                            for v6 in xs:
                                for v7 in xs:
                                    for v8 in xs:
                                        for v9 in xs:
                                            for v10 in xs:
                                                for v11 in xs:
                                                    for v12 in xs:
                                                        for v13 in xs:
                                                            for v14 in xs:
                                                                for v15 in xs:
                                                                    for v16 in xs:
                                                                        for v17 in xs:
                                                                            for v18 in xs:
                                                                                for v19 in xs:
                                                                                    for v20 in xs:
                                                                                        for v21 in xs:
                                                                                            for v22 in xs:
                                                                                                for v23 in xs:
                                                                                                    assert v0 > 0, "v0 is positive"

def deep_taint(xs: List[int]) -> None:
    for a in xs:
        assert a > 0, "a is positive"
        for b in xs:
            for c in xs:
                y = 1
