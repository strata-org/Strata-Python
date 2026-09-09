# Feature: CONTAINERS — list/dict/set heterogeneity, ALIASING, mutation (worklist item 5).
#
# Monty result (pydantic-monty 0.0.18, the running oracle): full CPython-faithful
# reference semantics for containers. All of the following MATCH CPython:
#   a=[1,2]; b=a; a.append(3); b        -> [1, 2, 3]   (alias sees mutation)
#   [1, "two", 3.0]                     -> heterogeneous list OK
#   {1, 2, 2, 3}                        -> set OK (len 3)
#   {"a":1, "b":"two"}; d["c"]=3.0      -> heterogeneous dict + mutation OK
#   transitive (b=a; c=b) & via-container aliasing -> all shared
#
# Strata front end: lists/dicts are encoded as VALUE-SEMANTICS datatypes
# (ListAny / DictStrAny). `b = a` is translated as a COPY, not an alias
# (frontend-subset.md:233, 498-500). Mutation through one name is NOT visible
# through the other -> SILENTLY UNSOUND. See the large pending soundness cluster
# (test_soundness_list_alias_mutation.py and ~9 siblings).
#
# Matrix: SPLITS.
#   * homogeneous list[T]/dict[K,V]/tuple, index/len/in/append/iter, NO alias -> (A)
#   * ALIASING + mutation-through-alias                                       -> (B) silently unsound  [HEADLINE]
#   * heterogeneous element types                                            -> (C) (Monty IN; Frontend doc-OUT)
#   * set                                                                    -> (C) (Monty IN; Frontend "may grow")
#
# The witness below is the minimal (B) case (also produced by model.py's z3 search).
# This program is in Monty's subset (list literals, subscription assignment).

a = [1, 2, 3]
b = a            # ALIAS (Frontend ListAny models this as a value COPY)
b[0] = 99        # mutate through the alias

# Observable: on Monty & CPython this is 99 (a and b are the same object).
# Frontend's value-copy ListAny encoding verifies it as 1 -> unsound (cell B).
a[0]
