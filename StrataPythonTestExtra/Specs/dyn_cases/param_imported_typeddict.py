# A known gap: a parameter's check tests a part of its type only by its class (here `dict` or
# `list`) when PySpec keeps that part as a name: a name that the model imports or reads from an
# imported module, a quoted name that the module defines only below the place that quotes it, or
# an alias of these. None of these checks tests `Name` in `Inner`, `Later`, `Late` or a child of
# `Node`, nor the elements of `Names` (docs/PythonToDyn.md §12.9, *The program keeps the declared
# types*).
from typing import List, TypedDict
import param_typeddict_shapes
from param_typeddict_shapes import Inner, Names

Local = Inner

Outer = TypedDict("Outer", {"Items": List["Later"]})
Later = TypedDict("Later", {"Name": str})

Node = TypedDict("Node", {"Name": str, "Children": List["Node"]})

Pending = List["Late"]
Late = TypedDict("Late", {"Name": str})

def put(item: Inner) -> None:
    ...

def put_all(items: List[Local]) -> None:
    ...

def put_qualified(item: param_typeddict_shapes.Inner) -> None:
    ...

def put_outer(o: Outer) -> None:
    ...

def put_names(xs: Names) -> None:
    ...

def put_node(n: Node) -> None:
    ...

def put_pending(xs: Pending) -> None:
    ...
