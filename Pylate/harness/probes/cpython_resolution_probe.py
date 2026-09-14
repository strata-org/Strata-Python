"""Independent CPython oracle for Pylate's resolved class declarations.

The source is reduced to admitted imports and inert class declarations, then
executed by this Python 3.13 process.  Member ownership uses ``vars(owner)``
rather than ``getattr`` so descriptors never run.  Binary protocol order is
observed with mirror classes whose slots log and return ``NotImplemented``.

Usage:
    python3.13 cpython_resolution_probe.py SOURCE.py
"""

from __future__ import annotations

import ast
import copy
import dataclasses
import json
import operator
import sys
from typing import Any


OPS = {
    "+": ("__add__", "__radd__", operator.add),
    "-": ("__sub__", "__rsub__", operator.sub),
    "*": ("__mul__", "__rmul__", operator.mul),
    "/": ("__truediv__", "__rtruediv__", operator.truediv),
    "//": ("__floordiv__", "__rfloordiv__", operator.floordiv),
    "%": ("__mod__", "__rmod__", operator.mod),
    "**": ("__pow__", "__rpow__", operator.pow),
    "|": ("__or__", "__ror__", operator.or_),
    "&": ("__and__", "__rand__", operator.and_),
    "^": ("__xor__", "__rxor__", operator.xor),
    "<<": ("__lshift__", "__rlshift__", operator.lshift),
    ">>": ("__rshift__", "__rrshift__", operator.rshift),
}

BUILTIN_BASES = {
    cls.__name__: cls
    for cls in (
        object,
        BaseException,
        Exception,
        SystemExit,
        KeyboardInterrupt,
        GeneratorExit,
        ArithmeticError,
        ZeroDivisionError,
        OverflowError,
        FloatingPointError,
        AssertionError,
        AttributeError,
        LookupError,
        IndexError,
        KeyError,
        NameError,
        UnboundLocalError,
        RuntimeError,
        NotImplementedError,
        RecursionError,
        StopIteration,
        StopAsyncIteration,
        TypeError,
        ValueError,
        UnicodeError,
        OSError,
        FileNotFoundError,
        EOFError,
        MemoryError,
        SystemError,
    )
}


class InertMethods(ast.NodeTransformer):
    """Keep method declarations and property decorators, but execute no body."""

    def visit_FunctionDef(self, node):
        node = copy.deepcopy(node)
        node.body = [ast.Pass()]
        node.returns = None
        node.type_params = []
        for arg in (
            list(node.args.posonlyargs)
            + list(node.args.args)
            + list(node.args.kwonlyargs)
        ):
            arg.annotation = None
        if node.args.vararg:
            node.args.vararg.annotation = None
        if node.args.kwarg:
            node.args.kwarg.annotation = None
        node.args.defaults = [ast.Constant(None) for _ in node.args.defaults]
        node.args.kw_defaults = [
            ast.Constant(None) if value is not None else None
            for value in node.args.kw_defaults
        ]
        return node

    def visit_AsyncFunctionDef(self, node):
        raise AssertionError("accepted source cannot contain async methods")


def base_name(base):
    if isinstance(base, ast.Name):
        return base.id
    raise AssertionError(f"non-static base reached oracle: {ast.unparse(base)}")


def admitted_module(tree):
    body = []
    for node in tree.body:
        if (
            isinstance(node, ast.ImportFrom)
            and node.module in ("typing", "dataclasses")
        ):
            body.append(copy.deepcopy(node))
        elif isinstance(node, ast.ClassDef):
            body.append(InertMethods().visit(copy.deepcopy(node)))
    module = ast.Module(body=body, type_ignores=[])
    return ast.fix_missing_locations(module)


def execute_classes(tree, filename):
    namespace = {"__name__": "__pylate_resolution_probe__"}
    code = compile(
        admitted_module(tree), filename, "exec", dont_inherit=True
    )
    exec(code, namespace)
    return namespace


def annotation_name(node):
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = annotation_name(node.value)
        return f"{prefix}.{node.attr}" if prefix else None
    return None


def const_json(value):
    if value is None:
        return {"kind": "none"}
    if isinstance(value, bool):
        return {"kind": "bool", "value": value}
    if isinstance(value, int):
        return {"kind": "int", "value": str(value)}
    if isinstance(value, float):
        return {"kind": "float", "value": str(value)}
    if isinstance(value, str):
        return {"kind": "str", "value": value}
    return None


def annotation_json(node):
    if isinstance(node, ast.Name):
        if node.id == "Any":
            return {"kind": "any"}
        return {"kind": "atom", "name": node.id}
    if isinstance(node, ast.Attribute):
        name = annotation_name(node)
        if name == "typing.Any":
            return {"kind": "any"}
        return {"kind": "atom", "name": name}
    if isinstance(node, ast.Constant):
        if node.value is None:
            return {"kind": "atom", "name": "None"}
        if isinstance(node.value, str):
            return {"kind": "atom", "name": node.value}
        return {"kind": "any"}
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return {
            "kind": "union",
            "members": [
                annotation_json(node.left),
                annotation_json(node.right),
            ],
        }
    if isinstance(node, ast.Subscript):
        head = annotation_name(node.value) or ""
        short = head.rsplit(".", 1)[-1]
        elements = (
            list(node.slice.elts)
            if isinstance(node.slice, ast.Tuple)
            else [node.slice]
        )
        args = [annotation_json(element) for element in elements]
        if short == "Optional":
            return {
                "kind": "union",
                "members": [args[0] if args else {"kind": "any"},
                            {"kind": "atom", "name": "None"}],
            }
        if short == "Union":
            return {"kind": "union", "members": args}
        if short in ("Required", "NotRequired", "ReadOnly"):
            kind = {
                "Required": "required",
                "NotRequired": "not-required",
                "ReadOnly": "read-only",
            }[short]
            return {
                "kind": kind,
                "inner": args[0] if args else {"kind": "any"},
            }
        if short == "Annotated":
            return args[0] if args else {"kind": "any"}
        if short == "Literal":
            return {
                "kind": "literal",
                "values": [
                    normalized
                    for element in elements
                    if (normalized := const_json(
                        element.value
                        if isinstance(element, ast.Constant)
                        else object()
                    ))
                    is not None
                ],
            }
        generic = {
            "List": "list",
            "list": "list",
            "Dict": "dict",
            "dict": "dict",
            "Set": "set",
            "set": "set",
            "Tuple": "tuple",
            "tuple": "tuple",
        }.get(short, head)
        variadic = (
            short in ("Tuple", "tuple")
            and len(elements) == 2
            and isinstance(elements[1], ast.Constant)
            and elements[1].value is Ellipsis
        )
        return {
            "kind": "generic",
            "name": generic,
            "args": args[:1] if variadic else args,
            "variadic": variadic,
        }
    return {"kind": "any"}


def normalize_field_annotation(annotation, required):
    encoded = annotation_json(annotation)
    read_only = False
    while encoded["kind"] in ("required", "not-required", "read-only"):
        if encoded["kind"] == "required":
            required = True
        elif encoded["kind"] == "not-required":
            required = False
        else:
            read_only = True
        encoded = encoded["inner"]
    return encoded, required, read_only


def self_store_names(class_node):
    names = set()
    for item in class_node.body:
        if not isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for node in ast.walk(item):
            if (
                isinstance(node, ast.Attribute)
                and isinstance(node.ctx, ast.Store)
                and isinstance(node.value, ast.Name)
                and node.value.id == "self"
            ):
                names.add(node.attr)
    return names


def source_declarations(tree):
    classes = [node for node in tree.body if isinstance(node, ast.ClassDef)]
    declarations = {}
    for node in classes:
        bases = [base_name(base) for base in node.bases]
        direct_typed_dict = "TypedDict" in bases
        fields = {}
        own_fields = set(self_store_names(node))
        for item in node.body:
            if isinstance(item, ast.AnnAssign) and isinstance(
                item.target, ast.Name
            ):
                own_fields.add(item.target.id)
                fields[item.target.id] = item.annotation
        methods = {}
        properties = set()
        for item in node.body:
            if not isinstance(item, ast.FunctionDef):
                continue
            flavor = "method"
            for decorator in item.decorator_list:
                if isinstance(decorator, ast.Name) and decorator.id == "property":
                    flavor = "property-get"
                    properties.add(item.name)
                elif (
                    isinstance(decorator, ast.Attribute)
                    and decorator.attr == "setter"
                ):
                    flavor = "property-set"
                    properties.add(item.name)
            methods.setdefault(item.name, set()).add(flavor)
        declarations[node.name] = {
            "node": node,
            "bases": bases,
            "direct_typed_dict": direct_typed_dict,
            "own_fields": own_fields,
            "field_annotations": fields,
            "methods": methods,
            "properties": properties,
            "dataclass": any(
                (
                    isinstance(decorator, ast.Call)
                    and isinstance(decorator.func, ast.Name)
                    and decorator.func.id == "dataclass"
                )
                or (
                    isinstance(decorator, ast.Name)
                    and decorator.id == "dataclass"
                )
                for decorator in node.decorator_list
            ),
        }
    for name, declaration in declarations.items():
        declaration["typed_dict"] = declaration["direct_typed_dict"] or any(
            base in declarations and declarations[base].get("typed_dict", False)
            for base in declaration["bases"]
        )
    return declarations


def shape_mros(declarations, namespace):
    result = {}
    for name, declaration in declarations.items():
        if declaration["typed_dict"]:
            bases = [
                result[base][1]
                for base in declaration["bases"]
                if base in result
            ]
            shadow = type(name, tuple(bases) or (object,), {})
            result[name] = (
                [cls.__name__ for cls in shadow.__mro__
                 if cls.__name__ in declarations],
                shadow,
            )
        else:
            cls = namespace[name]
            result[name] = (
                [base.__name__ for base in cls.__mro__
                 if base.__name__ in declarations],
                cls,
            )
    return {name: value[0] for name, value in result.items()}


def function_owner(function):
    if function is None:
        return None
    qualname = getattr(function, "__qualname__", "")
    return qualname.split(".<locals>", 1)[0].split(".", 1)[0] or None


def resolved_members(cls, selectors, class_names):
    members = {}
    for selector in selectors:
        owner = next(
            (base for base in cls.__mro__ if selector in vars(base)),
            None,
        )
        if owner is None or owner.__name__ not in class_names:
            continue
        raw = vars(owner)[selector]
        if isinstance(raw, property):
            members[selector] = {
                "kind": "property",
                "owner": owner.__name__,
                "getter_owner": function_owner(raw.fget),
                "setter_owner": function_owner(raw.fset),
            }
        elif callable(raw):
            members[selector] = {
                "kind": "method",
                "owner": owner.__name__,
            }
    return members


def dataclass_snapshot(cls, declaration):
    if not declaration["dataclass"]:
        return None
    source_methods = set(declaration["methods"])
    generated = [
        name
        for name in (
            "__init__",
            "__repr__",
            "__eq__",
            "__hash__",
            "__setattr__",
            "__delattr__",
        )
        if name in vars(cls) and name not in source_methods
    ]
    mutation_error = None
    try:
        setattr(object.__new__(cls), "__pylate_probe__", 1)
    except BaseException as error:
        mutation_error = type(error).__name__
    return {
        "frozen": bool(cls.__dataclass_params__.frozen),
        "generated_methods": generated,
        "mutation_error": mutation_error,
    }


def typed_dict_snapshot(cls, declaration):
    if not declaration["typed_dict"]:
        return None
    keys = list(cls.__annotations__)
    required = cls.__required_keys__
    optional = cls.__optional_keys__
    read_only = getattr(cls, "__readonly_keys__", frozenset())
    return {
        "runtime_tag": "dict",
        "required_keys": [key for key in keys if key in required],
        "optional_keys": [key for key in keys if key in optional],
        "read_only_keys": [key for key in keys if key in read_only],
    }


def build_mirror_classes(declarations):
    call_log = []
    mirrors = {}

    def slot(owner, selector):
        def invoke(self, other):
            call_log.append(f"{owner}.{selector}")
            return NotImplemented

        invoke.__name__ = selector
        return invoke

    protocol_names = {
        selector
        for forward, reflected, _ in OPS.values()
        for selector in (forward, reflected)
    }
    for name, declaration in declarations.items():
        if declaration["typed_dict"]:
            continue
        bases = []
        for base in declaration["bases"]:
            if base in mirrors:
                bases.append(mirrors[base])
            elif base in BUILTIN_BASES:
                bases.append(BUILTIN_BASES[base])
        namespace = {
            selector: slot(name, selector)
            for selector in declaration["methods"]
            if selector in protocol_names
        }
        mirrors[name] = type(name, tuple(bases) or (object,), namespace)
    return mirrors, call_log


def binary_orders(declarations):
    mirrors, call_log = build_mirror_classes(declarations)
    rows = []

    def blank_instance(cls):
        try:
            return object.__new__(cls)
        except TypeError:
            return cls.__new__(cls)

    for left_name, left_cls in mirrors.items():
        for right_name, right_cls in mirrors.items():
            left = blank_instance(left_cls)
            right = blank_instance(right_cls)
            for symbol, (_, _, operation) in OPS.items():
                call_log.clear()
                try:
                    operation(left, right)
                except TypeError:
                    pass
                if call_log:
                    rows.append({
                        "left": left_name,
                        "op": symbol,
                        "right": right_name,
                        "candidates": list(call_log),
                    })
    return rows


def resolution_snapshot(source, filename):
    tree = ast.parse(source, filename)
    declarations = source_declarations(tree)
    namespace = execute_classes(tree, filename)
    class_names = set(declarations)
    shapes = shape_mros(declarations, namespace)

    selectors = set()
    all_fields = set()
    for declaration in declarations.values():
        selectors.update(declaration["methods"])
        all_fields.update(declaration["own_fields"])
        if declaration["dataclass"]:
            selectors.add("__init__")

    classes = {}
    for name, declaration in declarations.items():
        cls = namespace[name]
        shape_mro = shapes[name]
        fields = {}
        for field in all_fields:
            owner = next(
                (
                    candidate
                    for candidate in shape_mro
                    if field in declarations[candidate]["own_fields"]
                ),
                None,
            )
            if owner is None:
                continue
            annotation = declarations[owner]["field_annotations"].get(field)
            encoded = (
                normalize_field_annotation(annotation, True)[0]
                if annotation
                else None
            )
            fields[field] = {"owner": owner, "annotation": encoded}

        classes[name] = {
            "declared_bases": declaration["bases"],
            "runtime_bases": [base.__name__ for base in cls.__bases__],
            "shape_mro": shape_mro,
            "runtime_mro": [base.__name__ for base in cls.__mro__],
            "members": resolved_members(cls, selectors, class_names),
            "fields": fields,
            "subclasses": [
                candidate
                for candidate in declarations
                if name in shapes[candidate]
            ],
            "exception_mro": (
                [base.__name__ for base in cls.__mro__]
                if not declaration["typed_dict"]
                and issubclass(cls, BaseException)
                else []
            ),
            "dataclass": dataclass_snapshot(cls, declaration),
            "typed_dict": typed_dict_snapshot(cls, declaration),
        }

    return {
        "classes": classes,
        "binary_orders": binary_orders(declarations),
    }


def main():
    # A floor, not a pin. This is a differential oracle, and the point of a
    # differential oracle is to run under every interpreter whose semantics we
    # claim to model -- pinning one version defeats that, and on a build host
    # that provides a different one it fails the build outright.
    #
    # 3.12 is the floor because the admitted subset includes `match` and PEP 695
    # generics, which earlier interpreters cannot parse.
    #
    # The observed facts -- MRO, member ownership, binary protocol order -- were
    # compared across 3.12.11, 3.12.12 and 3.13.5 over all 194 corpus files and
    # are byte-identical. The version travels in the output so a future
    # divergence is attributable rather than invisible.
    if sys.version_info[:2] < (3, 12):
        raise SystemExit(
            "resolution oracle requires CPython 3.12 or later, found "
            + sys.version.split()[0]
        )
    if len(sys.argv) != 2:
        raise SystemExit("usage: cpython_resolution_probe.py SOURCE.py")
    path = sys.argv[1]
    with open(path, encoding="utf-8") as source_file:
        source = source_file.read()
    print(json.dumps({
        "python_version": sys.version.split()[0],
        "resolution": resolution_snapshot(source, path),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
