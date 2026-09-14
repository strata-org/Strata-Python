/-
The core semantic parameter tables (REQUIREMENTS.md section 2):
dir()-derived method ground truth per builtin type (the three-way
policy's 'known' set) and the modeled builtin callables.
-/
import Pylate.Domains.Value

namespace Pylate

/-- Every non-dunder method the builtin type really has (dir()-derived,
    CPython 3.13). A call outside this list is a true AttributeError; a
    call inside it that the table below does not model is an opaque call:
    result any, receiver edges havocked, obligation emitted. -/
def knownMethods : Tag → List String
  | .tlist => ["append", "clear", "copy", "count", "extend", "index",
               "insert", "pop", "remove", "reverse", "sort"]
  | .tdict => ["clear", "copy", "fromkeys", "get", "items", "keys", "pop",
               "popitem", "setdefault", "update", "values"]
  | .tdictkeys | .tdictitems | .tdictvalues => []
  | .tset => ["add", "clear", "copy", "difference", "difference_update",
              "discard", "intersection", "intersection_update",
              "isdisjoint", "issubset", "issuperset", "pop", "remove",
              "symmetric_difference", "symmetric_difference_update",
              "union", "update"]
  | .ttuple => ["count", "index"]
  | .trange => ["count", "index"]
  | .tgen => ["close", "send", "throw"]
  | .tstr => ["capitalize", "casefold", "center", "count", "encode",
              "endswith", "expandtabs", "find", "format", "format_map",
              "index", "isalnum", "isalpha", "isascii", "isdecimal",
              "isdigit", "isidentifier", "islower", "isnumeric",
              "isprintable", "isspace", "istitle", "isupper", "join",
              "ljust", "lower", "lstrip", "maketrans", "partition",
              "removeprefix", "removesuffix", "replace", "rfind",
              "rindex", "rjust", "rpartition", "rsplit", "rstrip",
              "split", "splitlines", "startswith", "strip", "swapcase",
              "title", "translate", "upper", "zfill"]
  -- The bytes surface is real but unmodeled: listing it here routes an
  -- unmodeled call through the widening path instead of claiming
  -- AttributeError, which would delete a completion CPython performs.
  | .tbytes => ["capitalize", "center", "count", "decode", "endswith",
                "expandtabs", "find", "fromhex", "hex", "index", "isalnum", "isalpha",
                "isascii", "isdigit", "islower", "isspace", "istitle",
                "isupper", "join", "ljust", "lower", "lstrip", "maketrans", "partition",
                "removeprefix", "removesuffix", "replace", "rfind", "rindex",
                "rjust", "rpartition", "rsplit", "rstrip", "split",
                "splitlines", "startswith", "strip", "swapcase", "title",
                "translate", "upper", "zfill"]
  | _ => []

def builtinFuncs : List String :=
  ["len", "range", "print", "isinstance", "next", "iter", "str", "repr",
   "list", "dict", "set", "tuple"]

def builtinTypeNames : List String :=
  ["object", "type", "bool", "int", "float", "complex", "str", "list",
   "dict", "set", "tuple", "range"]

-- ------------------------------------------------------------------ logs

end Pylate
