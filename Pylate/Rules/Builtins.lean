/-
rules for the builtin leaf surface.

Protocol-sensitive operations remain behind Services; these plans own the
ordered leaf transfers and construction effects that need no class-table
inspection.
-/
import Pylate.RuleLang.Dispatch

namespace Pylate.RuleDriven

open Pylate

private def positional (name : String) (required : Bool := true) : Parameter :=
  ⟨name, .positionalOnly, required⟩

private def keywordOnly (name : String) (required : Bool := true) : Parameter :=
  ⟨name, .keywordOnly, required⟩

private def receiver : ValueExpr := .read .receiver
private def parameter (name : String) : ValueExpr := .read (.parameter name)

private def methodRuleWith (tag : Tag) (name : String)
    (signature : Signature) (body : Plan)
    (contracts : List (String × ArgContract) := []) : Rule :=
  { key := .method tag name
    callable := { signature, body, contracts } }

private def methodRule (tag : Tag) (name : String)
    (parameters : List Parameter) (body : Plan)
    (contracts : List (String × ArgContract) := []) : Rule :=
  methodRuleWith tag name { parameters } body contracts

private def functionRuleWith (name : String) (signature : Signature)
    (body : Plan) (contracts : List (String × ArgContract) := []) : Rule :=
  { key := .function name
    callable := { signature, body, contracts } }

private def functionRule (name : String) (parameters : List Parameter)
    (body : Plan) (contracts : List (String × ArgContract) := []) : Rule :=
  functionRuleWith name { parameters } body contracts

/-- CPython's index conversion, used for every integral builtin argument. -/
private def index : ArgContract := .supportsIndex
private def str : ArgContract := .string
private def optionalStr : ArgContract := .optional .string

private def normalOrRaise (value : ValueExpr) (cls : String) : Plan :=
  .alternatives [
    .normal value,
    .raise (RaiseSpec.machine cls)
  ]

private def fresh (cls : LocCls)
    (initializers : List (CellSelector × ValueExpr) := []) : Plan :=
  .allocate cls initializers (.normal (.read (.local 0)))

private def invokeBuiltin (operation : Operation) : Plan :=
  .invoke { operation, forwardInput := true }
    (.normal (.read (.local 0)))

private def invokeDictMethod (method : DictMethod) : Plan :=
  .invoke {
      operation := .dictMethod method
      receiver := some receiver
      forwardInput := true
    } (.normal (.read (.local 0)))

private def opaqueMethodRuleBase (method : OpaqueBuiltinMethod)
    (signature : Signature) : Rule :=
  {
    key := .method method.receiver method.name
    callable := {
      signature
      body := .invoke {
          operation := .opaqueBuiltinMethod method
          receiver := some receiver
          forwardInput := true
        } (.normal (.read (.local 0)))
      isOpaque := true
    }
  }

private def opaqueMethodRule (method : OpaqueBuiltinMethod)
    (signature : Signature)
    (contracts : List (String × ArgContract) := []) : Rule :=
  let rule := opaqueMethodRuleBase method signature
  { rule with callable := { rule.callable with contracts } }

private def knownMethodRule (method : OpaqueBuiltinMethod)
    (signature : Signature)
    (contracts : List (String × ArgContract) := []) : Rule :=
  let rule := opaqueMethodRule method signature contracts
  { rule with callable := { rule.callable with isOpaque := false } }

def listAppendRule : Rule :=
  methodRule .tlist "append" [positional "object"]
    (.mutate (.grow receiver .list (.fixed .elem) (parameter "object"))
      (.normal .none))
    [("object", .any)]

/-- `insert` converts its index before it may mutate the list. -/
def listInsertRule : Rule :=
  methodRule .tlist "insert"
    [positional "index", positional "object"]
    (.mutate (.grow receiver .list (.fixed .elem) (parameter "object"))
      (.normal .none))
    [("index", index), ("object", .any)]

def listExtendRule : Rule :=
  methodRule .tlist "extend" [positional "iterable"]
    (.mutate
      (.grow receiver .list (.fixed .elem) (.elements (.parameter "iterable")))
      (.normal .none))
    [("iterable", .iterable)]

/-- An empty list always raises; a nonempty one raises only when an explicit
    index can be out of range. -/
def listPopRule : Rule :=
  methodRule .tlist "pop" [positional "index" false]
    (.branch (.definitelyEmpty receiver)
      (.raise (RaiseSpec.machine "IndexError"))
      (.branch (.definitelyNonempty receiver)
        (.branch (.supplied "index")
          (normalOrRaise (.elements .receiver) "IndexError")
          (.normal (.elements .receiver)))
        (normalOrRaise (.elements .receiver) "IndexError")))
    [("index", index)]

def listRemoveRule : Rule :=
  methodRule .tlist "remove" [positional "value"]
    (normalOrRaise .none "ValueError")
    [("value", .any)]

def listClearRule : Rule :=
  methodRule .tlist "clear" [] <|
    .mutate (.clear receiver .list (.fixed .elem)) (.normal .none)

def listCopyRule : Rule :=
  methodRule .tlist "copy" [] <|
    fresh .list [(.elem, .elements .receiver)]

def listCountRule : Rule :=
  methodRule .tlist "count" [positional "value"] (.normal .int)
    [("value", .any)]

def listIndexRule : Rule :=
  methodRule .tlist "index" [
      positional "value",
      positional "start" false,
      positional "stop" false
    ] (normalOrRaise .int "ValueError")
    [("value", .any), ("start", index), ("stop", index)]

def listSortRule : Rule :=
  methodRule .tlist "sort" [
      keywordOnly "key" false,
      keywordOnly "reverse" false
    ] (.normal .none)
    [("key", .optional .callableOrNone), ("reverse", .truthValue)]

def listReverseRule : Rule :=
  methodRule .tlist "reverse" [] (.normal .none)

def setAddRule : Rule :=
  methodRule .tset "add" [positional "element"]
    (.mutate (.grow receiver .set (.fixed .elem) (parameter "element"))
      (.normal .none))
    [("element", .hashable)]

def setDiscardRule : Rule :=
  methodRule .tset "discard" [positional "element"] (.normal .none)
    [("element", .setElement)]

def setRemoveRule : Rule :=
  methodRule .tset "remove" [positional "element"]
    (normalOrRaise .none "KeyError")
    [("element", .setElement)]

def setPopRule : Rule :=
  methodRule .tset "pop" []
    (.branch (.definitelyEmpty receiver)
      (.raise (RaiseSpec.machine "KeyError"))
      (.branch (.definitelyNonempty receiver)
        (.normal (.elements .receiver))
        (normalOrRaise (.elements .receiver) "KeyError")))

def setClearRule : Rule :=
  methodRule .tset "clear" [] <|
    .mutate (.clear receiver .set (.fixed .elem)) (.normal .none)

def setCopyRule : Rule :=
  methodRule .tset "copy" [] <|
    fresh .set [(.elem, .elements .receiver)]

private def variadicSetResultRule (name : String) : Rule :=
  { key := .method .tset name
    callable := {
      signature := { varPos := true }
      body := fresh .set [
        (.elem, .join (.elements .receiver) .argumentElements)
      ]
      variadic := some (.iterableOf .hashable)
    } }

def setUnionRule : Rule := variadicSetResultRule "union"
def setIntersectionRule : Rule := variadicSetResultRule "intersection"
def setDifferenceRule : Rule := variadicSetResultRule "difference"

def setSymmetricDifferenceRule : Rule :=
  methodRule .tset "symmetric_difference" [positional "other"]
    (fresh .set [
      (.elem, .join (.elements .receiver)
        (.elements (.parameter "other")))
    ])
    [("other", .iterableOf .hashable)]

/-- Removal keeps a sound over-approximation of the element summary and gives
    up cardinality: the receiver may end up empty. -/
private def setRemovalUpdateRule (name : String) : Rule :=
  { key := .method .tset name
    callable := {
      signature := { varPos := true }
      body := .mutate (.emptiness receiver .set .top) (.normal .none)
      variadic := some (.iterableOf .hashable)
    } }

def setDifferenceUpdateRule : Rule :=
  setRemovalUpdateRule "difference_update"

def setIntersectionUpdateRule : Rule :=
  setRemovalUpdateRule "intersection_update"

/-- The symmetric difference may add the operand's elements and may remove
    the receiver's, so the summary grows and cardinality is unknown. -/
def setSymmetricDifferenceUpdateRule : Rule :=
  methodRule .tset "symmetric_difference_update" [positional "other"]
    (.mutate (.grow receiver .set (.fixed .elem) (.elements (.parameter "other")))
      (.mutate (.emptiness receiver .set .top) (.normal .none)))
    [("other", .iterableOf .hashable)]

def setUpdateRule : Rule :=
  { key := .method .tset "update"
    callable := {
      signature := { varPos := true }
      body := .mutate (.grow receiver .set (.fixed .elem) .argumentElements)
        (.normal .none)
      variadic := some (.iterableOf .hashable)
    } }

private def setPredicateRule (name : String) : Rule :=
  methodRule .tset name [positional "other"] (.normal .bool)
    [("other", .iterableOf .hashable)]

def setIsSubsetRule : Rule := setPredicateRule "issubset"
def setIsSupersetRule : Rule := setPredicateRule "issuperset"
def setIsDisjointRule : Rule := setPredicateRule "isdisjoint"

private def countRule (tag : Tag) : Rule :=
  methodRule tag "count" [positional "value"] (.normal .int)
    [("value", .any)]

private def indexRule (tag : Tag) : Rule :=
  methodRule tag "index" [
      positional "value",
      positional "start" false,
      positional "stop" false
    ] (normalOrRaise .int "ValueError")
    [("value", .any), ("start", index), ("stop", index)]

def tupleCountRule : Rule := countRule .ttuple
def tupleIndexRule : Rule := indexRule .ttuple
def rangeCountRule : Rule := countRule .trange
def rangeIndexRule : Rule :=
  methodRule .trange "index" [positional "value"]
    (normalOrRaise .int "ValueError")
    [("value", .any)]

private def dictMethodRule (method : DictMethod) (signature : Signature)
    (contracts : List (String × ArgContract) := []) : Rule :=
  methodRuleWith .tdict method.name signature (invokeDictMethod method)
    contracts

def dictGetRule : Rule :=
  dictMethodRule .get {
    parameters := [positional "key", positional "default" false]
  } [("key", .hashable), ("default", .any)]

def dictPopRule : Rule :=
  dictMethodRule .pop {
    parameters := [positional "key", positional "default" false]
  } [("key", .hashable), ("default", .any)]

def dictKeysRule : Rule := dictMethodRule .keys {}
def dictValuesRule : Rule := dictMethodRule .values {}
def dictItemsRule : Rule := dictMethodRule .items {}

def dictSetdefaultRule : Rule :=
  dictMethodRule .setdefault {
    parameters := [positional "key", positional "default" false]
  } [("key", .hashable), ("default", .any)]

def dictUpdateRule : Rule :=
  dictMethodRule .update {
    parameters := [positional "mapping" false]
    varKw := true
  } [("mapping", .mappingPairsInto)]

def dictCopyRule : Rule := dictMethodRule .copy {}

def dictFromkeysRule : Rule :=
  dictMethodRule .fromkeys {
    parameters := [positional "iterable", positional "value" false]
  } [("iterable", .iterable), ("value", .any)]

def dictClearRule : Rule := dictMethodRule .clear {}

/-- `str.translate` looks the table up per character. The lookup hook carries
    its own exceptions; an unusable replacement is a TypeError. -/
def strTranslateRule : Rule :=
  methodRule .tstr "translate" [positional "table"]
    (.alternatives [
      .normal .str,
      .raise (RaiseSpec.machine "TypeError")
    ])
    [("table", .invokesHook "__getitem__")]

/-- Resuming a generator runs body code, so every outcome the body can produce
    stays possible: the next yielded value, exhaustion, or a body exception.
    The element summary stands in for the yielded value. -/
def genSendRule : Rule :=
  methodRule .tgen "send" [positional "value"]
    (.alternatives [
      .normal (.elements .receiver),
      .raise (RaiseSpec.machine "StopIteration"),
      .raise (RaiseSpec.machine "TypeError")
    ])
    [("value", .any)]

-- `close` is deliberately not rule data. Its outcomes include whatever the
-- analyzed generator's `finally` blocks raise, which is a property of the
-- program and not of the rule, so it is dispatched as a known method
-- (`KnownMethods.executeGeneratorClose`) where the tracked per-site generator
-- exceptions are reachable.

/-- `throw` injects an exception at the suspension point: the injected class
    propagates unless the body handles it, in which case the generator may
    yield again or finish. -/
def genThrowRule : Rule :=
  methodRule .tgen "throw" [
      positional "value",
      positional "traceback" false
    ]
    (.alternatives [
      .normal (.elements .receiver),
      .raise (RaiseSpec.ofOperand "value"),
      .raise (RaiseSpec.machine "StopIteration"),
      .raise (RaiseSpec.machine "RuntimeError"),
      .raise (RaiseSpec.machine "TypeError")
    ])
    [("value", .any), ("traceback", .any)]

/-- Replacement-field evaluation can fail on the format string itself, on a
    missing key or index, or in a `__format__` hook. -/
private def formatOutcomes : Plan :=
  .alternatives [
    .normal .str,
    .raise (RaiseSpec.machine "ValueError"),
    .raise (RaiseSpec.machine "KeyError"),
    .raise (RaiseSpec.machine "IndexError"),
    .raise (RaiseSpec.machine "TypeError"),
    .raise (RaiseSpec.machine "AttributeError")
  ]

/-- `encode` produces bytes. An unknown codec is a LookupError and an
    unencodable character a UnicodeEncodeError; neither can be ruled out
    without a codec and character-set domain. -/
def strFormatMapRule : Rule :=
  methodRule .tstr "format_map" [positional "mapping"] formatOutcomes
    [("mapping", .invokesHook "__getitem__")]

def strEncodeRule : Rule :=
  methodRule .tstr "encode" [
      positional "encoding" false,
      positional "errors" false
    ]
    (.alternatives [
      .normal .bytes,
      .raise (RaiseSpec.machine "LookupError"),
      .raise (RaiseSpec.machine "UnicodeEncodeError")
    ])
    [("encoding", str), ("errors", str)]

def opaqueBuiltinMethodRules : List Rule :=
  [
    knownMethodRule .dictPopitem {},

    -- `close` cannot be plan data: its outcomes include whatever the analyzed
    -- generator's `finally` blocks raise, which is a property of the program.
    -- Routed here so `KnownMethods.executeGeneratorClose` runs, where the
    -- tracked per-site generator exceptions are reachable.
    knownMethodRule .genClose {},


    knownMethodRule .strMaketrans (contracts :=
      [("x", .any), ("y", .any), ("z", .any)]) {
      parameters := [
        positional "x",
        positional "y" false,
        positional "z" false
      ]
    },
    knownMethodRule .strPartition {
      parameters := [positional "sep"]
    } [("sep", .separatorString .tstr)],
    knownMethodRule .strRpartition {
      parameters := [positional "sep"]
    } [("sep", .separatorString .tstr)],




  ]

private def stringZeroRule (name : String) (result : ValueExpr) : Rule :=
  methodRule .tstr name [] (.normal result)

private def stringOneRule (name parameterName : String)
    (result : ValueExpr)
    (contract : ArgContract := .string) : Rule :=
  methodRule .tstr name [positional parameterName] (.normal result)
    [(parameterName, contract)]

/-- `strip`/`lstrip`/`rstrip`: the separator set is absent, None, or a string. -/
private def stringCharsRule (name : String) : Rule :=
  methodRule .tstr name [positional "chars" false] (.normal .str)
    [("chars", optionalStr)]

/-- Search-with-bounds shape: a string needle and index-converted bounds. -/
private def stringBoundsRule (name needle : String)
    (result : ValueExpr) (needleContract : ArgContract := .string) : Rule :=
  methodRule .tstr name [
      positional needle,
      positional "start" false,
      positional "end" false
    ] (.normal result)
    [(needle, needleContract), ("start", index), ("end", index)]

private def stringBoundsRaiseRule (name : String) : Rule :=
  methodRule .tstr name [
      positional "sub",
      positional "start" false,
      positional "end" false
    ] (normalOrRaise .int "ValueError")
    [("sub", str), ("start", index), ("end", index)]

def stringRules : List Rule :=
  [
    stringZeroRule "upper" .str,
    stringZeroRule "lower" .str,
    stringCharsRule "strip",
    stringCharsRule "lstrip",
    stringCharsRule "rstrip",
    stringZeroRule "title" .str,
    stringZeroRule "capitalize" .str,
    stringZeroRule "casefold" .str,
    stringZeroRule "swapcase" .str,
    methodRule .tstr "replace" [
      positional "old",
      positional "new",
      positional "count" false
    ] (.normal .str)
      [("old", str), ("new", str), ("count", index)],
    stringOneRule "join" "iterable" .str (.iterableOf .string),
    { key := .method .tstr "format"
      callable := {
        signature := { varPos := true, varKw := true }
        body := formatOutcomes
        variadic := some (.invokesHook "__format__")
      } },
    stringOneRule "removeprefix" "prefix" .str,
    stringOneRule "removesuffix" "suffix" .str,
    methodRule .tstr "ljust"
      [positional "width", positional "fillchar" false] (.normal .str)
      [("width", index), ("fillchar", .fillCharacter)],
    methodRule .tstr "rjust"
      [positional "width", positional "fillchar" false] (.normal .str)
      [("width", index), ("fillchar", .fillCharacter)],
    methodRule .tstr "center"
      [positional "width", positional "fillchar" false] (.normal .str)
      [("width", index), ("fillchar", .fillCharacter)],
    stringOneRule "zfill" "width" .str index,
    methodRule .tstr "expandtabs" [positional "tabsize" false]
      (.normal .str) [("tabsize", index)],
    stringBoundsRule "startswith" "prefix" .bool .stringOrTupleOfStrings,
    stringBoundsRule "endswith" "suffix" .bool .stringOrTupleOfStrings,
    stringZeroRule "isalnum" .bool,
    stringZeroRule "isalpha" .bool,
    stringZeroRule "isascii" .bool,
    stringZeroRule "isdecimal" .bool,
    stringZeroRule "isdigit" .bool,
    stringZeroRule "isidentifier" .bool,
    stringZeroRule "islower" .bool,
    stringZeroRule "isnumeric" .bool,
    stringZeroRule "isprintable" .bool,
    stringZeroRule "isspace" .bool,
    stringZeroRule "istitle" .bool,
    stringZeroRule "isupper" .bool,
    stringBoundsRule "count" "sub" .int,
    stringBoundsRule "find" "sub" .int,
    stringBoundsRule "rfind" "sub" .int,
    stringBoundsRaiseRule "index",
    stringBoundsRaiseRule "rindex",
    methodRule .tstr "split"
      [positional "sep" false, positional "maxsplit" false]
      (fresh .list [(.elem, .str)])
      [("maxsplit", index), ("sep", .optional (.separatorString .tstr))],
    methodRule .tstr "rsplit"
      [positional "sep" false, positional "maxsplit" false]
      (fresh .list [(.elem, .str)])
      [("maxsplit", index), ("sep", .optional (.separatorString .tstr))],
    methodRule .tstr "splitlines" [positional "keepends" false]
      (fresh .list [(.elem, .str)])
      [("keepends", .truthValue)]
  ]

-- ------------------------------------------------------------------ bytes

/-- The `bytes` method surface. It was the whole of `unmodeled-surface`: 42 names
    reachable through `str.encode` with no rule, so every call widened to `any`.
    Sound, and precision left on the floor.

    Every result type and raise below was read out of CPython 3.13 rather than
    assumed to mirror `str`, because they do not mirror it everywhere: `decode`
    yields a `str` and can raise `UnicodeDecodeError`, `hex` yields a `str`, and
    `fromhex` and `maketrans` are static and raise `ValueError` on bad input.
    `tests/known_methods_oracle.py` keeps the name list honest; these rules make
    the names mean something. -/
private def bytesZeroRule (name : String) (result : ValueExpr) : Rule :=
  methodRule .tbytes name [] (.normal result)

private def bytesStripRule (name : String) : Rule :=
  methodRule .tbytes name [positional "chars" false] (.normal .bytes)
    [("chars", .optional .any)]

/-- Search with bounds. `index` and `rindex` raise where `find` and `rfind`
    return -1, which is the one asymmetry in this family. -/
private def bytesSearchRule (name : String) (raises : Bool) : Rule :=
  methodRule .tbytes name [
      positional "sub",
      positional "start" false,
      positional "end" false
    ] (if raises then normalOrRaise .int "ValueError" else .normal .int)
    [("sub", .any), ("start", index), ("end", index)]

private def bytesPadRule (name : String) : Rule :=
  methodRule .tbytes name [
      positional "width",
      positional "fillchar" false
    ] (.normal .bytes)
    [("width", index), ("fillchar", .optional .any)]

/-- An empty separator is a `ValueError` here too, so this takes the separator
    contract rather than `.any`, which had admitted only a normal completion. -/
private def bytesPartitionRule (name : String) : Rule :=
  methodRule .tbytes name [positional "sep"]
    (fresh .tuple [(.tupleSlot 0, .bytes), (.tupleSlot 1, .bytes),
                   (.tupleSlot 2, .bytes), (.elem, .bytes)])
    [("sep", .separatorString .tbytes)]

/-- An empty separator is a `ValueError`, which the separator contract states. -/
private def bytesSplitRule (name : String) : Rule :=
  methodRule .tbytes name
    [positional "sep" false, positional "maxsplit" false]
    (fresh .list [(.elem, .bytes)])
    [("sep", .optional (.separatorString .tbytes)), ("maxsplit", index)]

def bytesRules : List Rule :=
  [ bytesZeroRule "capitalize" .bytes,
    bytesZeroRule "lower" .bytes,
    bytesZeroRule "upper" .bytes,
    bytesZeroRule "title" .bytes,
    bytesZeroRule "swapcase" .bytes,
    bytesZeroRule "isalnum" .bool,
    bytesZeroRule "isalpha" .bool,
    bytesZeroRule "isascii" .bool,
    bytesZeroRule "isdigit" .bool,
    bytesZeroRule "islower" .bool,
    bytesZeroRule "isspace" .bool,
    bytesZeroRule "istitle" .bool,
    bytesZeroRule "isupper" .bool,
    bytesZeroRule "hex" .str,
    bytesStripRule "strip",
    bytesStripRule "lstrip",
    bytesStripRule "rstrip",
    bytesSearchRule "find" false,
    bytesSearchRule "rfind" false,
    bytesSearchRule "index" true,
    bytesSearchRule "rindex" true,
    bytesSearchRule "count" false,
    bytesPadRule "ljust",
    bytesPadRule "rjust",
    bytesPadRule "center",
    bytesPartitionRule "partition",
    bytesPartitionRule "rpartition",
    bytesSplitRule "split",
    bytesSplitRule "rsplit",
    methodRule .tbytes "splitlines" [positional "keepends" false]
      (fresh .list [(.elem, .bytes)])
      [("keepends", .truthValue)],
    methodRule .tbytes "zfill" [positional "width"] (.normal .bytes)
      [("width", index)],
    methodRule .tbytes "expandtabs" [positional "tabsize" false]
      (.normal .bytes) [("tabsize", index)],
    methodRule .tbytes "replace" [
        positional "old", positional "new", positional "count" false
      ] (.normal .bytes)
      [("old", .any), ("new", .any), ("count", index)],
    methodRule .tbytes "removeprefix" [positional "prefix"] (.normal .bytes)
      [("prefix", .any)],
    methodRule .tbytes "removesuffix" [positional "suffix"] (.normal .bytes)
      [("suffix", .any)],
    -- A str argument is a TypeError, which the contract reports.
    methodRule .tbytes "startswith" [
        positional "prefix", positional "start" false, positional "end" false
      ] (.normal .bool)
      [("prefix", .any), ("start", index), ("end", index)],
    methodRule .tbytes "endswith" [
        positional "suffix", positional "start" false, positional "end" false
      ] (.normal .bool)
      [("suffix", .any), ("start", index), ("end", index)],
    -- Decoding is the one that leaves the byte world, and it can fail on the
    -- bytes rather than on the arguments.
    methodRule .tbytes "decode" [
        positional "encoding" false, positional "errors" false
      ] (.alternatives [
          .normal .str,
          .raise (RaiseSpec.machine "UnicodeDecodeError"),
          .raise (RaiseSpec.machine "LookupError")
        ])
      [("encoding", optionalStr), ("errors", optionalStr)],
    methodRule .tbytes "join" [positional "iterable"]
      (normalOrRaise .bytes "TypeError") [("iterable", .any)],
    methodRule .tbytes "translate" [
        positional "table", positional "delete" false
      ] (.normal .bytes)
      [("table", .any), ("delete", .optional .any)],
    -- Static on the type, and both validate their input.
    methodRule .tbytes "fromhex" [positional "string"]
      (normalOrRaise .bytes "ValueError") [("string", .string)],
    methodRule .tbytes "maketrans" [positional "frm", positional "to"]
      (normalOrRaise .bytes "ValueError") [("frm", .any), ("to", .any)] ]

def lenRule : Rule :=
  functionRule "len" [positional "object"]
    (invokeBuiltin .builtinLen)
    [("object", .any)]

def strRule : Rule :=
  functionRule "str" [positional "object" false]
    (invokeBuiltin .builtinStr) [("object", .any)]

def reprRule : Rule :=
  functionRule "repr" [positional "object"]
    (invokeBuiltin .builtinRepr) [("object", .any)]

def printRule : Rule :=
  functionRuleWith "print" {
      parameters := [
        keywordOnly "sep" false,
        keywordOnly "end" false,
        keywordOnly "file" false,
        keywordOnly "flush" false
      ]
      varPos := true
    } (.normal .none)
    [("file", .invokesHook "write"), ("sep", optionalStr),
     ("end", optionalStr), ("flush", .truthValue)]

def isinstanceRule : Rule :=
  functionRule "isinstance"
    [positional "object", positional "classinfo"] (.normal .bool)
    [("object", .any), ("classinfo", .runtimeTags [.ttype, .tunion, .ttuple])]

def rangeRule : Rule :=
  functionRule "range" [
      positional "start",
      positional "stop" false,
      positional "step" false
    ] (.branch (.supplied "step")
        (.alternatives [
          fresh .range [(.elem, .int)],
          .raise (RaiseSpec.machine "ValueError")
        ])
        (fresh .range [(.elem, .int)]))
    [("start", index), ("stop", index), ("step", index)]

-- `iter`/`next` implement the protocol in their bodies, so their operands
-- carry no separate argument contract.
def iterRule : Rule :=
  functionRule "iter" [positional "iterable"]
    (invokeBuiltin .builtinIter)
    [("iterable", .any)]

def nextRule : Rule :=
  functionRule "next" [
      positional "iterator",
      positional "default" false
    ] (invokeBuiltin .builtinNext)
    [("iterator", .any), ("default", .any)]

private def collectionConstructorRule (name : String) (cls : LocCls) : Rule :=
  functionRule name [positional "iterable" false]
    (.allocate cls [(.elem, .elements (.parameter "iterable"))] <|
      .branch (.definitelyNonempty (parameter "iterable"))
        (.mutate (.emptiness (.read (.local 0)) cls .nonempty)
          (.normal (.read (.local 0))))
        (.normal (.read (.local 0))))
    [("iterable", .iterable)]

def listRule : Rule := collectionConstructorRule "list" .list
def tupleRule : Rule := collectionConstructorRule "tuple" .tuple

def setRule : Rule :=
  functionRule "set" [positional "iterable" false]
    (.require (.hashable (.elements (.parameter "iterable")))
      (RaiseSpec.machine "TypeError")
      (.allocate .set [(.elem, .elements (.parameter "iterable"))] <|
        .branch (.definitelyNonempty (parameter "iterable"))
          (.mutate (.emptiness (.read (.local 0)) .set .nonempty)
            (.normal (.read (.local 0))))
          (.normal (.read (.local 0)))))
    [("iterable", .iterable)]

/-- `dict(source)` is the destination the mapping-pairs contract populated;
    without a source it is a fresh empty dict. -/
def dictRule : Rule :=
  functionRuleWith "dict" {
      parameters := [positional "mapping" false]
      varKw := true
    } (.branch (.supplied "mapping")
        (.normal (.read (.parameter "mapping")))
        (fresh .dict))
    [("mapping", .mappingOrIterablePairs)]

def foundationRuleSet : RuleSet :=
  { rules := [
      listAppendRule,
      listClearRule,
      listCopyRule,
      listPopRule,
      setAddRule
    ] }

theorem foundationRuleSetCompiles :
    (compileRules foundationRuleSet).toOption.isSome = true := by
  native_decide

-- The theorem above proves this set validates; the table is built without
-- re-deriving that in every process.
def compiledFoundationRules : CompiledRules := buildTable foundationRuleSet

def builtinRuleSet : RuleSet :=
  { rules :=
    [
      listAppendRule,
      listInsertRule,
      listExtendRule,
      listPopRule,
      listRemoveRule,
      listClearRule,
      listCopyRule,
      listCountRule,
      listIndexRule,
      listSortRule,
      listReverseRule,
      setAddRule,
      setDiscardRule,
      setRemoveRule,
      setPopRule,
      setClearRule,
      setCopyRule,
      setUnionRule,
      setIntersectionRule,
      setDifferenceRule,
      setSymmetricDifferenceRule,
      setUpdateRule,
      setDifferenceUpdateRule,
      setIntersectionUpdateRule,
      setSymmetricDifferenceUpdateRule,
      strEncodeRule,
      strFormatMapRule,
      strTranslateRule,
      genSendRule,
      genThrowRule,
      setIsSubsetRule,
      setIsSupersetRule,
      setIsDisjointRule,
      tupleCountRule,
      tupleIndexRule,
      rangeCountRule,
      rangeIndexRule,
      dictGetRule,
      dictPopRule,
      dictKeysRule,
      dictValuesRule,
      dictItemsRule,
      dictSetdefaultRule,
      dictUpdateRule,
      dictCopyRule,
      dictFromkeysRule,
      dictClearRule,
      lenRule,
      strRule,
      reprRule,
      printRule,
      isinstanceRule,
      rangeRule,
      iterRule,
      nextRule,
      listRule,
      tupleRule,
      setRule,
      dictRule
    ] ++ stringRules ++ bytesRules ++ opaqueBuiltinMethodRules }

/-- The rule set compiles. Checked at build time, so an invalid rule can never
    degrade the engine to a smaller or empty rule database at run time. -/
theorem builtinRuleSetCompiles :
    (compileRules builtinRuleSet).toOption.isSome = true := by
  native_decide

def compiledBuiltinRules : CompiledRules := buildTable builtinRuleSet

/-- Every declared rule is present: a silently shrinking database is as bad as
    an empty one. -/
theorem builtinRulesComplete :
    compiledBuiltinRules.entries.length = builtinRuleSet.rules.length := by
  native_decide

def initialLiveRuleSet : RuleSet := builtinRuleSet

def compiledInitialLiveRules : CompiledRules := compiledBuiltinRules

end Pylate.RuleDriven
