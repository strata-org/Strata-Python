# Case 04 module target cleanup
import json as deleted_module
import json as preserved_module


class E(Exception):
    pass


target = "pre-existing"
try:
    raise E("caught")
except E as target:
    pass

try:
    target
except NameError:
    target_result = "NameError"
else:
    target_result = "still bound"


len = "module shadow"
try:
    raise E("caught")
except E as len:
    pass

builtin_fallback_result = len([1, 2, 3])


try:
    raise E("caught")
except E as deleted_module:
    pass

try:
    deleted_module.dumps({"bad": True})
except NameError:
    deleted_import_result = "NameError"
else:
    deleted_import_result = "still bound"

preserved_import_result = preserved_module.dumps({"ok": True}, sort_keys=True)

RESULT = (
    target_result,
    builtin_fallback_result,
    deleted_import_result,
    preserved_import_result,
)
