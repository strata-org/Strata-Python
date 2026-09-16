import servicelib


def require_dict_equal_deep_bad() -> bool:
    client = servicelib.connect("storage")
    client.require_dict_equal(
        Left={"top": "v",
              "l1": {"tags": ["t1", "t2"],
                     "l2": {"l3a": "x", "l3b": "y"}}},
        Right={"l1": {"l2": {"l3b": "z", "l3a": "x"},
                      "tags": ["t1", "t2"]},
               "top": "v"})
    return True
