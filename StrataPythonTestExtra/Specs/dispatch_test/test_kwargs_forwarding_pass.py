import servicelib


def kwargs_forwarding_pass() -> bool:
    client = servicelib.connect("storage")
    params: dict[str, str] = {
        "Bucket": "mybucket",
        "Key": "mykey",
    }
    client.put_with_explicit_bucket(**params)
    return True
