import servicelib

# Regression test for evalIfValue (Issue #812).
# Symbolic bucket requires evalIfValue to compile the regex precondition.

def store_with_symbolic_bucket(bucket: str) -> bool:
    if bucket == "my-bucket":
        client = servicelib.connect("storage")
        client.put_item(Bucket=bucket, Key="mykey", Data="hello")
    return True
