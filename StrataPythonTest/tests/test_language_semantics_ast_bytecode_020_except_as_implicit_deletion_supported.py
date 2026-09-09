# as-variable deleted — use it inside handler only
def safe_divide(a, b):
    try:
        return a / b
    except ZeroDivisionError as e:
        msg = str(e)  # capture before deletion
    return f"Error: {msg}"
assert safe_divide(1, 0) == "Error: division by zero"
print("OK: except-as — variable usable inside handler")
