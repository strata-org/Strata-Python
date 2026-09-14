def guard(k):
    try:
        return 10 // k
    except (ValueError, KeyError):
        return 0
