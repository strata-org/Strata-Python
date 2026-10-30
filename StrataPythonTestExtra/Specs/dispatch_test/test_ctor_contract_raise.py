from servicelib.CtorError import ClientError


def raise_client_error(flag: bool) -> None:
    if flag:
        raise ClientError("resp", "op")
