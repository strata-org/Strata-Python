def read_flag() -> int:
    try:
        return 1
    finally:
        print("cleanup")


read_flag()
