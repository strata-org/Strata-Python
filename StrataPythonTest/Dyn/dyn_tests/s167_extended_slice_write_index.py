# Test: an extended slice write whose step's __index__ grows the list fits the slice to the grown list
class Two:
    def __index__(self):
        xs[0:0] = [0]
        return 2


xs = [1, 2, 3, 4]
xs[::Two()] = [7, 8, 9]
print(len(xs), xs[0], xs[1], xs[2], xs[4])
ys = [1, 2, 3, 4]


class Two2:
    def __index__(self):
        ys[0:0] = [0]
        return 2


try:
    ys[::Two2()] = [7, 8]
except ValueError as e:
    print("ValueError", e.args[0])
