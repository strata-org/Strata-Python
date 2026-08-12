state: int = 0


class Setter:
    async def set_state(self):
        global state
        state = 1
