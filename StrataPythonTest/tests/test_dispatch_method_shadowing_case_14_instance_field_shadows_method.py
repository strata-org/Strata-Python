"""A plain function is a non-data descriptor and can be shadowed."""


class Worker:
    def run(self):
        return "class-method"


worker = Worker()
unshadowed = worker.run()
worker.run = lambda: "instance-callable"

RESULT = (unshadowed, worker.run(), Worker.run(worker))
