# Leaves a read-only and an unreadable directory, each with a nested one and files, in its working
# directory, for TraceCleanupTest.lean.
import os
for d, mode in (("ro", 0o500), ("nr", 0o000)):
    os.makedirs(d + "/inner")
    for f in (d + "/f", d + "/inner/f"):
        with open(f, "w") as out:
            out.write("x")
    os.chmod(d + "/inner", mode)
    os.chmod(d, mode)
print("done")
