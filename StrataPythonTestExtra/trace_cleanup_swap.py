# Replaces its working directory with a symlink that points nowhere, for TraceCleanupTest.lean.
import os
d = os.getcwd()
os.chdir("/")
os.rmdir(d)
os.symlink(d + "-nowhere", d)
print("done")
