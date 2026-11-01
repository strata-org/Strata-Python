# Test: print raises TypeError for an unknown keyword before it reads flush
print(1, bad=1, flush=True)
