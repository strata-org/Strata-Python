import os

i = 1
output_dir = "output"
while os.path.exists(os.path.join(output_dir, str(i))):
    i = i + 1

print(i)
