import numpy as np, sys, time

# Streams 1 GiB copies until killed: one DRAM-bandwidth hog per process.
a = np.ones(1 << 27)
b = np.empty_like(a)
end = time.time() + float(sys.argv[1])
while time.time() < end:
    np.copyto(b, a)
    np.copyto(a, b)
