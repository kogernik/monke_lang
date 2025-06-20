import time

def fib(n):
    if n <= 1:
        return n
    else:
        return fib(n - 1) + fib(n - 2)

n = 35

start_time = time.time()
result = fib(n)
elapsed = time.time() - start_time

print(f"fib({n}) = {result}")
print(f"elapsed: {elapsed:.6f} secs")

