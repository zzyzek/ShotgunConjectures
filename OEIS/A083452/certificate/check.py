# A083452: n concatenated n times exceeds n^n for n > 1.  n < 1000.
print(all(int(str(n) * n) > n**n for n in range(2, 1000)))
