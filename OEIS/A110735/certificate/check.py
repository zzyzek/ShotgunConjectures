# A110735, n = 101: no number b1 1 b2 0 b3 1 b4 (digits b_i) is a multiple of 101.
print(all((b1*10**6 + 10**5 + b2*10**4 + b3*10**2 + 10 + b4) % 101 for b1 in range(10) for b2 in range(10)
          for b3 in range(10) for b4 in range(10)))
