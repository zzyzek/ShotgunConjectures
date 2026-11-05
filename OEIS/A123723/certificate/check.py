# Brute-force check of the A123722 / A123723 classifications for n < LIMIT.
# S(n) = number of squares mod n (A000224). Prints the first terms and any violation.
import sys
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
def S(n): return len({x * x % n for x in range(n)})
def isprime(m): return m > 1 and all(m % d for d in range(2, int(m ** 0.5) + 1))
for k in (3, 4):
    seq = [n for n in range(1, LIMIT) if S(n) == n // k + 1]
    print("k =", k, "first terms:", seq[:22])
    bad = [n for n in seq if n % k == 0 and n != k and not isprime(n // k)]
    print("  multiples of k (other than k) with n/k not prime:", bad)
    if k == 3:
        miss = [p for p in range(3, LIMIT // 3) if isprime(p) and 3 * p not in set(seq)]
        print("  odd primes p < LIMIT/3 with 3p missing:", miss)
