# A113610: a(n) = digit sum of all composites strictly between prime(n) and prime(n+1).
# Local minima a(n) > a(n+1) < a(n+2), n > 9, where prime(n), prime(n+1) (literal reading)
# or prime(n+1), prime(n+2) (variant) are not twin primes.  Primes < 10^5.
from sympy import primerange
P = list(primerange(2, 10**5)); P = [None] + P
ds = lambda x: sum(map(int, str(x)))
a = [None] + [sum(ds(x) for x in range(P[n] + 1, P[n+1])) for n in range(1, len(P) - 1)]
lit = [n for n in range(10, len(a) - 2) if a[n] > a[n+1] < a[n+2] and P[n+1] - P[n] != 2]
var = [n for n in range(10, len(a) - 2) if a[n] > a[n+1] < a[n+2] and P[n+2] - P[n+1] != 2]
print("literal failures:", len(lit), lit[:5], " variant failures:", len(var), var[:5])
print("a(12..14) =", a[12:15], " primes", P[12:15], "; a(21..23) =", a[21:24], " primes", P[21:24])
