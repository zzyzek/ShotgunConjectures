# NT-F6.2 recheck: for each pattern, (a) chi_{-4}(odd part) avoids it, or
# (b) for the prime q every translate t + pattern (mod q) contains a nonzero
# quadratic nonresidue class mod q.
#
def chi4odd(n):
  while n % 2 == 0: n //= 2
  return 1 if n % 4 == 1 else -1
def chi_ok(pat, R=20000):
  return all(any(chi4odd(r+s) == -1 for s in pat) for r in range(1, R))
def leg_ok(pat, q):
  qr = {(x*x) % q for x in range(1, q)}
  nr = set(range(1, q)) - qr
  return all(any((t+s) % q in nr for s in pat) for t in range(q))
pats = {(0,1,6,7): None, (0,1,6,10): None, (0,1,7,10): None, (0,5,6,9): None, (0,6,7,10): None}
for p in pats:
  print(p, "chi_-4:", chi_ok(p), "primes q<60 that work:", [q for q in [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59] if leg_ok(p, q)])
