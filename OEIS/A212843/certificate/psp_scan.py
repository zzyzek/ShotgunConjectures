# Feitsma-Galway base-2 pseudoprimes < 1e13 (with factors, Carmichael flag):
# A212843 (prime-factor residues mod 30), A214305 (Poulet residue claims).
#
import sys
path = sys.argv[1]
twofac = {}
c11 = []
bad1 = []
bad214305_any = []
cnt = 0
with open(path) as f:
  for line in f:
    t = line.split()
    if not t: continue
    carm = (t[0] == 'C')
    if carm: t = t[1:]
    if not t[0].isdigit(): continue
    n = int(t[0]); ps = [int(x) for x in t[1:]]
    if carm:
      cnt += 1
      if any(p % 10 == 1 for p in ps) and n % 10 != 1: bad1.append(n)
      if all(p % 10 == 1 for p in ps):
        r11 = sum(1 for p in ps if p % 30 == 11)
        r1 = sum(1 for p in ps if p % 30 == 1)
        if r1 == 0 and r11 % 2 == 1 and r11 >= 5: c11.append((n, ps))
    if n < 10**7:
      if len(ps) == 2 and ps[0] != ps[1]:
        twofac[n] = ps
      # Conjecture 2 of A214305: p2 divisible by d, p1 < p2 two-factor Poulet with d | p1.
      for d in set(ps):
        for p1, f1 in twofac.items():
          if p1 < n and d in f1 and d == max(f1):
            if (n - d) % (p1 - d) != 0:
              bad214305_any.append((n, ps, p1, f1, d))
print("Carmichael numbers scanned:", cnt)
print("A212843 part 1 violations:", bad1[:5])
print("A212843: Carmichael with all primes = 11 mod 30, odd count >= 5:", len(c11), c11[:5])
print("A214305 conj 2 (d = largest factor of p1) violations, first 5:", bad214305_any[:5])
