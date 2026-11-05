# Empirical moment-based (Markov) bounds: fraction of odd m with
# sigma(m)/m >= 2, versus the true fraction; and fraction of m coprime
# to 6 with sigma(m)/m < 4/3 (gives even deficient 2m).
#
import sys
N = int(sys.argv[1])
s = [0]*(N+1)
for d in range(1, N+1):
  for m in range(d, N+1, d):
    s[m] += d
odd = [s[m]/m for m in range(1, N+1, 2)]
for k in range(1, 7):
  mk = sum(r**k for r in odd)/len(odd)
  print("k", k, "E_odd[r^k]", round(mk, 4), "Markov bound P(r>=2)", round(mk/2**k, 4))
print("true odd abundant frac", sum(1 for r in odd if r > 2)/len(odd))
c6 = [s[m]/m for m in range(1, N+1) if (m % 6) in (1, 5)]
print("frac m coprime 6 with r<4/3", sum(1 for r in c6 if r < 4/3)/len(c6))
