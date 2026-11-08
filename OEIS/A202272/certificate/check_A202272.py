# Brute force A202272 to N and compare with the conjectured forms.
import sys, re
N = int(sys.argv[1])
def ok(n):
  s = str(n)
  nz = [int(c) for c in s if c != '0']
  sums = {0}
  for d in nz:
    sums |= {x+d for x in sums}
  sums.discard(0)
  if '0' in s: sums.add(0)
  return all(str(v) in s for v in sums)
pat = re.compile(r'^([0-9]0*|10(0*90*)|90*100*)$')
bad = 0; cnt = 0
for n in range(N):
  a = ok(n); b = bool(pat.match(str(n)))
  if a: cnt += 1
  if a != b:
    bad += 1; print("mismatch", n, a, b)
print("N", N, "terms", cnt, "mismatches", bad)
