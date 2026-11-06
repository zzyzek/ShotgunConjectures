# The predicted denominator-3 set {n : 2n+1 = 3 m^2, every prime p != 3 dividing m is 2 mod 3}
# against the whole A166101 b-file.
import sys
def factor(m):
  f = set(); p = 2
  while p * p <= m:
    while m % p == 0: f.add(p); m //= p
    p += 1
  if m > 1: f.add(m)
  return f
b = [int(l.split()[1]) for l in open("b166101.txt") if l.strip() and not l.startswith("#")]
top = max(b); pred = []
m = 1
while 3 * m * m <= 2 * top + 1:
  if m % 2 == 1 and all((p == 3) or (p % 3 == 2) for p in factor(m)):
    pred.append((3 * m * m - 1) // 2)
  m += 1
ok = (pred == b)
print("b-file terms", len(b), "max", top, "match", ok)
sys.exit(0 if ok else 1)
