# A079665: (b^s+1)/(b^r+1), 1 <= r < s, is an integer iff r | s and s/r odd,
# iff the conjecture's conditions hold.  Checks b = 2..12, s <= 60.
#
def v2(n):
  t = 0
  while n % 2 == 0: n //= 2; t += 1
  return t
def conj(r, s):
  t = v2(s); k = s >> t
  c1 = 2*r < s
  c2 = (s % 2 == 0) or (s % r == 0)
  c3 = (r % (2**t) == 0) and (k % (r >> t) == 0) and v2(r) == t
  return c1 and c2 and c3
ok = all(((b**s + 1) % (b**r + 1) == 0) == (s % r == 0 and (s//r) % 2 == 1) == conj(r, s)
         for b in range(2, 13) for s in range(2, 61) for r in range(1, s))
print("all agree:", ok)
