# NT-F19.1 recheck: n with no two different partitions n = a+b+c having the
# same product abc, (i) distinct parts 0<a<b<c, (ii) 0<a<=b<=c.
# Also verifies the family for 865 <= n <= 20000 (symbolic identity in README).
#
def fails(N, strict):
  out = []
  for n in range(3, N+1):
    seen, ok = set(), False
    for a in range(1, n):
      for b in range(a + (1 if strict else 0), n):
        c = n - a - b
        if c < b + (1 if strict else 0): break
        p = a*b*c
        if p in seen: ok = True; break
        seen.add(p)
      if ok: break
    if not ok: out.append(n)
  return out
print("distinct parts, failures n <= 1500:", fails(1500, True))
print("a<=b<=c, failures n <= 1500:", fails(1500, False))
def fam(n):
  for s in range(19):
    for w in range(19):
      if (n - 4*s - 5*w) % 19 == 0 and (n - 4*s - 5*w)//19 >= 37:
        t = (n - 4*s - 5*w)//19
        return (2*t+2*s, 8*t+2*s+2*w, 9*t+3*w), (3*t+3*s, 4*t+s+w, 12*t+4*w)
for n in range(865, 20001):
  A, B = fam(n)
  assert sum(A) == n == sum(B) and A[0]*A[1]*A[2] == B[0]*B[1]*B[2] and A != B
  assert 0 < A[0] < A[1] < A[2] and 0 < B[0] < B[1] < B[2]
print("family ok 865..20000")
