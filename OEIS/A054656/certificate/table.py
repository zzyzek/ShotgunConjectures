# Base table for the Lean proof of A054656: for each m <= 87 a short list of
# representations of m as sums of distinct primes (parts < max(31, m-27)
# when m > 27) such that every prime in the first one is missed by some
# later one, except the listed exceptional pairs.
import itertools
def isp(n): return n > 1 and all(n % d for d in range(2, int(n**.5)+1))
def reps(m, bound):
  ps = [q for q in range(2, bound) if isp(q)]
  out = []
  def go(i, rem, cur):
    if rem == 0: out.append(sorted(cur)); return
    if i < 0: return
    if ps[i] <= rem: go(i-1, rem-ps[i], cur+[ps[i]])
    go(i-1, rem, cur)
  go(len(ps)-1, m, [])
  return out
EXC = {2:[2],3:[3],8:[3,5],9:[2,7],10:[3],11:[11],12:[7]}
tab = []
for m in range(0, 88):
  if m in (1, 4, 6): tab.append([]); continue
  bound = max(31, m-27) if m > 27 else m+1
  rs = sorted(reps(m, bound), key=len)
  found = None
  for k in (1, 2, 3, 4):
    for c in itertools.combinations(rs, k):
      inter = set(c[0]).intersection(*map(set, c))
      if sorted(inter) == (EXC.get(m, []) if m <= 27 else []):
        found = list(c); break
    if found: break
  assert found, m
  tab.append(found)
print(tab)
print(max(len(t) for t in tab))
