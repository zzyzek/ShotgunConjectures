# NT-F31.2 recheck.  m and k m both have balanced-ternary digits in {+1,-1}.
# Reading the product k m from the least significant digit: carry c, digit
# e of m, digit f of k m, with c + k e = f + 3 c'.  T = carries reachable
# from 0 after at least one step; D = carries that are not the value of any
# (possibly empty) +-1 digit string.  No m exists iff T is a subset of D
# (carries stay in [-(k+1)/2, (k+1)/2]).
#
def rep(c):
  # c is the value of a +-1 digit string (the empty string gives 0)
  while c != 0:
    r = c % 3
    if r == 0: return False
    c = (c - (1 if r == 1 else -1)) // 3
  return True
def reach(k):
  seen, fr = set(), [0]
  while fr:
    nf = []
    for c in fr:
      for e in (1, -1):
        for f in (1, -1):
          v = c + k*e - f
          if v % 3 == 0 and (v//3) not in seen:
            seen.add(v//3); nf.append(v//3)
    fr = nf
  return seen
def exists(k): return any(rep(c) for c in reach(k))
T = sorted(reach(247))
print("k=247: |T| =", len(T), "min", T[0], "max", T[-1], "any representable:", any(rep(c) for c in T))
print("T =", T)
bad = [k for k in range(1, 3000) if k % 3 != 0 and not exists(k)]
print("failing k < 3000:", bad)
