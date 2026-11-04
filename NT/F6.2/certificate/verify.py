# Rigorous check of the prime-modulus obstructions: for prime q, if every
# translate t+S (S = {0} u pat, mod q) contains a nonzero quadratic
# nonresidue class, then f(n) = (n/q) on n coprime to q, any f(q), has
# f = -1 somewhere on r+S for every r: the element in that class is
# coprime to q and a nonresidue.  The mod-4 case is argued in the note.
#
pats = [(1, 6, 7), (1, 6, 10), (1, 7, 10), (5, 6, 9), (6, 7, 10)]
for pat in pats:
  ok = []
  for q in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
    R = {(x * x) % q for x in range(1, q)}
    S = [0] + [p % q for p in pat]
    if all(any((s + t) % q != 0 and (s + t) % q not in R for s in S) for t in range(q)):
      ok.append(q)
  print(pat, "prime obstructions q =", ok)
