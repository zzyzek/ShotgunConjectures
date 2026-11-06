#!/usr/bin/env python3
#
# Check for OEIS A094913: a(n) = max over binary words w of length n of
# the number of distinct nonempty factors of w, and A006697(n) - 1.
#
# 1. Brute force a(n) for n <= 16 equals sum_{i=1..n} min(2^i, n-i+1)
#    (Flaxman-Harrow-Sorkin 2004 Thm 8, bullets 1-2) and the printed terms.
# 2. The subword complexity of z = fixed point of a -> aab, b -> b
#    (the definition of A006697) equals sum_{i=0..n} min(2^i, n-i+1)
#    for n <= 16 (Allouche-Shallit 2016 Thm 1), read off the prefix of
#    length 2^17 (the run b^m first appears near position 2^(m+1), so a
#    prefix of length L only shows all factors of length about log2 L).
# 3. FHS Thm 8 bullet 3, (2^(k+1)-1) + C(n-k+1, 2) with k = floor(log2 n),
#    disagrees with the sum at some n; the script lists them for n <= 40.
#
# Run: nice -n 19 timeout 300 python3 check.py   (a few seconds)
#

from math import comb

PRINTED_A094913 = [0,1,3,5,8,12,16,21,27,34,42,50,59,69,80,92,105,119,134,150,166,183]
PRINTED_A006697 = [1,2,4,6,9,13,17,22,28,35,43,51,60,70,81,93,106,120,135,151,167,184]

def S(n, start):
  return sum(min(2**i, n-i+1) for i in range(start, n+1))

def brute(n):
  best = 0
  for x in range(2**n):
    w = format(x, f"0{n}b") if n else ""
    f = { w[i:j] for i in range(n) for j in range(i+1, n+1) }
    best = max(best, len(f))
  return best

ok = True
for n in range(17):
  ok &= (brute(n) == S(n, 1) == PRINTED_A094913[n])
print("brute force = FHS sum = printed A094913, n <= 16:", ok)

z = "a"
while len(z) < 2**17:
  z = "".join("aab" if c == "a" else "b" for c in z)
z = z[:2**17]
good = all( len({ z[i:i+n] for i in range(len(z)-n+1) }) == S(n, 0) for n in range(17) )
good &= all( S(n, 0) == PRINTED_A006697[n] for n in range(len(PRINTED_A006697)) )
good &= all( S(n, 0) - 1 == S(n, 1) for n in range(1000) )
print("complexity of z (2^17-letter prefix) = AS sum for n <= 16, printed A006697 match:", good)
ok &= good

bad = [ n for n in range(1, 41)
        if (2**(n.bit_length())-1) + comb(n-(n.bit_length()-1)+1, 2) != S(n, 0) ]
print("n <= 40 where FHS Thm 8 bullet-3 closed form (empty word included) differs:", bad)

print("ALL OK" if ok else "FAILED")
