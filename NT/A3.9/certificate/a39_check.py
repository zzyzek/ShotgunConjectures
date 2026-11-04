# NT-A3.9 recheck: p(k) = least prime with decimal digit sum k, k < 180.
# Numbers of a fixed length with digit sum k are generated in increasing
# order (most significant digit first, smallest digit first).
#
import sys; sys.path.insert(0, '.')
from mr import is_prime
def gen(L, k):
  def rec(pos, rem, first):
    if pos == L:
      if rem == 0: yield 0
      return
    for d in range(1 if first else 0, 10):
      r = rem - d
      if 0 <= r <= 9*(L-pos-1):
        for t in rec(pos+1, r, False): yield d*10**(L-pos-1) + t
  return rec(0, k, True)
def p(k):
  L = (k+8)//9
  while True:
    for n in gen(L, k):
      if is_prime(n): return n
    L += 1
bad = []
for k in range(2, 180):
  if k % 3 == 0: continue
  q = p(k)
  if k > 25 and q % 10 != 9: bad.append((k, 10, q))
  if k > 38 and q % 100 != 99: bad.append((k, 100, q))
  if k > 59 and q % 1000 != 999: bad.append((k, 1000, q))
print("violations:", bad)
print("candidates below p(86) with digit sum 86:", [n for n in gen(10, 86) if n < p(86)])
