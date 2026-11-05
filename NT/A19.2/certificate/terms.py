# Recompute OEIS A091155: n such that n - 2^k is squarefree
# for every k >= 0 with 2^k < n (n >= 2; n = 1 holds vacuously and
# OEIS starts at 2). Compare with the published terms.
#
import sys

PUBLISHED = [2, 3, 4, 7, 15, 23, 39, 63, 75, 87, 111, 135, 147, 159, 195,
  219, 231, 255, 267, 315, 387, 399, 411, 423, 435, 447, 459, 495, 519, 567,
  615, 663, 675, 699, 711, 735, 747, 759, 771, 819, 867, 915, 999, 1011,
  1023, 1035, 1047, 1071, 1095, 1119, 1155, 1167, 1263]

# Sieve of squarefree flags up to N.
#
def squarefree_flags(N):
  sf = [True] * (N + 1)
  sf[0] = False
  d = 2
  while d * d <= N:
    for m in range(d * d, N + 1, d * d):
      sf[m] = False
    d += 1
  return sf

def terms(N):
  sf  = squarefree_flags(N)
  out = []
  for n in range(1, N + 1):
    ok = True
    k  = 0
    while (1 << k) < n:
      if not sf[n - (1 << k)]:
        ok = False
        break
      k += 1
    if ok:
      out.append(n)
  return out

if __name__ == "__main__":
  N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
  t = terms(N)
  head = [v for v in t if 2 <= v <= PUBLISHED[-1]]
  print("matches published:", head == PUBLISHED)
  print("count <=", N, ":", len(t))
  print("exceptions to n = 3 mod 12:", [v for v in t if v % 12 != 3])
