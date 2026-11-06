# Sanity check of the upper-bound construction: points of the fcc lattice
# (minimum distance 1) inside a ball of radius R.  Prints n, the actual
# diameter D of the point set, and D / n^(1/3), which should approach
# (3*sqrt(2)/pi)^(1/3) = 1.10534 (finite-n values may sit on either side).
#
import math, itertools

def fcc_ball(R):
  # fcc = integer points with even coordinate sum, scaled by 1/sqrt(2)
  # (nearest-neighbour distance sqrt(2) before scaling).
  #
  s, m, pts = 1 / math.sqrt(2), int(R * math.sqrt(2)) + 2, []
  for x, y, z in itertools.product(range(-m, m + 1), repeat=3):
    if ((x + y + z) % 2 == 0) and ((x*x + y*y + z*z) * s * s <= R * R):
      pts.append((x * s, y * s, z * s))
  return pts

def diam(pts):
  # Diameter of a centrally symmetric set = 2 * max norm.
  #
  return 2 * max(math.sqrt(x*x + y*y + z*z) for x, y, z in pts)

L = (3 * math.sqrt(2) / math.pi) ** (1 / 3)
print("limit", L)
for R in [2, 4, 8, 16]:
  P = fcc_ball(R)
  n, D = len(P), diam(P)
  print(R, n, round(D, 4), round(D / n ** (1 / 3), 5))
