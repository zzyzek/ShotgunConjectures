# Side lengths of the triangles that tile the sphere edge-to-edge (Ueno-Agaoka 2002,
# Corollary 3), angles in units of pi. Spherical law of cosines for angles:
#   cos a = (cos A + cos B cos C) / (sin B sin C).
# Prints, per family, the range of the shortest and longest side (degrees) and the number of tiles.
from math import pi, cos, sin, acos, degrees
def sides(A, B, C):
  A, B, C = A * pi, B * pi, C * pi
  f = lambda X, Y, Z: degrees(acos(max(-1, min(1, (cos(X) + cos(Y) * cos(Z)) / (sin(Y) * sin(Z))))))
  return sorted([f(A, B, C), f(B, C, A), f(C, A, B)])
print("sporadic:")
for name, ang, F in (("F24", (2/3, 1/4, 1/4), 24), ("F60a", (2/3, 1/5, 1/5), 60), ("F60b", (2/5, 1/3, 1/3), 60),
                     ("F48", (1/2, 1/3, 1/4), 48), ("F120", (1/2, 1/3, 1/5), 120)):
  print("  %-5s F=%3d sides %s" % (name, F, ["%.2f" % s for s in sides(*ang)]))
fams = {
  "2n: (1/2,1/2,2/n)":        lambda n: ((1/2, 1/2, 2/n), 2 * n, 3),
  "4n: ((n-1)/2n,(n-1)/2n,2/n)": lambda n: (((n-1)/(2*n), (n-1)/(2*n), 2/n), 4 * n, 4),
  "8n: (1/2,(n-1)/2n,1/n)":   lambda n: ((1/2, (n-1)/(2*n), 1/n), 8 * n, 3),
}
for name, fam in fams.items():
  lo = None
  rows = []
  for n in range(3, 400):
    ang, F, nmin = fam(n)
    if n < nmin: continue
    s = sides(*ang); rows.append((n, F, s))
  mx = min(r[2][2] for r in rows); allbelow90 = all(r[2][2] < 90 for r in rows)
  print("%-30s n=%d..%d: longest side >= %.3f deg (n large), all sides < 90 deg: %s; F=%d at n=%d: %s"
        % (name, rows[0][0], rows[-1][0], mx, allbelow90, rows[10][1], rows[10][0], ["%.2f" % x for x in rows[10][2]]))
# alpha + beta = 1 family: a + b = 180 deg, so a side >= 90 deg; sample
for al in (0.55, 0.7, 0.9):
  s = sides(al, 1 - al, 1/40); print("  alpha+beta=1, gamma=1/40, alpha=%.2f: sides %s" % (al, ["%.2f" % x for x in s]))
