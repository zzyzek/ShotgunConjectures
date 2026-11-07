# Numerical check: the equiangular 10-gon with consecutive sides t + m_k d closes.
import cmath
m = [0, 6, 2, 8, 4, 5, 1, 7, 3, 9]
assert sorted(m) == list(range(10))
w = cmath.exp(2j*cmath.pi/10)
for t, d in [(1, 1), (2, 3), (7, 30)]:
  z = sum((t + m[k]*d) * w**k for k in range(10))
  print(t, d, [t + x*d for x in m], abs(z))
