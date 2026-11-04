# Chernick-type families: for each factor f_i(k), check that f_i(k) - 1
# divides N(k) - 1 as polynomials with an integer quotient (sympy).
# Then N(k) is Carmichael (Korselt) whenever all factors are prime.
#
from sympy import symbols, expand, Poly, div
k = symbols('k')
fam = {'A182085': [30*k+7, 60*k+13, 150*k+31],
       'A182088': [30*k-29, 60*k-59, 90*k-89, 180*k-179],
       'A182089': [330*k+7, 660*k+13, 990*k+19, 1980*k+37],
       'A182132': [30*k-7, 90*k-23, 300*k-79],
       'A182133': [30*k+13, 90*k+37, 150*k+61],
       'A182416': [60*k+13, 180*k+37, 300*k+61]}
for a, fs in fam.items():
  N = 1
  for f in fs: N = expand(N * f)
  for f in fs:
    q, r = div(Poly(N - 1, k), Poly(f - 1, k))
    ok = (r.is_zero) and all(c.is_integer for c in q.all_coeffs())
    print(a, f - 1, 'quotient', q.as_expr(), 'integer exact:', ok)
