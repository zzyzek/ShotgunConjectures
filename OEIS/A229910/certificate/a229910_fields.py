# A229910 second conjecture (finite fields): does F_q (q > 13) contain a
# primitive g with g + 1/g primitive?  And (q > 61) g with g - 1/g primitive?
# Exhaustive for prime powers q < 400; F_q = F_p[x]/(f), f irreducible
# (sympy test).  Expected exceptions (Cohen, Oliveira e Silva, Sutherland,
# Trudgian 2018, Cor. 2): + : {2,3,4,5,7,9,13,25,121},
# - : {2,3,4,5,9,13,25,61,121}.
#
from sympy import factorint, Poly, symbols
from itertools import product
X = symbols('x')

def make_field(p, e):
  if e == 1:
    return (lambda a, b: (a[0] * b[0] % p,)), [(i,) for i in range(1, p)], (1,)
  for coeffs in product(range(p), repeat=e):
    f = list(coeffs) + [1]
    if Poly(list(reversed(f)), X, modulus=p).is_irreducible: break
  def mul(a, b):
    r = [0] * (2 * e - 1)
    for i, u in enumerate(a):
      if u:
        for j, v in enumerate(b): r[i + j] = (r[i + j] + u * v) % p
    for d in range(2 * e - 2, e - 1, -1):
      c = r[d]
      if c:
        for i in range(e + 1): r[d - e + i] = (r[d - e + i] - c * f[i]) % p
    return tuple(r[:e])
  nz = [a for a in product(range(p), repeat=e) if any(a)]
  return mul, nz, tuple([1] + [0] * (e - 1))

def check(q):
  fq = factorint(q)
  if len(fq) != 1: return None
  (p, e), = fq.items()
  mul, nz, one = make_field(p, e)
  N = q - 1
  ps = list(factorint(N))
  def pw(a, k):
    r = one
    while k:
      if k & 1: r = mul(r, a)
      a = mul(a, a); k >>= 1
    return r
  prim = set(a for a in nz if all(pw(a, N // r) != one for r in ps))
  add = lambda a, b, s: tuple((u + s * v) % p for u, v in zip(a, b))
  plus = minus = False
  for g in prim:
    gi = pw(g, N - 1)
    plus = plus or (add(g, gi, 1) in prim)
    minus = minus or (add(g, gi, -1) in prim)
    if plus and minus: break
  return plus, minus

bad_plus, bad_minus = [], []
for q in range(2, 400):
  r = check(q)
  if r is None: continue
  if not r[0]: bad_plus.append(q)
  if not r[1]: bad_minus.append(q)
print("prime powers q < 400 with no g such that g, g + 1/g are primitive:", bad_plus)
print("prime powers q < 400 with no g such that g, g - 1/g are primitive:", bad_minus)
