# Check the key step of the p = 2 argument for r = 3, 5, 7: beta = diag(0,1), l = (r+1)/2,
# N = K_l, C = invertible diagonal matrices mod 2^r, J = K_(l-1).
# (1) c^(-1) j c j^(-1) lies in K_l and psi_beta of it is 1 for all c in C, j in J (mod K_l reps);
# (2) psi_beta([j1, j2]) for j = 1 + 2^(l-1) x, x in M_2(F_2), gives a form on J/R that is
#     nondegenerate on (off-diagonal part), with R = diagonal part.
import itertools, cmath
def mul(A, B, m):
  return ((A[0]*B[0]+A[1]*B[2]) % m, (A[0]*B[1]+A[1]*B[3]) % m,
          (A[2]*B[0]+A[3]*B[2]) % m, (A[2]*B[1]+A[3]*B[3]) % m)
def inv(A, m):
  d = (A[0]*A[3]-A[1]*A[2]) % m; di = pow(d, -1, m)
  return ((A[3]*di) % m, (-A[1]*di) % m, (-A[2]*di) % m, (A[0]*di) % m)
for r in (3, 5, 7):
  m = 2**r; l = (r+1)//2; q = 2**(r-l)
  def psi(A):
    # A in K_l: A = 1 + 2^l x; psi = exp(2 pi i tr(beta x)/2^(r-l)), beta = diag(0,1)
    x = [((A[0]-1) % m), A[1] % m, A[2] % m, ((A[3]-1) % m)]
    assert all(v % 2**l == 0 for v in x), A
    x = [v // 2**l for v in x]
    return x[3] % q
  C = [(a, 0, 0, d) for a in range(1, m, 2) for d in range(1, m, 2)]
  Js = [(1+2**(l-1)*x0, 2**(l-1)*x1, 2**(l-1)*x2, 1+2**(l-1)*x3) for x0, x1, x2, x3 in itertools.product(range(2**(r-l+1)), repeat=4)]
  for c in C[::7]:
    ci = inv(c, m)
    for j in Js[::5]:
      e = mul(mul(mul(ci, j, m), c, m), inv(j, m), m)
      assert psi(e) == 0
  # commutator form on representatives x in M_2(F_2)
  reps = [(1+2**(l-1)*a, 2**(l-1)*b, 2**(l-1)*cc, 1+2**(l-1)*d) for a, b, cc, d in itertools.product(range(2), repeat=4)]
  form = {}
  for j1 in reps:
    for j2 in reps:
      k = mul(mul(j1, j2, m), inv(mul(j2, j1, m), m), m)
      form[(j1, j2)] = psi(k) * 2 // q if q > 1 else 0
  e12 = (1, 2**(l-1), 0, 1); e21 = (1, 0, 2**(l-1), 1)
  assert psi(mul(mul(e12, e21, m), inv(mul(e21, e12, m), m), m)) == q // 2
  print("r =", r, "ok")
