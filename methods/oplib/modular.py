"""
Modular obstructions: show an equation has no (or only listed) solutions by
reducing mod small m.

Pattern. "LHS = RHS has no solutions" often fails already mod some small m:
compute the set of residues each side can take mod m (polynomial variables
range over Z/m; exponent variables over the eventually periodic orbit of
base^e mod m) and test whether the sets meet. Examples from the scan:
n! = 2^a + 2^b (n >= 7, mod 7), x^4 + y^4 = 4! z^4 (mod 16), "Carmichael +
2 is a sum of three squares" (mod 8), abc of a Pythagorean triple (mod 60).

`obstruct` searches moduli; `residues_poly` / `residues_power` are the
building blocks. For a family with a free parameter n (like n!), pass the
side as a set computed separately.
"""
from itertools import product


def residues_power(base, m, emin=0):
  """Residues base^e mod m for e >= emin (orbit is eventually periodic)."""
  seen, out = {}, set()
  v, e = pow(base, emin, m), emin
  while v not in seen:
    seen[v] = e
    out.add(v)
    v = (v * base) % m
    e += 1
  return out


def residues_poly(f, nvars, m):
  """Residues f(x_1..x_k) mod m over all x in (Z/m)^k (f takes ints)."""
  return { f(*xs) % m for xs in product(range(m), repeat=nvars) }


def sumset(A, B, m):
  return { (a + b) % m for a in A for b in B }


def obstruct(lhs, rhs, moduli):
  """lhs(m), rhs(m) return residue sets mod m. First m with disjoint sets, else None."""
  for m in moduli:
    if not (lhs(m) & rhs(m)):
      return m
  return None


def primitive_obstruct(f, nvars, m, exclude_all_divisible_by=None):
  """Residues of f over tuples not all divisible by p (for primitive solutions).
  Use when the equation is homogeneous and a descent reduces to primitive ones."""
  p = exclude_all_divisible_by
  return { f(*xs) % m for xs in product(range(m), repeat=nvars)
           if (p is None) or any(x % p for x in xs) }
