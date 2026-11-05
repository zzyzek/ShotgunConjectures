# Generate the Lean pieces of A124431_mathlib.lean: definitions (defs.lean),
# A124431_rat (rat.lean) and A124431_core (core.lean), after checking the
# telescoping identity with sympy. Output goes to the current directory.
#
import sympy as sp

# Certificate: G(n,i)/2^(n-2i) = sum (u + v i) C(n-i-a, i-b) C(n-i-a2, i-b2).
#
CERT = [((0,0,0,0),(1,4)), ((0,0,0,1),(0,-6)), ((0,1,0,1),(0,-4)), ((0,0,1,0),(-2,-5)),
        ((0,0,2,0),(sp.Rational(-1,2),0)), ((0,0,3,0),(sp.Rational(1,2),sp.Rational(-1,4))),
        ((1,0,1,0),(1,0)), ((1,0,2,0),(0,sp.Rational(3,4))), ((1,0,3,0),(0,sp.Rational(-1,2))),
        ((2,0,2,0),(sp.Rational(1,4),2)), ((2,0,3,0),(0,sp.Rational(-5,4))),
        ((3,0,3,0),(sp.Rational(-1,4),sp.Rational(1,4)))]

nn, ii = sp.symbols('n i')
X  = nn - ii + 1
D  = X - ii

def ff(z, k):
  r = sp.Integer(1)
  for t in range(k):
    r *= (z - t)
  return r

# K(alpha, beta) = C(X - alpha, i + beta) with X = n - i + 1; p * K = E * q.
#
def pq(a, b):
  if b == 0:  return ff(X, a), ff(D, a)
  if b == 1:  return (ii + 1) * ff(X, a), ff(D, a) * (D - a)
  if b == -1: return ff(X, a), ii * ff(D, a - 1)

def lean_poly(e):
  s = str(sp.expand(e)) if False else str(e)
  return s.replace('**', '^')

def ktxt(a, b):
  top = "n - i + 1" if a == 0 else "n - i + 1 - %d" % a
  bot = {0: "i", 1: "i + 1", -1: "i - 1"}[b]
  return "A124431_Cz (%s) (%s)" % (top, bot)

def hname(a, b):
  return "h%d%s" % (a, {0: "z", 1: "p", -1: "m"}[b])

# The identity stuff = 0 with stuff in K atoms (S = 2^(n-2i-4) removed).
#
c = [nn + 1, -2 * (2 * nn + 1), 2 * (nn - 1), 2 * (5 - 2 * nn), nn - 3]
terms = []
for l in range(5):
  terms.append((c[l] * 2 ** (4 - l), (l + 1, 0), (l + 1, 0)))
  terms.append((c[l] * 2 ** (4 - l) * 2, (l + 1, -1), (l, 0)))
for (a, b, a2, b2), (u, v) in CERT:
  terms.append((-4 * (u + v * (ii + 1)), (a + 2, 1 - b), (a2 + 2, 1 - b2)))
  terms.append((16 * (u + v * ii), (a + 1, -b), (a2 + 1, -b2)))

E = sp.Symbol('E')
tot = sum(co * E * pq(*k1)[1] / pq(*k1)[0] * E * pq(*k2)[1] / pq(*k2)[0] for co, k1, k2 in terms)
print("sympy identity:", sp.simplify(sp.together(tot)) == 0)

P = ff(X, 5) ** 2 * (ii + 1) ** 2
need = sorted(set([k for _, k1, k2 in terms for k in (k1, k2)]))
print("atoms:", need)

L = []
L.append("theorem A124431_core (n i : ℤ) (hX : ((n : ℚ) - i + 1) * ((n : ℚ) - i) * ((n : ℚ) - i - 1) *")
L.append("    ((n : ℚ) - i - 2) * ((n : ℚ) - i - 3) ≠ 0) (hi : (i : ℚ) + 1 ≠ 0) :")
L.append("    ((n : ℚ) + 1) * A124431_w n i - 2 * (2 * n + 1) * A124431_w (n - 1) i +")
L.append("      2 * (n - 1) * A124431_w (n - 2) i + 2 * (5 - 2 * n) * A124431_w (n - 3) i +")
L.append("      (n - 3) * A124431_w (n - 4) i = A124431_G n (i + 1) - A124431_G n i := by")
L.append("  set S : ℚ := (2 : ℚ) ^ (n - 2 * i - 4) with hS")
pw = [("n - 2 * i", 16), ("n - 1 - 2 * i", 8), ("n - 2 - 2 * i", 4), ("n - 3 - 2 * i", 2),
      ("n - 4 - 2 * i", 1), ("n - 2 * (i + 1)", 4)]
for k, (ex, val) in enumerate(pw):
  L.append("  have p%d : (2 : ℚ) ^ (%s) = S * %d := by" % (k, ex, val))
  L.append("    rw [hS, show %s = (n - 2 * i - 4) + %d by ring, zpow_add₀ two_ne_zero]" % (ex, {16:4,8:3,4:2,2:1,1:0}[val]))
  L.append("    norm_num")
L.append("  simp only [A124431_w, A124431_G]")
L.append("  rw [p0, p1, p2, p3, p4, p5]")

# Basic relations, cast-normalised.
#
for t in range(5):
  L.append("  have r1_%d := A124431_R1 (n - i + 1 - %d) i" % (t, t))
for a in range(2, 6):
  L.append("  have r3_%d := A124431_R3 (n - i + 1 - %d) i" % (a, a))
for a in range(1, 6):
  L.append("  have r2_%d := A124431_R2 (n - i + 1 - %d + 1) i" % (a, a))
L.append("  push_cast at *")

Xs = "((n : ℚ) - i + 1)"
Ds = "(((n : ℚ) - i + 1) - (i : ℚ))"
def ffs(z, k):
  if k == 0: return "1"
  return " * ".join("(%s - %d)" % (z, t) for t in range(k))
for a in range(1, 6):
  # h(a,0): K(a,0) ff(X,a) = E ff(D,a)
  combo = []
  for t in range(a):
    co = [ffs(Xs, t)] + ["(%s - %d)" % (Ds, s) for s in range(t + 1, a)]
    combo.append("%s * r1_%d" % (" * ".join(co), t))
  L.append("  have %s : %s * (%s) = %s * (%s) := by" % (hname(a, 0), ktxt(a, 0), ffs(Xs, a), ktxt(0, 0), ffs(Ds, a)))
  L.append("    linear_combination (norm := ring_nf) %s" % " + ".join(combo))
for a in range(1, 6):
  prev = "%s" % hname(a - 1, 0) if a > 1 else None
  rhs = "%s * ((i : ℚ) * (%s))" % (ktxt(0, 0), ffs(Ds, a - 1))
  L.append("  have %s : %s * (%s) = %s := by" % (hname(a, -1), ktxt(a, -1), ffs(Xs, a), rhs))
  if prev:
    L.append("    linear_combination (norm := ring_nf) (%s) * r2_%d + (i : ℚ) * %s" % (ffs(Xs, a - 1), a, prev))
  else:
    L.append("    linear_combination (norm := ring_nf) r2_%d" % a)
for a in range(2, 6):
  L.append("  have %s : %s * (((i : ℚ) + 1) * (%s)) = %s * ((%s) * (%s - %d)) := by" %
           (hname(a, 1), ktxt(a, 1), ffs(Xs, a), ktxt(0, 0), ffs(Ds, a), Ds, a))
  L.append("    linear_combination (norm := ring_nf) (%s) * r3_%d + (%s - %d) * %s" % (ffs(Xs, a), a, Ds, a, hname(a, 0)))

# p, q as Lean strings.
#
def pqs(a, b):
  if b == 0:  return ffs(Xs, a), ffs(Ds, a)
  if b == 1:  return "((i : ℚ) + 1) * (%s)" % ffs(Xs, a), "(%s) * (%s - %d)" % (ffs(Ds, a), Ds, a)
  if b == -1: return ffs(Xs, a), "(i : ℚ) * (%s)" % ffs(Ds, a - 1)

def hof(k):
  if k == (0, 0): return None
  return hname(*k)

Ds = "(%s - (i : ℚ))" % Xs
stuff = []
ratt = []
for co, k1, k2 in terms:
  cs = "(%s)" % str(sp.expand(co)).replace('**', '^').replace('n', '(n : ℚ)').replace('i', '(i : ℚ)')
  csx = "(%s)" % str(sp.expand(co.subs(nn, sp.Symbol('x') + ii - 1))).replace('**', '^').replace('i', '(i : ℚ)')
  stuff.append("%s * %s * %s" % (cs, ktxt(*k1), ktxt(*k2)))
  p1, q1 = pqs(*k1); p2, q2 = pqs(*k2)
  ratt.append((csx, k1, k2))
stuffs = " + ".join(stuff)

def pqx(a, b):
  Xs_, Ds_ = "x", "(x - i)"
  def f(z, k):
    if k == 0: return "1"
    return " * ".join("(%s - %d)" % (z, t) for t in range(k))
  if b == 0:  return f(Xs_, a), f(Ds_, a)
  if b == 1:  return "(i + 1) * (%s)" % f(Xs_, a), "(%s) * (%s - %d)" % (f(Ds_, a), Ds_, a)
  if b == -1: return f(Xs_, a), "i * (%s)" % f(Ds_, a - 1)
def u(k):
  p, q = pqx(*k)
  return "((%s) / (%s))" % (q, p)
R = []
R.append("theorem A124431_rat (x i : ℚ) (h0 : x - 0 ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) (h3 : x - 3 ≠ 0)")
R.append("    (h4 : x - 4 ≠ 0) (hi : i + 1 ≠ 0) :")
R.append("    " + " +\n      ".join("%s * %s * %s" % (cs.replace('(i : ℚ)', 'i'), u(k1), u(k2)) for cs, k1, k2 in ratt) + " = 0 := by")
R.append("  field_simp")
R.append("  ring")
open('rat.lean', 'w').write("\n".join(R) + "\n")

L.append("  have hx0 : ((n : ℚ) - i + 1) - 0 ≠ 0 := by intro h; apply hX; linear_combination (((n : ℚ) - i) * ((n : ℚ) - i - 1) * ((n : ℚ) - i - 2) * ((n : ℚ) - i - 3)) * h")
for t in range(1, 5):
  others = " * ".join("((n : ℚ) - i + 1 - %d)" % s for s in range(5) if s != t)
  L.append("  have hx%d : ((n : ℚ) - i + 1) - %d ≠ 0 := by intro h; apply hX; linear_combination (%s) * h" % (t, t, others))
for k in need:
  if k == (0, 0): continue
  p, q = pqs(*k)
  L.append("  have e%s : %s = %s * ((%s) / (%s)) := by" % (hname(*k), ktxt(*k), ktxt(0, 0), q, p))
  if k[0] + (1 if k[1] == 1 else 0) == 1:
    L.append("    rw [mul_div_assoc', eq_div_iff (by assumption)]")
  else:
    L.append("    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]")
  L.append("    exact %s" % hname(*k))
L.append("  have st : %s = 0 := by" % stuffs)
L.append("    rw [%s]" % ", ".join("e" + hname(*k) for k in need if k != (0, 0)))
L.append("    linear_combination (%s) ^ 2 * A124431_rat ((n : ℚ) - i + 1) i hx0 hx1 hx2 hx3 hx4 hi" % ktxt(0, 0))
L.append("  linear_combination (norm := ring_nf) S * st")
open('core.lean', 'w').write("\n".join(L) + "\n")
print("lines", len(L))

# Definitions A124431_w and A124431_G (G from CERT).
#
def cz(a, b):
  top = "n - i" if a == 0 else "n - i - %d" % a
  bot = "i" if b == 0 else "i - %d" % b
  return "A124431_Cz (%s) (%s)" % (top, bot)

parts = ["((%s : ℚ) + (%s : ℚ) * i) * %s * %s" % (u, v, cz(a, b), cz(a2, b2)) for (a, b, a2, b2), (u, v) in CERT]
open('defs.lean', 'w').write("""/-- The summand w(m, i) = 2^(m-2i) (C(m-i, i)^2 + 2 C(m-i, i-1) C(m-i+1, i)). -/
noncomputable def A124431_w (m i : ℤ) : ℚ :=
  2 ^ (m - 2 * i) * (A124431_Cz (m - i) i ^ 2 + 2 * A124431_Cz (m - i) (i - 1) * A124431_Cz (m - i + 1) i)

/-- The telescoping certificate G(n, i). -/
noncomputable def A124431_G (n i : ℤ) : ℚ :=
  2 ^ (n - 2 * i) * (""" + " +\n    ".join(parts) + ")\n")
