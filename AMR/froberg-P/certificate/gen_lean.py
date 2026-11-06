# Generate froberg_P.lean: square-and-multiply chains for Psi^e mod p,
# one small theorem per step; matrices stored as base-16 Nat codes.
import sys

CASES = [
  (3, 8, [2]),
  (5, 124, [2, 31]),
  (7, 1368, [2, 3, 19]),
  (11, 32129475, [3, 5, 7, 19, 3221]),
]

def psi(p):
  return [[pow(a, j, p) if (a or j) else 1 for j in range(p)] for a in range(p)]

def mul(p, A, B):
  n = len(B)
  return [[sum(r[k] * B[k][j] for k in range(n)) % p for j in range(n)] for r in A]

def code(M):
  v = 0
  for x in reversed([x for r in M for x in r]):
    v = x + 16 * v
  return "0x%X" % v

HEADER = open(sys.argv[1]).read()
out = [HEADER]
for (p, n, qs) in CASES:
  P = psi(p)
  I = [[int(i == j) for j in range(p)] for i in range(p)]
  out.append("def c%d_code0 : Nat := %s" % (p, code(P)))
  out.append("theorem c%d_code0_ok : decodeMat %d c%d_code0 = psiMat %d := by decide +kernel" % (p, p, p, p))
  out.append("")
  for tag, e in [("n", n)] + [("q%d" % q, n // q) for q in qs]:
    bits = [b == "1" for b in bin(e)[3:]]
    name = "c%d_%s" % (p, tag)
    out.append("-- p = %d, exponent e = %d%s." % (p, e, "" if tag == "n" else " = n / " + tag[1:]))
    out.append("--")
    out.append("def %s_bits : List Bool := [%s]" % (name, ", ".join("true" if b else "false" for b in bits)))
    out.append("theorem %s_bits_val : bitsVal 1 %s_bits = %d := by decide +kernel" % (name, name, e))
    A = P
    prev = "c%d_code0" % p
    for k, b in enumerate(bits):
      C = mul(p, A, A)
      out.append("def %s_s%d : Nat := %s" % (name, k + 1, code(C)))
      out.append("theorem %s_sq%d : encodeMat (mulMat %d (decodeMat %d %s) (decodeMat %d %s)) = %s_s%d := by decide +kernel"
                 % (name, k + 1, p, p, prev, p, prev, name, k + 1))
      cur = "%s_s%d" % (name, k + 1)
      if b:
        C = mul(p, C, P)
        out.append("def %s_m%d : Nat := %s" % (name, k + 1, code(C)))
        out.append("theorem %s_mul%d : encodeMat (mulMat %d (decodeMat %d %s) (decodeMat %d c%d_code0)) = %s_m%d := by decide +kernel"
                   % (name, k + 1, p, p, cur, p, p, name, k + 1))
        cur = "%s_m%d" % (name, k + 1)
      prev = cur
      A = C
    last = prev
    if tag == "n":
      assert A == I
      out.append("theorem %s_identity : decodeMat %d %s = identMat %d := by decide +kernel" % (name, p, last, p))
    else:
      assert A != I
      out.append("theorem %s_not_identity : decodeMat %d %s ≠ identMat %d := by decide +kernel" % (name, p, last, p))
    out.append("")
  out.append("theorem c%d_factors : (%s).all primeB = true ∧ stripAll %s %d = 1 := by decide +kernel"
             % (p, qs, qs, n))
  out.append("")
print("\n".join(out))
