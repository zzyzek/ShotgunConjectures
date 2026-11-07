import sys
sys.path.insert(0, '.')
from exact import pool, count, val
pts = [(-0.562047+0.132048j), (0.39538+0.420723j), (-0.062047+0.998073j), (0.89538-0.445302j), (1.39538+0.420723j), (1+0j), (-1+0j), 0j, (0.437953+0.132048j)]
pl = pool(1)
P = [pl[(round(z.real, 5), round(z.imag, 5))] for z in pts]
cs = count(P)
def q(f): return f"({f.numerator}/{f.denominator} : Rat)" if f.denominator != 1 else f"({f.numerator} : Rat)"
def k(x): return "⟨" + ", ".join(q(t) for t in x) + "⟩"
def pt(p): return "(" + k(p[0]) + ", " + k(p[1]) + ")"
print("def pts : List Pt := [\n  " + ",\n  ".join(pt(p) for p in P) + "]\n")
items = []
for c, s in cs.items():
    tri = sorted(s)[:3]
    items.append("(" + pt(c) + ", " + str(tri[0]) + ", " + str(tri[1]) + ", " + str(tri[2]) + ")")
print("def circs : List (Pt × Nat × Nat × Nat) := [\n  " + ",\n  ".join(items) + "]")
