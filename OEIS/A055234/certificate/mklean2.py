# Build the Lean witness table for A055234: for each n <= NMAX a factor list f with sigma(val f) = n*phi(val f).
import sys
from sympy import factorint, totient, divisor_sigma
NMAX=int(sys.argv[1])
W={}
for f in ('ilp.out','ilp_q2.out','ilp60.out','ilp_q3.out','ilp_q4.out'):
  for l in open(f):
    p=l.split()
    if len(p)<4 or p[3]!='verified=True': continue
    n=int(p[0][2:]); x=int(p[2][2:])
    if n not in W or x<W[n]: W[n]=x
miss=[n for n in range(1,NMAX+1) if n not in W]
assert not miss, miss
rows=[]
for n in range(1,NMAX+1):
  x=W[n]; fa=sorted(factorint(x).items())
  assert int(divisor_sigma(x))==n*int(totient(x))
  rows.append("  (%d, [%s])"%(n, ", ".join("(%d, %d)"%(p,e) for p,e in fa)))
open('witnesses.txt','w').write("\n".join("%d %d"%(n,W[n]) for n in range(1,NMAX+1))+"\n")
HEAD=r'''import OpenProblemsLib

/-
OEIS A055234: smallest x with sigma(x) = n*phi(x), or -1 if none.
Conjecture (F. Firoozbakht, 2004): for each n, a(n) > 0, i.e. sigma(x) = n*phi(x) has a solution.

Checked here: for every n with 1 <= n <= NMAX there is x > 0 with sigma(x) = n * phi(x)
(`A055234_exists`).  Each witness is given by its factorization; `factCheck` proves the bases are
distinct primes (trial division), and sigma, phi are evaluated from the factorization
(OpenProblemsLib.ArithFactor: `sigma_val`, `totient_val`).

Not checked here: minimality (the witnesses are not claimed to be a(n)); the conjecture for n > NMAX.
-/

open OpenProblemsLib.ArithFactor ArithmeticFunction

'''
OKDEF='''
def A055234ok (e : ℕ × PF) : Bool :=
  factCheck e.2 && e.2.all (fun pe => decide (0 < pe.2)) && (sigF e.2 == e.1 * phiF e.2)

'''
TAIL=r'''
theorem A055234_covers : (List.range NMAX).all (fun m => A055234W.any (fun e => e.1 == m + 1)) = true := by
  decide +kernel

theorem A055234_exists (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ NMAX) :
    ∃ x, 0 < x ∧ sigma 1 x = n * Nat.totient x := by
  have hc := A055234_covers
  rw [List.all_eq_true] at hc
  have hm := hc (n - 1) (List.mem_range.mpr (by omega))
  rw [List.any_eq_true] at hm
  obtain ⟨e, he, hen⟩ := hm
  have hn : e.1 = n := by
    have := beq_iff_eq.mp hen
    omega
  have ht := A055234_table
  rw [List.all_eq_true] at ht
  have hok := ht e he
  simp only [A055234ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hf, hpos⟩, hs⟩ := hok
  have hF := factOK_of_check e.2 hf
  refine ⟨val e.2, val_pos e.2 hF, ?_⟩
  rw [sigma_val e.2 hF, totient_val e.2 hF hpos, hs, hn]
'''

CH=40
chunks=[rows[i:i+CH] for i in range(0,len(rows),CH)]
defs=[]; thms=[]
for ci,ch in enumerate(chunks):
  defs.append("def A055234W%d : List (ℕ × PF) := [\n%s\n]\n"%(ci,",\n".join(ch)))
  thms.append("theorem A055234_table%d : A055234W%d.all A055234ok = true := by decide +kernel\n"%(ci,ci))
allw=" ++ ".join("A055234W%d"%ci for ci in range(len(chunks)))
tabproof="\n".join("  · exact A055234_table%d"%ci for ci in range(len(chunks)))
lean=HEAD.replace("NMAX",str(NMAX))+"\n".join(defs)+OKDEF+"\n".join(thms)+r"""
def A055234W : List (ℕ × PF) := ALLW

theorem A055234_table : A055234W.all A055234ok = true := by
  simp only [A055234W, List.all_append, TABSPLIT, Bool.and_self]
""".replace("ALLW",allw)+TAIL.replace("NMAX",str(NMAX))
lean=lean.replace("TABSPLIT",", ".join("A055234_table%d"%ci for ci in range(len(chunks))))
open('A055234_mathlib.lean','w').write(lean)
print("written", len(rows), "rows in", len(chunks), "chunks")
