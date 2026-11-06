# Generate the core-Lean witness for A132870 / A177390 (k = 1): rows 0..29 of the unitriangular
# solution are integers, row 30 is R/2 with R(0) odd; Lean checks all row equations n <= 30.
from fractions import Fraction as F
from math import comb
import subprocess, sys
k=1; N=30
T=[[F(1)]]
for n in range(1,N+1):
    e=k*n; target=[F(comb(n,j)*(k*n*n)**(n-j)) for j in range(n+1)]
    row=[F(0)]*n+[F(1)]
    for j in range(n-1,-1,-1):
        row[j]=F(0); v=[F(0)]*(n+1); v[n]=F(1)
        for t in range(e):
            w=[F(0)]*(n+1)
            for i in range(j,n+1):
                if v[i]:
                    Ri=row if i==n else T[i]
                    for c in range(j,i+1): w[c]+=v[i]*Ri[c]
            v=w
        row[j]=(target[j]-v[j])/e
    T.append(row)
assert all(x.denominator==1 for r in T[:30] for x in r)
R=[2*x for x in T[30]]; assert all(x.denominator==1 for x in R) and R[0].numerator%2==1
rows=[[int(x) for x in r] for r in T[:30]]
Rint=[int(x) for x in R]
def lst(v): return "[" + ", ".join(str(x) for x in v) + "]"
out=open(sys.argv[1],'w')
out.write('''/-
OEIS A132870 / A177390 (Hanna's conjecture, k = 1): no integer lower-unitriangular J with
"g.f. of row n of J^(k n) = (k n^2 + y)^n" for k = 1 (the triangle of A132870).

Checked here (core Lean, `decide +kernel`, exact integers):
* `rows` (rows 0..29, from the A132870 recursion) are integer, unitriangular, and
  for every n <= 29 row n of rows^n equals the coefficients of (n^2 + y)^n (`eq_upto29`);
* the rational row 30 equal to R/2 (R below, R 0 odd) extends them so that row 30 of T^30 equals
  the coefficients of (30^2 + y)^30, checked as 2 * (row 30 of T^30) = 2 * target (`eq_row30`);
* R 0 is odd (`R0_odd`), so T(30,0) = R 0 / 2 is not an integer.
Not checked here (stated in the README): uniqueness. For a lower-unitriangular J, entry (n, j) of
J^e equals e * J(n,j) plus terms in rows < n and in J(n,l), l > j; with e = n > 0 the row
equations determine row n from the earlier rows, so the rational solution is unique and an
integer one would have to equal T, whose entry (30,0) is not an integer.
-/

def rows : List (List Int) := [
''')
out.write(",\n".join("  "+lst(r) for r in rows))
out.write("]\n\ndef R : List Int := "+lst(Rint)+"\n\n")
out.write('''def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

def target (n : Nat) : List Int :=
  (List.range (n + 1)).map fun j => (binom n j : Int) * ((n * n : Nat) : Int) ^ (n - j)

def get (v : List Int) (i : Nat) : Int := v.getD i 0

/-- v * M for a row vector v (length m) and lower-triangular rows M (row i has length i+1). -/
def vecMul (M : List (List Int)) (m : Nat) (v : List Int) : List Int :=
  (List.range m).map fun c =>
    ((List.range m).map fun i => get v i * get (M.getD i []) c).foldl (· + ·) 0

def rowPow (M : List (List Int)) (n e : Nat) : List Int :=
  (List.range e).foldl (fun v _ => vecMul M (n + 1) v)
    ((List.range (n + 1)).map fun i => if i = n then 1 else 0)

def unitri : Bool :=
  (List.range 30).all fun i => (rows.getD i []).length == i + 1 && get (rows.getD i []) i == 1

theorem rows_unitri : unitri = true := by decide +kernel

theorem eq_upto29 :
    (List.range 30).all (fun n => rowPow rows n n == target n) = true := by decide +kernel

/-- Rows 0..29 together with 2*(row 30) = R: scaled iteration w = 2 v. -/
def rows30 : List (List Int) := rows ++ [R]

def vecMul2 (v : List Int) : List Int :=
  -- 2 (v * T) where v = w/2, w integer with w 30 = 2: sum_{i<30} w_i rows_i + (w_30 / 2) * R
  (List.range 31).map fun c =>
    ((List.range 30).map fun i => get v i * get (rows.getD i []) c).foldl (· + ·) 0
      + (get v 30 / 2) * get R c

def row30Scaled : List Int :=
  (List.range 30).foldl (fun w _ => vecMul2 w) ((List.range 31).map fun i => if i = 30 then 2 else 0)

theorem R_last : get R 30 = 2 := by decide +kernel

theorem eq_row30 : row30Scaled = (target 30).map (2 * ·) := by decide +kernel

theorem R0_odd : get R 0 % 2 = 1 := by decide +kernel
''')
out.close()
