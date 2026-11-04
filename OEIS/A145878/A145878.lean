/-
OEIS A145878: T(n,k) = number of permutations of [n] with k strong fixed points.
Formulas (once conjectures, now "previous conjectures" in the entry, proved by
Baren et al. via McGinnis's recursion): T(3+k,k) = 3k+3,
T(4+k,k) = (k+1)(k+28)/2, T(5+k,k) = (k+1)(3k+77),
T(6+k,k) = (k+1)(k^2+110k+2982)/6, T(7+k,k) = (k+1)(3k^2+235k+7352)/2.

Argument. A permutation with k strong fixed points splits into k+1 blocks
with none (sizes summing to n-k, T(0,0)=1, T(1,0)=0), so
T(r+k,k) = sum_j C(k+1, j) w_r(j), w_r(j) = weighted compositions of r into j
blocks of size ≥ 2; this is a polynomial in k of degree ≤ floor(r/2) ≤ 3.
Agreement at 4 values of k proves each formula.

Checked here (core Lean, `decide`): with T(m,0) = 1, 0, 1, 3, 14, 77, 497, 3676
(A052186) for m ≤ 7 and T(n,k) = sum_{i=1..n-k+1} T(n-i,k-1) T(i-1,0) (McGinnis),
the five formulas hold for 0 ≤ k ≤ 8.
Not checked here: the block decomposition (which gives the recursion and the
degree bound), and the values of A052186.
-/

def c0 : Nat → Nat
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 14 | 5 => 77 | 6 => 497 | 7 => 3676 | _ => 0

/-- T(r + k, k), by recursion on k, for r ≤ 7. -/
def Tk : Nat → Nat → Nat
  | r, 0 => c0 r
  | r, k + 1 => ((List.range (r + 1)).map (fun i => Tk (r - i) k * c0 i)).foldl (· + ·) 0

theorem f3 : (List.range 9).all (fun k => Tk 3 k == 3 * k + 3) = true := by decide
theorem f4 : (List.range 9).all (fun k => 2 * Tk 4 k == (k + 1) * (k + 28)) = true := by decide
theorem f5 : (List.range 9).all (fun k => Tk 5 k == (k + 1) * (3 * k + 77)) = true := by decide
theorem f6 : (List.range 9).all (fun k => 6 * Tk 6 k == (k + 1) * (k * k + 110 * k + 2982)) = true := by decide
theorem f7 : (List.range 9).all (fun k => 2 * Tk 7 k == (k + 1) * (3 * k * k + 235 * k + 7352)) = true := by decide
