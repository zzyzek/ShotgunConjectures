/-
OEIS A192023, comment (Clark Kimberling, Mar 31 2012): "for n > 2, A192023(n-2) is the
number of 2 X 2 matrices with all terms in {1,2,...,n} and determinant 2n."
A192023(n) = n*(2n^2+6n-5)/3 (Wiener index of the comb graph; the formula is the
entry's own, stated there as the definition-equivalent closed form).

Checked here (kernel evaluation, `decide +kernel`):
  * `A192023_det_counterexample`: for n = 3 there are 2 matrices [[w,x],[y,z]] with
    entries in {1,2,3} and w*z - x*y = 6, while A192023(1) = 1;
  * `A192023_det_mismatch_<n>`: the two sides differ for every n with 3 <= n <= 10 (one theorem per n);
  * `A192023_linear_<n>`: the corrected statement (Kimberling's table in A211795,
    relation w = -x + y + z + 2): #{(w,x,y,z) in {1..n}^4 : w + x = y + z + 2}
    = A192023(n-1) for 1 <= n <= 15 (one theorem per n).
Not checked here: the corrected statement for all n (hand proof in README.md);
that `aSeq` equals the graph-theoretic definition of A192023 (we use the OEIS formula).
-/

def aSeq (n : Nat) : Nat := n * (2 * n * n + 6 * n - 5) / 3

-- Sum of f i over i = 1..n.
--
def sumTo (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + f (i + 1)) 0

-- Number of (y, z) in {1..n}^2 with y * z = m.
--
def prodReps (n m : Nat) : Nat :=
  sumTo n (fun y => if m % y = 0 ∧ 1 ≤ m / y ∧ m / y ≤ n then 1 else 0)

-- Number of matrices [[w, x], [y, z]] with entries in {1..n} and w*z - x*y = d
-- (d >= 1, so w*z = x*y + d).
--
def detCount (n d : Nat) : Nat :=
  sumTo n (fun w => sumTo n (fun z => if d < w * z then prodReps n (w * z - d) else 0))

-- Number of (w, x, y, z) in {1..n}^4 with w + x = y + z + 2 (z is determined).
--
def linCount (n : Nat) : Nat :=
  sumTo n (fun w => sumTo n (fun x => sumTo n (fun y =>
    if y + 2 < w + x ∧ w + x - y - 2 ≤ n then 1 else 0)))

theorem A192023_det_counterexample : detCount 3 6 = 2 ∧ aSeq 1 = 1 := by decide +kernel

theorem A192023_det_mismatch_3 : detCount 3 6 ≠ aSeq 1 := by decide +kernel

theorem A192023_det_mismatch_4 : detCount 4 8 ≠ aSeq 2 := by decide +kernel

theorem A192023_det_mismatch_5 : detCount 5 10 ≠ aSeq 3 := by decide +kernel

theorem A192023_det_mismatch_6 : detCount 6 12 ≠ aSeq 4 := by decide +kernel

theorem A192023_det_mismatch_7 : detCount 7 14 ≠ aSeq 5 := by decide +kernel

theorem A192023_det_mismatch_8 : detCount 8 16 ≠ aSeq 6 := by decide +kernel

theorem A192023_det_mismatch_9 : detCount 9 18 ≠ aSeq 7 := by decide +kernel

theorem A192023_det_mismatch_10 : detCount 10 20 ≠ aSeq 8 := by decide +kernel

theorem A192023_linear_1 : linCount 1 = aSeq 0 := by decide +kernel

theorem A192023_linear_2 : linCount 2 = aSeq 1 := by decide +kernel

theorem A192023_linear_3 : linCount 3 = aSeq 2 := by decide +kernel

theorem A192023_linear_4 : linCount 4 = aSeq 3 := by decide +kernel

theorem A192023_linear_5 : linCount 5 = aSeq 4 := by decide +kernel

theorem A192023_linear_6 : linCount 6 = aSeq 5 := by decide +kernel

theorem A192023_linear_7 : linCount 7 = aSeq 6 := by decide +kernel

theorem A192023_linear_8 : linCount 8 = aSeq 7 := by decide +kernel

theorem A192023_linear_9 : linCount 9 = aSeq 8 := by decide +kernel

theorem A192023_linear_10 : linCount 10 = aSeq 9 := by decide +kernel

theorem A192023_linear_11 : linCount 11 = aSeq 10 := by decide +kernel

theorem A192023_linear_12 : linCount 12 = aSeq 11 := by decide +kernel

theorem A192023_linear_13 : linCount 13 = aSeq 12 := by decide +kernel

theorem A192023_linear_14 : linCount 14 = aSeq 13 := by decide +kernel

theorem A192023_linear_15 : linCount 15 = aSeq 14 := by decide +kernel
