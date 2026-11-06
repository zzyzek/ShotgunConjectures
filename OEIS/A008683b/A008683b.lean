/-
OEIS A008683 (Moebius function), comment of M. Granvik (Dec 2008):
"Consider the table A051731 and treat 1 as a divisor. Move the value in the
lower right corner vertically to a divisor position in the transpose of the
table and you will find that the determinant is the Moebius function. The
number of permutation matrices that contribute to the Moebius function
appears to be A074206."

Two readings (README), both 0-indexed n × n:
* `A008683b_m1`: A051731 (entry (i, k) = 1 iff k | i) with its lower right 1
  moved up column n to row 1: column n becomes e_1.
* `A008683b_m2`: the Redheffer matrix (entry (i, j) = 1 iff j = 1 or i | j)
  with its lower right entry set to 0 (the A008683 comment on A143104).

`A008683b_det M n` is the Leibniz determinant and `A008683b_cnt M n` the
number of permutations σ with all M(i, σ(i)) = 1 ("contributing permutation
matrices"), both by enumerating injective row-by-row assignments (the sign
of a permutation is (-1)^(inversions), counted as columns are chosen).

Checked here by `decide` for 2 ≤ n ≤ 10 (`A008683b_check`): for both
matrices the determinant is μ(n) (`A008683b_mu`, by trial division) and the
count is the number of ordered factorizations H(n) (`A008683b_H`, A074206).

Not checked here: general n (README: cofactor of the zeta matrix /
Redheffer's theorem for the determinant; divisor chains n = c_0 > c_1 > ...
> c_k = 1 for the count, all other rows forced to the diagonal).
-/

/-- Reading 1: A051731 with the corner moved to row 1 of column n. -/
def A008683b_m1 (n i j : Nat) : Bool :=
  if j = n - 1 then i == 0 else (i + 1) % (j + 1) == 0

/-- Reading 2: Redheffer matrix with the corner set to 0. -/
def A008683b_m2 (n i j : Nat) : Bool :=
  if i = n - 1 ∧ j = n - 1 then false else (j == 0 || (j + 1) % (i + 1) == 0)

/-- Signed sum and count over injective assignments of rows i, i+1, ...,
n-1 (fuel f = n - i) avoiding the columns in `used`. -/
def A008683b_go (M : Nat → Nat → Bool) (n : Nat) : Nat → Nat → List Nat → Int × Nat
  | 0, _, _ => (1, 1)
  | f + 1, i, used =>
    (List.range n).foldl (fun acc j =>
      if M i j && !(used.contains j) then
        let r := A008683b_go M n f (i + 1) (j :: used)
        let s : Int := if (used.filter (· > j)).length % 2 = 0 then 1 else -1
        (acc.1 + s * r.1, acc.2 + r.2)
      else acc) (0, 0)

def A008683b_det (M : Nat → Nat → Bool) (n : Nat) : Int := (A008683b_go M n n 0 []).1
def A008683b_cnt (M : Nat → Nat → Bool) (n : Nat) : Nat := (A008683b_go M n n 0 []).2

/-- Moebius function by trial division (fuel = n). -/
def A008683b_muAux : Nat → Nat → Nat → Int
  | 0, _, _ => 1
  | f + 1, m, p =>
    if m ≤ 1 then 1
    else if p * p > m then -1
    else if m % p = 0 then
      (if (m / p) % p = 0 then 0 else - A008683b_muAux f (m / p) (p + 1))
    else A008683b_muAux f m (p + 1)

def A008683b_mu (n : Nat) : Int := A008683b_muAux (2 * n) n 2

/-- Ordered factorizations H(n) (A074206), H(1) = 1. -/
def A008683b_Haux : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, m => if m ≤ 1 then 1 else
      ((List.range (m + 1)).filter (fun d => 2 ≤ d ∧ m % d = 0)).foldl
        (fun acc d => acc + A008683b_Haux f (m / d)) 0

def A008683b_H (n : Nat) : Nat := A008683b_Haux n n

theorem A008683b_tables :
    (List.range 15).map A008683b_mu = [1, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1] ∧
    (List.range 15).map A008683b_H = [1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 8, 1, 3] := by
  decide +kernel

theorem A008683b_check :
    ∀ n, n < 11 → 2 ≤ n →
      A008683b_det (A008683b_m1 n) n = A008683b_mu n ∧
      A008683b_cnt (A008683b_m1 n) n = A008683b_H n ∧
      A008683b_det (A008683b_m2 n) n = A008683b_mu n ∧
      A008683b_cnt (A008683b_m2 n) n = A008683b_H n := by
  decide +kernel
