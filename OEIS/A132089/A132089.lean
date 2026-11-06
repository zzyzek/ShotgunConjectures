/-
OEIS A132089: triangle T = L^2, the matrix square of Losanitsch's triangle
L = A034851, L(n, k) = (C(n, k) + C(n mod 2, k mod 2) C(n div 2, k div 2))/2.
Conjectures in the entry: (1) the first column of T equals the row sums of
L (which are A005418); (2) the first column of L^(m+1) equals the row sums
of L^m.

`A132089_L` is L (the PARI formula in the entry), `A132089_pow m` is L^m
as a lower-triangular array (row n of L^(m+1) sums over j = 0..n, which is
the full matrix product because L^m(n, j) = 0 for j > n, see
`A132089_pow_upper`).

Main theorem `A132089_main` (conjecture 2, for every m ≥ 0, which contains
conjecture 1 as m = 1): L^(m+1)(n, 0) = sum_{k=0..n} L^m(n, k). Reason:
L(j, 0) = 1 for every j (`A132089_L_col0`).

Also checked by `decide`: `A132089_data`, the 65 listed terms of
A132089 equal L^2 (rows 0..9 and row 10 minus its last entry); `A132089_A005418`: row sums of L equal
2^(n-1) + 2^(floor((n+1)/2) - 1) = A005418(n+1) for 1 ≤ n ≤ 40 (the
general identity is the known name of A005418, not proved here).
-/

/-- Binomial coefficient (Pascal recursion). -/
def A132089_choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => A132089_choose n k + A132089_choose n (k + 1)

theorem A132089_choose_zero_right (n : Nat) : A132089_choose n 0 = 1 := by
  cases n <;> rfl

theorem A132089_choose_gt : ∀ n k, n < k → A132089_choose n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    simp only [A132089_choose]
    rw [A132089_choose_gt n k (by omega), A132089_choose_gt n (k + 1) (by omega)]

/-- Losanitsch's triangle A034851. -/
def A132089_L (n k : Nat) : Nat :=
  (A132089_choose n k + A132089_choose (n % 2) (k % 2) * A132089_choose (n / 2) (k / 2)) / 2

/-- Sum of f j for j = 0..n-1. -/
def A132089_sum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => A132089_sum f n + f n

/-- L^m as a lower-triangular array. -/
def A132089_pow : Nat → Nat → Nat → Nat
  | 0, n, k => if n = k then 1 else 0
  | m + 1, n, k => A132089_sum (fun j => A132089_pow m n j * A132089_L j k) (n + 1)

theorem A132089_L_col0 (j : Nat) : A132089_L j 0 = 1 := by
  simp [A132089_L, A132089_choose_zero_right]

theorem A132089_L_upper (n k : Nat) (h : n < k) : A132089_L n k = 0 := by
  unfold A132089_L
  rw [A132089_choose_gt n k h]
  rcases Nat.lt_or_ge (n / 2) (k / 2) with h2 | h2
  · rw [A132089_choose_gt _ _ h2]; simp
  · have hn : n % 2 = 0 := by omega
    have hk2 : k % 2 = 1 := by omega
    rw [hn, hk2, A132089_choose_gt 0 1 (by omega)]; simp

theorem A132089_sum_zero (f : Nat → Nat) (h : ∀ j, f j = 0) : ∀ n, A132089_sum f n = 0
  | 0 => rfl
  | n + 1 => by simp [A132089_sum, A132089_sum_zero f h n, h n]

theorem A132089_sum_congr (f g : Nat → Nat) : ∀ n, (∀ j, j < n → f j = g j) →
    A132089_sum f n = A132089_sum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [A132089_sum]
    rw [A132089_sum_congr f g n (fun j hj => h j (by omega)), h n (by omega)]

/-- L^m is lower triangular, so the finite sums are the matrix product. -/
theorem A132089_pow_upper : ∀ m n k, n < k → A132089_pow m n k = 0
  | 0, n, k, h => by simp [A132089_pow]; omega
  | m + 1, n, k, h => by
    simp only [A132089_pow]
    apply A132089_sum_zero
    intro j
    rcases Nat.lt_or_ge n j with hj | hj
    · rw [A132089_pow_upper m n j hj]; simp
    · rw [A132089_L_upper j k (by omega)]; simp

/-- Conjecture (2), and (1) at m = 1: the first column of L^(m+1) is the
row-sum sequence of L^m. -/
theorem A132089_main (m n : Nat) :
    A132089_pow (m + 1) n 0 = A132089_sum (fun k => A132089_pow m n k) (n + 1) := by
  simp only [A132089_pow]
  apply A132089_sum_congr
  intro j _
  rw [A132089_L_col0, Nat.mul_one]

/-- The listed data of A132089 (65 terms: rows 0..9 and row 10 without its last entry) is L^2. -/
theorem A132089_data :
    ((List.range 11).flatMap (fun n => (List.range (n + 1)).map (A132089_pow 2 n))).take 65 =
    [1,2,1,3,2,1,6,6,4,1,10,12,12,4,1,20,30,36,18,6,1,36,62,92,56,27,6,1,
     72,144,246,188,110,36,8,1,136,304,600,536,380,152,48,8,1,272,680,
     1504,1576,1296,644,248,60,10,1,528,1448,3576,4256,4008,2332,1080,320,75,10] := by
  decide +kernel

/-- Row sums of L are A005418(n+1) = 2^(n-1) + 2^(floor((n+1)/2) - 1), 1 ≤ n ≤ 40. -/
theorem A132089_A005418 :
    ∀ n, n < 41 → 1 ≤ n →
      A132089_sum (fun k => A132089_L n k) (n + 1) = 2 ^ (n - 1) + 2 ^ ((n + 1) / 2 - 1) := by
  decide +kernel
