/-
OEIS A226661: least k > 0 such that the 3x+k map T_k (x/2 for even x,
(3x+k)/2 for odd x, k odd) has a primitive cycle of positive integers with
exactly n odd elements. Conjecture: a(n) > 0 for all n ≥ 1. True.

Construction: take m ≥ 1 with 2^(n+m) > 3^n and gcd(3^n - 2^n, 2^m - 1) = 1,
k = 2^(n+m) - 3^n (odd, prime to 3), B = 2^m - 1, y_j = 3^j 2^(n-j) B and
x_j = y_j - k (0 ≤ j ≤ n). For j < n, x_j is odd and T_k(x_j) = x_(j+1);
x_n = 2^m (3^n - 2^n), and m halvings return to x_0 = 3^n - 2^n. The odd
elements x_0 < ... < x_(n-1) are distinct, the even ones are
2^i (3^n - 2^n), 1 ≤ i ≤ m: a cycle with exactly n odd elements. The gcd of
its elements divides x_0 and 2 x_1 - 3 x_0 = k, and
gcd(x_0, k) = gcd(3^n - 2^n, 2^n (2^m - 1)) = gcd(3^n - 2^n, 2^m - 1) = 1.
Such m exists: any prime m > 3^n / 2 works, because every prime factor q of
2^m - 1 has ord_q(2) = m, so q ≡ 1 (mod m) and q > 3^n > 3^n - 2^n.

Checked here (core Lean): for all n ≥ 1 and m with 3^n < 2^(n+m):
`step` (x_j odd and T_k x_j = x_(j+1), j < n), `top` (x_n = 2^m (3^n - 2^n)),
`halve` (the even part of the cycle returns to x_0), `x0_eq`; and
`choice_small`, explicit m for 1 ≤ n ≤ 30 with 2^(n+m) > 3^n and
gcd(3^n - 2^n, 2^m - 1) = 1, by `decide`.
Not checked here: that k is prime to 3 (3 does not divide 2^(n+m)); existence
of a suitable m for n > 30 (the prime-m argument
above needs infinitely many primes and Fermat's little theorem), and the
identity gcd(x_0, k) = gcd(3^n - 2^n, 2^m - 1) (Euclid steps above).
-/

def T (k x : Nat) : Nat := if x % 2 = 0 then x / 2 else (3 * x + k) / 2

def y (n m j : Nat) : Nat := 3 ^ j * 2 ^ (n - j) * (2 ^ m - 1)
def kk (n m : Nat) : Nat := 2 ^ (n + m) - 3 ^ n

theorem pow3_odd (n : Nat) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem k_odd (n m : Nat) (hm : 1 ≤ m) (h : 3 ^ n < 2 ^ (n + m)) : kk n m % 2 = 1 := by
  have h2 : 2 ^ (n + m) % 2 = 0 := by
    rw [show n + m = (n + m - 1) + 1 by omega, Nat.pow_succ]; exact Nat.mul_mod_left _ 2
  have := pow3_odd n
  unfold kk; omega

theorem y_ge (n m j : Nat) (hj : j ≤ n) : 2 ^ n * (2 ^ m - 1) ≤ y n m j := by
  unfold y
  apply Nat.mul_le_mul_right
  have h1 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by decide) j
  have h2 : 2 ^ n = 2 ^ j * 2 ^ (n - j) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h2]
  exact Nat.mul_le_mul_right _ h1

theorem k_le_y (n m j : Nat) (hj : j ≤ n) : kk n m ≤ y n m j := by
  have := y_ge n m j hj
  have e : 2 ^ n * (2 ^ m - 1) = 2 ^ (n + m) - 2 ^ n := by
    rw [Nat.mul_sub, Nat.mul_one, Nat.pow_add]
  have h3 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
  unfold kk; omega

theorem step (n m j : Nat) (hm : 1 ≤ m) (h : 3 ^ n < 2 ^ (n + m)) (hj : j < n) :
    (y n m j - kk n m) % 2 = 1 ∧ T (kk n m) (y n m j - kk n m) = y n m (j + 1) - kk n m := by
  have hle := k_le_y n m j (by omega)
  have hko := k_odd n m hm h
  have e1 : y n m j = 2 * (3 ^ j * 2 ^ (n - (j + 1)) * (2 ^ m - 1)) := by
    unfold y
    rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ (n - (j + 1))) 2, ← Nat.mul_assoc, Nat.mul_comm (3 ^ j) 2,
      Nat.mul_assoc 2, Nat.mul_assoc 2, Nat.mul_assoc]
  have e2 : y n m (j + 1) = 3 * (3 ^ j * 2 ^ (n - (j + 1)) * (2 ^ m - 1)) := by
    unfold y
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc 3, Nat.mul_assoc 3, Nat.mul_assoc]
  rw [e1] at hle ⊢
  rw [e2]
  generalize 3 ^ j * 2 ^ (n - (j + 1)) * (2 ^ m - 1) = A at *
  generalize kk n m = k at *
  have hodd : (2 * A - k) % 2 = 1 := by omega
  refine ⟨hodd, ?_⟩
  unfold T
  simp only [show ¬ ((2 * A - k) % 2 = 0) by omega, ↓reduceIte]
  omega

theorem top (n m : Nat) (h : 3 ^ n < 2 ^ (n + m)) :
    y n m n - kk n m = 2 ^ m * (3 ^ n - 2 ^ n) := by
  unfold y kk
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
  have h3 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
  have e1 : 3 ^ n * (2 ^ m - 1) = 3 ^ n * 2 ^ m - 3 ^ n := by rw [Nat.mul_sub, Nat.mul_one]
  have e2 : 2 ^ m * (3 ^ n - 2 ^ n) = 3 ^ n * 2 ^ m - 2 ^ (n + m) := by
    rw [Nat.mul_sub, Nat.pow_add, Nat.mul_comm (2 ^ m) (3 ^ n), Nat.mul_comm (2 ^ m) (2 ^ n)]
  have h4 : 2 ^ (n + m) ≤ 3 ^ n * 2 ^ m := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h3
  have h5 : 3 ^ n ≤ 3 ^ n * 2 ^ m := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
  omega

theorem halve (k i c : Nat) : T k (2 ^ (i + 1) * c) = 2 ^ i * c := by
  unfold T
  have e : 2 ^ (i + 1) * c = 2 * (2 ^ i * c) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]
  rw [e]
  simp only [Nat.mul_mod_right, ↓reduceIte]
  omega

theorem x0_eq (n m : Nat) (h : 3 ^ n < 2 ^ (n + m)) : y n m 0 - kk n m = 3 ^ n - 2 ^ n := by
  unfold y kk
  simp only [Nat.pow_zero, Nat.one_mul, Nat.sub_zero]
  have h3 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
  have e : 2 ^ n * (2 ^ m - 1) = 2 ^ (n + m) - 2 ^ n := by
    rw [Nat.mul_sub, Nat.mul_one, Nat.pow_add]
  omega

def ms : List Nat := [1, 2, 2, 3, 3, 5, 5, 5, 6, 6, 7, 10, 8, 9, 9, 10, 10, 11, 12, 13,
  13, 13, 14, 17, 15, 17, 16, 17, 17, 19]

theorem choice_small : (List.range 30).all (fun i =>
    let n := i + 1
    let m := ms.getD i 0
    decide (1 ≤ m) && decide (3 ^ n < 2 ^ (n + m)) && Nat.gcd (3 ^ n - 2 ^ n) (2 ^ m - 1) == 1) = true := by
  decide +kernel
