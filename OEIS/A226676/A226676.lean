/-
OEIS A226676: least k > 0 such that the 3x-k map T_k (x/2 for even x,
(3x-k)/2 for odd x, k odd) has a primitive cycle of exactly N positive
integers. Conjecture: a(N) > 0 for N > 2. True.

Construction (N ≥ 3, n = N - 1 ≥ 2): k = 3^n - 2^(n+1) = 3^(N-1) - 2^N
(positive, odd, prime to 3), x_j = k + 3^j 2^(n-j) for 0 ≤ j ≤ n. For j < n,
x_j is odd and T_k(x_j) = x_(j+1); x_n = 2 (3^n - 2^n) is even and
T_k(x_n) = x_0 = 3^n - 2^n. The x_j (j < n) increase strictly and x_n is even,
so the cycle has exactly n + 1 = N elements. Primitive: the gcd of the
elements divides x_0 and k, and gcd(3^n - 2^n, 3^n - 2^(n+1)) =
gcd(3^n - 2^n, 2^n) = 1 since 3^n - 2^n is odd. (Same construction as
OEIS-A226677, read by cycle length.)

Checked here (core Lean, for all n ≥ 2): `k_pos`, `k_odd`, `k_mod3`, `step`,
`close`, `x0_eq`; and `primitive_small`, gcd(x_0, k) = 1 for 2 ≤ n ≤ 40.
Not checked here: gcd(x_0, k) = 1 for n > 40 (one line above), and the
strict increase of x_j.
-/

def T (k x : Nat) : Nat := if x % 2 = 0 then x / 2 else (3 * x - k) / 2

def x (k n j : Nat) : Nat := k + 3 ^ j * 2 ^ (n - j)

theorem pow_gt (n : Nat) (h : 2 ≤ n) : 2 ^ (n + 1) < 3 ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have : m = 1 := by omega
      subst this; decide
    · have := ih hm
      rw [Nat.pow_succ, Nat.pow_succ 3]
      omega

theorem pow3_odd (n : Nat) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem pow3_mod3 (n : Nat) (h : 1 ≤ n) : 3 ^ n % 3 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.pow_succ]; exact Nat.mul_mod_left _ 3

theorem pow2_mod3 (n : Nat) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => decide
  | succ m ih => rw [Nat.pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> decide

theorem k_pos (n : Nat) (h : 2 ≤ n) : 0 < 3 ^ n - 2 ^ (n + 1) := by
  have := pow_gt n h; omega

theorem k_odd (n : Nat) (h : 2 ≤ n) : (3 ^ n - 2 ^ (n + 1)) % 2 = 1 := by
  have h1 := pow_gt n h
  have h2 := pow3_odd n
  have h3 : 2 ^ (n + 1) % 2 = 0 := by rw [Nat.pow_succ]; exact Nat.mul_mod_left _ 2
  omega

theorem k_mod3 (n : Nat) (h : 2 ≤ n) : (3 ^ n - 2 ^ (n + 1)) % 3 ≠ 0 := by
  have h1 := pow_gt n h
  have h2 := pow3_mod3 n (by omega)
  have h3 := pow2_mod3 (n + 1)
  omega

theorem step (k n j : Nat) (hk : k % 2 = 1) (hj : j < n) :
    x k n j % 2 = 1 ∧ T k (x k n j) = x k n (j + 1) := by
  have e1 : 2 ^ (n - j) = 2 * 2 ^ (n - (j + 1)) := by
    rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have e2 : 3 ^ j * 2 ^ (n - j) = 2 * (3 ^ j * 2 ^ (n - (j + 1))) := by
    rw [e1, Nat.mul_left_comm]
  have e3 : 3 ^ (j + 1) * 2 ^ (n - (j + 1)) = 3 * (3 ^ j * 2 ^ (n - (j + 1))) := by
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]
  unfold x T
  rw [e2, e3]
  generalize 3 ^ j * 2 ^ (n - (j + 1)) = A
  have hodd : (k + 2 * A) % 2 = 1 := by omega
  refine ⟨hodd, ?_⟩
  simp only [show ¬ ((k + 2 * A) % 2 = 0) by omega, ↓reduceIte]
  omega

theorem close (n : Nat) (h : 2 ≤ n) :
    let k := 3 ^ n - 2 ^ (n + 1)
    x k n n % 2 = 0 ∧ T k (x k n n) = x k n 0 := by
  intro k
  have h1 := pow_gt n h
  have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold x T
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.one_mul]
  have hk : k = 3 ^ n - 2 ^ (n + 1) := rfl
  have hev : (k + 3 ^ n) % 2 = 0 := by omega
  refine ⟨hev, ?_⟩
  simp only [hev, ↓reduceIte]
  omega

theorem x0_eq (n : Nat) (h : 2 ≤ n) : x (3 ^ n - 2 ^ (n + 1)) n 0 = 3 ^ n - 2 ^ n := by
  have h1 := pow_gt n h
  have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold x
  simp only [Nat.pow_zero, Nat.one_mul, Nat.sub_zero]
  omega

theorem primitive_small : (List.range 39).all (fun i =>
    Nat.gcd (3 ^ (i + 2) - 2 ^ (i + 2)) (3 ^ (i + 2) - 2 ^ (i + 3)) == 1) = true := by decide +kernel
