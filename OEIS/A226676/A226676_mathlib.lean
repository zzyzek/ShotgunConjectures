/-
OEIS A226676, Mathlib proof.

A226676(N) = least k > 0 such that the 3x-k map T_k (x/2 for even x,
(3x-k)/2 for odd x) has a primitive cycle of exactly N positive integers
(0 if there is none). A cycle is primitive if the gcd of its elements is 1.
Conjecture: a(N) > 0 for N > 2.

Main theorem `A226676_main`: for every N ≥ 3 there are k > 0 (odd, prime to
3) and x₀ > 0 such that, for the map `A226676_T k`,
* x₀ is periodic with minimal period exactly N (`Function.minimalPeriod`),
  so its orbit {T^[j] x₀ : j < N} is a cycle of N distinct elements;
* all N elements are positive;
* the gcd of the N elements is 1 (primitive).
Hence a(N) > 0, the README result (an upper bound for a(N), not its value).
`A226676_T k x` uses natural-number subtraction; on the cycle 3x ≥ k, so
it agrees with (3x - k)/2 over ℤ there.

Construction: n = N - 1, k = 3^n - 2^(n+1), x_j = k + 3^j 2^(n-j).
Nothing is outside Lean.
-/
import Mathlib

/-- The 3x-k map. -/
def A226676_T (k x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (3 * x - k) / 2

def A226676_x (k n j : ℕ) : ℕ := k + 3 ^ j * 2 ^ (n - j)

theorem A226676_pow_gt (n : ℕ) (h : 2 ≤ n) : 2 ^ (n + 1) < 3 ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have : m = 1 := by omega
      subst this; decide
    · have := ih hm
      rw [Nat.pow_succ, Nat.pow_succ 3]
      omega

theorem A226676_pow3_odd (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem A226676_k_odd (n : ℕ) (h : 2 ≤ n) : (3 ^ n - 2 ^ (n + 1)) % 2 = 1 := by
  have h1 := A226676_pow_gt n h
  have h2 := A226676_pow3_odd n
  have h3 : 2 ^ (n + 1) % 2 = 0 := by rw [Nat.pow_succ]; exact Nat.mul_mod_left _ 2
  omega

theorem A226676_k_mod3 (n : ℕ) (h : 2 ≤ n) : (3 ^ n - 2 ^ (n + 1)) % 3 ≠ 0 := by
  have h1 := A226676_pow_gt n h
  have h2 : 3 ^ n % 3 = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.pow_succ]; exact Nat.mul_mod_left _ 3
  have h3 : 2 ^ (n + 1) % 3 = 1 ∨ 2 ^ (n + 1) % 3 = 2 := by
    have : ¬ 3 ∣ 2 ^ (n + 1) := fun h =>
      absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
    omega
  omega

theorem A226676_step (k n j : ℕ) (hk : k % 2 = 1) (hj : j < n) :
    A226676_x k n j % 2 = 1 ∧ A226676_T k (A226676_x k n j) = A226676_x k n (j + 1) := by
  have e1 : 2 ^ (n - j) = 2 * 2 ^ (n - (j + 1)) := by
    rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have e2 : 3 ^ j * 2 ^ (n - j) = 2 * (3 ^ j * 2 ^ (n - (j + 1))) := by
    rw [e1, Nat.mul_left_comm]
  have e3 : 3 ^ (j + 1) * 2 ^ (n - (j + 1)) = 3 * (3 ^ j * 2 ^ (n - (j + 1))) := by
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]
  unfold A226676_x A226676_T
  rw [e2, e3]
  generalize 3 ^ j * 2 ^ (n - (j + 1)) = A
  have hodd : (k + 2 * A) % 2 = 1 := by omega
  refine ⟨hodd, ?_⟩
  simp only [show ¬ ((k + 2 * A) % 2 = 0) by omega, ↓reduceIte]
  omega

theorem A226676_close (n : ℕ) (h : 2 ≤ n) :
    A226676_x (3 ^ n - 2 ^ (n + 1)) n n % 2 = 0 ∧
    A226676_T (3 ^ n - 2 ^ (n + 1)) (A226676_x (3 ^ n - 2 ^ (n + 1)) n n) =
      A226676_x (3 ^ n - 2 ^ (n + 1)) n 0 := by
  have h1 := A226676_pow_gt n h
  have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold A226676_x A226676_T
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.one_mul]
  have hev : (3 ^ n - 2 ^ (n + 1) + 3 ^ n) % 2 = 0 := by omega
  refine ⟨hev, ?_⟩
  simp only [hev, ↓reduceIte]
  omega

/-- The orbit of x₀ = x_0 runs through x_0, ..., x_n and returns. -/
theorem A226676_iter (n : ℕ) (h : 2 ≤ n) :
    (∀ j, j ≤ n → (A226676_T (3 ^ n - 2 ^ (n + 1)))^[j] (A226676_x (3 ^ n - 2 ^ (n + 1)) n 0) =
      A226676_x (3 ^ n - 2 ^ (n + 1)) n j) ∧
    (A226676_T (3 ^ n - 2 ^ (n + 1)))^[n + 1] (A226676_x (3 ^ n - 2 ^ (n + 1)) n 0) =
      A226676_x (3 ^ n - 2 ^ (n + 1)) n 0 := by
  have hk := A226676_k_odd n h
  have hit : ∀ j, j ≤ n → (A226676_T (3 ^ n - 2 ^ (n + 1)))^[j]
      (A226676_x (3 ^ n - 2 ^ (n + 1)) n 0) = A226676_x (3 ^ n - 2 ^ (n + 1)) n j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih (by omega), (A226676_step _ n i hk (by omega)).2]
  refine ⟨hit, ?_⟩
  rw [Function.iterate_succ_apply', hit n le_rfl, (A226676_close n h).2]

/-- Minimal period from a period and no earlier return. -/
theorem A226676_minimalPeriod_eq {α : Type*} (f : α → α) (x : α) (N : ℕ) (hN : 0 < N)
    (hper : f^[N] x = x) (hne : ∀ j, 0 < j → j < N → f^[j] x ≠ x) :
    Function.minimalPeriod f x = N := by
  have hp : Function.IsPeriodicPt f N x := hper
  have hle := hp.minimalPeriod_le hN
  have hpos := hp.minimalPeriod_pos hN
  by_contra hc
  exact hne _ hpos (lt_of_le_of_ne hle hc) Function.iterate_minimalPeriod

/-- The construction for n ≥ 2: minimal period n + 1, positive elements, gcd 1. -/
theorem A226676_cycle (n : ℕ) (h : 2 ≤ n) :
    let k := 3 ^ n - 2 ^ (n + 1)
    let x₀ := A226676_x k n 0
    0 < k ∧ k % 2 = 1 ∧ k % 3 ≠ 0 ∧ 0 < x₀ ∧
    Function.minimalPeriod (A226676_T k) x₀ = n + 1 ∧
    (∀ j < n + 1, 0 < (A226676_T k)^[j] x₀) ∧
    (Finset.range (n + 1)).gcd (fun j => (A226676_T k)^[j] x₀) = 1 ∧
    ((Finset.range (n + 1)).filter (fun j => (A226676_T k)^[j] x₀ % 2 = 1)).card = n := by
  intro k x₀
  have h1 := A226676_pow_gt n h
  have hk := A226676_k_odd n h
  obtain ⟨hit, hper⟩ := A226676_iter n h
  have hpos : ∀ j, 0 < A226676_x k n j := fun j => by unfold A226676_x; omega
  have hx0 : x₀ = k + 2 ^ n := by simp [x₀, A226676_x]
  have hinc : ∀ j, 0 < j → j ≤ n → x₀ < A226676_x k n j := by
    intro j hj hjn
    rw [hx0]; unfold A226676_x
    have : 2 ^ j * 2 ^ (n - j) < 3 ^ j * 2 ^ (n - j) :=
      Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by norm_num) (by omega)) (by positivity)
    rw [← pow_add, Nat.add_sub_cancel' hjn] at this
    omega
  refine ⟨by omega, hk, A226676_k_mod3 n h, hpos 0, ?_, ?_, ?_, ?_⟩
  · apply A226676_minimalPeriod_eq _ _ _ (by omega) hper
    intro j hj hjN
    rw [hit j (by omega)]
    exact (hinc j hj (by omega)).ne'
  · intro j hj
    rw [hit j (by omega)]; exact hpos j
  · -- g divides x_0 and x_1; 3 x_0 = 2 x_1 + k, so g ∣ k and g ∣ 2^n; x_0 is odd.
    set g := (Finset.range (n + 1)).gcd (fun j => (A226676_T k)^[j] x₀)
    have hg0 : g ∣ x₀ := by
      have := Finset.gcd_dvd (s := Finset.range (n + 1))
        (f := fun j => (A226676_T k)^[j] x₀) (Finset.mem_range.2 (by omega : 0 < n + 1))
      simpa using this
    have hg1 : g ∣ A226676_x k n 1 := by
      have := Finset.gcd_dvd (s := Finset.range (n + 1))
        (f := fun j => (A226676_T k)^[j] x₀) (Finset.mem_range.2 (by omega : 1 < n + 1))
      rwa [hit 1 (by omega)] at this
    have e3 : 3 * x₀ = 2 * A226676_x k n 1 + k := by
      rw [hx0]; unfold A226676_x
      have : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      rw [this]; ring
    have hgk : g ∣ k := (Nat.dvd_add_right (Dvd.dvd.mul_left hg1 2)).1 (e3 ▸ Dvd.dvd.mul_left hg0 3)
    have hg2 : g ∣ 2 ^ n := (Nat.dvd_add_right hgk).1 (hx0 ▸ hg0)
    have hodd : Nat.Coprime x₀ (2 ^ n) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right]
      exact Nat.odd_iff.2 (A226676_step k n 0 hk (by omega)).1
    exact Nat.eq_one_of_dvd_one (hodd ▸ Nat.dvd_gcd hg0 hg2)
  · have : (Finset.range (n + 1)).filter (fun j => (A226676_T k)^[j] x₀ % 2 = 1) =
        Finset.range n := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hj, hodd⟩
        by_contra hjn
        have : j = n := by omega
        subst this
        rw [hit j le_rfl, (A226676_close j h).1] at hodd
        omega
      · intro hj
        exact ⟨by omega, by rw [hit j (by omega)]; exact (A226676_step k n j hk hj).1⟩
    rw [this, Finset.card_range]

theorem A226676_main (N : ℕ) (hN : 3 ≤ N) :
    ∃ k x₀ : ℕ, 0 < k ∧ 0 < x₀ ∧
      Function.minimalPeriod (A226676_T k) x₀ = N ∧
      (∀ j < N, 0 < (A226676_T k)^[j] x₀) ∧
      (Finset.range N).gcd (fun j => (A226676_T k)^[j] x₀) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨h1, -, -, h4, h5, h6, h7, -⟩ := A226676_cycle n (by omega)
  exact ⟨_, _, h1, h4, h5, h6, h7⟩
