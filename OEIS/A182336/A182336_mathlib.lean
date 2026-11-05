/-
OEIS A182336, Mathlib proof of C. R. Greathouse IV's conjecture (2012).

a(n) = least m ≥ n with Hamming distance D(n, m) = popcount(n XOR m) = 4 (offset 0).
`A182336_pc` is the binary digit sum (structural recursion with fuel), `A182336_D n m` =
`A182336_pc (n ^^^ m)`, `A182336_a n` = `Nat.find` of {m | n ≤ m ∧ D(n, m) = 4}.

Main theorem `A182336_main`: for every n > 96, n + 1 ≤ a(n) ≤ 9n/8 + 1 (⌊9n/8⌋ in ℕ, the same
thing for an integer a(n)).
`A182336_data`: a(0..22) are the OEIS data terms. `A182336_96`: a(96) = 111 > 9·96/8 + 1 = 109,
so the threshold 96 cannot be lowered.

Proof. Lower bound: D(n, n) = 0. Upper bound: an explicit m with D(n, m) = 4 and
8(m - n) ≤ n + 8. Bits split over blocks (`A182336_D_lift`:
D(2^K a + s, 2^K b + t) = D(a, b) + D(s, t) for s, t < 2^K). Write n = 64q + r.
* r < 56 (one of bits 3, 4, 5 of n is 0): a table over r < 56 (`A182336_table`, decide) gives
  r < r' < 64 with r' ≤ r + 15 and D(r, r') = 4; m = 64q + r' works once n ≥ 112.
* r ≥ 56: let u = ⌊n/8⌋ and u + 1 = 2^j w with w = 2H + 1 odd, j ≥ 3. Then
  n = 2^j (16H + 7) + s and m = n + 2^j = 2^j (16H + 8) + s with s < 2^j, so
  D(n, m) = D(7, 8) = 4, and 8·2^j ≤ 8(u + 1) ≤ n + 8.
* 97 ≤ n < 112: finite check (`A182336_small`, decide).

Not checked in Lean: nothing for the statement above.
-/
import Mathlib

/-- Binary digit sum with explicit fuel. -/
def A182336_pcF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => n % 2 + A182336_pcF k (n / 2)

/-- popcount (fuel n suffices since n < 2^n). -/
def A182336_pc (n : ℕ) : ℕ := A182336_pcF n n

/-- Hamming distance of the binary expansions. -/
def A182336_D (n m : ℕ) : ℕ := A182336_pc (n ^^^ m)

theorem A182336_pcF_zero (k : ℕ) : A182336_pcF k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [A182336_pcF, ih]

theorem A182336_pcF_stable (k : ℕ) : ∀ n j, n < 2 ^ k → A182336_pcF (k + j) n = A182336_pcF k n := by
  induction k with
  | zero =>
    intro n j hn
    have : n = 0 := by simpa using hn
    subst this
    rw [A182336_pcF_zero, A182336_pcF_zero]
  | succ k ih =>
    intro n j hn
    rw [show k + 1 + j = (k + j) + 1 by omega, A182336_pcF, A182336_pcF,
      ih (n / 2) j (by rw [pow_succ] at hn; omega)]

theorem A182336_pc_eq {n k : ℕ} (hn : n < 2 ^ k) : A182336_pc n = A182336_pcF k n := by
  unfold A182336_pc
  have hn' : n < 2 ^ n := Nat.lt_two_pow_self
  rcases le_total k n with h | h
  · have := A182336_pcF_stable k n (n - k) hn
    rw [show k + (n - k) = n by omega] at this
    exact this
  · have := A182336_pcF_stable n n (k - n) hn'
    rw [show n + (k - n) = k by omega] at this
    exact this.symm

theorem A182336_pcF_add (K : ℕ) : ∀ (k a s : ℕ), s < 2 ^ K →
    A182336_pcF (K + k) (2 ^ K * a + s) = A182336_pcF K s + A182336_pcF k a := by
  induction K with
  | zero =>
    intro k a s hs
    have : s = 0 := by simpa using hs
    subst this
    simp [A182336_pcF_zero]
  | succ K ih =>
    intro k a s hs
    rw [show K + 1 + k = (K + k) + 1 by omega, A182336_pcF, A182336_pcF]
    have h1 : 2 ^ (K + 1) * a + s = 2 * (2 ^ K * a) + s := by ring
    have h2 : (2 ^ (K + 1) * a + s) % 2 = s % 2 := by rw [h1]; omega
    have h3 : (2 ^ (K + 1) * a + s) / 2 = 2 ^ K * a + s / 2 := by rw [h1]; omega
    rw [h2, h3, ih k a (s / 2) (by rw [pow_succ] at hs; omega)]
    ring

/-- popcount is additive over a block split. -/
theorem A182336_pc_add {K a s : ℕ} (hs : s < 2 ^ K) :
    A182336_pc (2 ^ K * a + s) = A182336_pc a + A182336_pc s := by
  have ha : a < 2 ^ a := Nat.lt_two_pow_self
  have hlt : 2 ^ K * a + s < 2 ^ (K + a) := by
    rw [pow_add]
    have : 2 ^ K * a + s < 2 ^ K * (a + 1) := by rw [mul_add, mul_one]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ ha)
  rw [A182336_pc_eq hlt, A182336_pcF_add K a a s hs, ← A182336_pc_eq hs, ← A182336_pc_eq ha]
  ring

theorem A182336_xor_lift {K a b s t : ℕ} (hs : s < 2 ^ K) (ht : t < 2 ^ K) :
    (2 ^ K * a + s) ^^^ (2 ^ K * b + t) = 2 ^ K * (a ^^^ b) + (s ^^^ t) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hs, Nat.testBit_two_pow_mul_add _ ht,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hs ht)]
  split_ifs <;> simp [Nat.testBit_xor]

/-- Hamming distance is additive over a block split. -/
theorem A182336_D_lift {K s t : ℕ} (a b : ℕ) (hs : s < 2 ^ K) (ht : t < 2 ^ K) :
    A182336_D (2 ^ K * a + s) (2 ^ K * b + t) = A182336_D a b + A182336_D s t := by
  unfold A182336_D
  rw [A182336_xor_lift hs ht, A182336_pc_add (Nat.xor_lt_two_pow hs ht)]

theorem A182336_D_self (n : ℕ) : A182336_D n n = 0 := by
  simp [A182336_D, A182336_pc, A182336_pcF_zero]

theorem A182336_ex (n : ℕ) : ∃ m, n ≤ m ∧ A182336_D n m = 4 := by
  refine ⟨2 ^ n * 15 + n, by omega, ?_⟩
  have h := A182336_D_lift (K := n) 0 15 Nat.lt_two_pow_self Nat.lt_two_pow_self
  rw [mul_zero, zero_add] at h
  rw [h, A182336_D_self]
  decide

/-- a(n) = least m ≥ n with D(n, m) = 4. -/
def A182336_a (n : ℕ) : ℕ := Nat.find (A182336_ex n)

theorem A182336_a_eq_of {n v : ℕ} (h1 : n ≤ v) (h2 : A182336_D n v = 4)
    (h3 : ∀ m < v, n ≤ m → A182336_D n m ≠ 4) : A182336_a n = v := by
  rw [A182336_a, Nat.find_eq_iff]
  exact ⟨⟨h1, h2⟩, fun m hm h => h3 m hm h.1 h.2⟩

/-- The OEIS data list a(0..22). -/
def A182336_L : List ℕ :=
  [15, 14, 13, 12, 11, 10, 9, 8, 19, 18, 17, 16, 17, 16, 16, 17, 31, 30, 29, 28, 27, 26, 25]

theorem A182336_check : ∀ i < 23, i ≤ A182336_L.getD i 0 ∧ A182336_D i (A182336_L.getD i 0) = 4 ∧
    ∀ m < A182336_L.getD i 0, i ≤ m → A182336_D i m ≠ 4 := by
  decide +kernel

theorem A182336_data : ∀ i < 23, A182336_a i = A182336_L.getD i 0 := by
  intro i hi
  obtain ⟨h1, h2, h3⟩ := A182336_check i hi
  exact A182336_a_eq_of h1 h2 h3

theorem A182336_96 : A182336_a 96 = 111 ∧ 9 * 96 / 8 + 1 < 111 := by
  refine ⟨A182336_a_eq_of (by norm_num) (by decide) ?_, by norm_num⟩
  have : ∀ m < 111, 96 ≤ m → A182336_D 96 m ≠ 4 := by decide +kernel
  exact this

theorem A182336_table : ∀ r < 56, ∃ r' < 64, r < r' ∧ r' ≤ r + 15 ∧ A182336_D r r' = 4 := by
  decide +kernel

theorem A182336_small : ∀ n < 112, 96 < n →
    ∃ m < 130, n ≤ m ∧ A182336_D n m = 4 ∧ 8 * m ≤ 9 * n + 8 := by
  decide +kernel

theorem A182336_upper {n : ℕ} (hn : 96 < n) :
    ∃ m, n ≤ m ∧ A182336_D n m = 4 ∧ 8 * m ≤ 9 * n + 8 := by
  rcases lt_or_ge n 112 with hsmall | hbig
  · obtain ⟨m, -, hm⟩ := A182336_small n hsmall hn
    exact ⟨m, hm⟩
  have hn64 : n = 2 ^ 6 * (n / 64) + n % 64 := by omega
  have hr64 : n % 64 < 2 ^ 6 := by
    have := Nat.mod_lt n (by norm_num : 64 > 0)
    norm_num
    omega
  rcases lt_or_ge (n % 64) 56 with hr | hr
  · obtain ⟨r', hr'64, hlt, hle, hD⟩ := A182336_table (n % 64) hr
    refine ⟨2 ^ 6 * (n / 64) + r', by omega, ?_, by omega⟩
    have e : A182336_D (2 ^ 6 * (n / 64) + n % 64) (2 ^ 6 * (n / 64) + r') =
        A182336_D (n / 64) (n / 64) + A182336_D (n % 64) r' :=
      A182336_D_lift _ _ hr64 (by norm_num; omega)
    rw [← hn64, A182336_D_self] at e
    rw [e, hD]
  · set u := n / 8 with hu
    have hu7 : u % 8 = 7 := by omega
    obtain ⟨j, w, hw, hjw⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := u + 1) (by omega) 2
      (by norm_num)
    have hwo : w % 2 = 1 := by omega
    rcases j with _ | _ | _ | j
    · simp at hjw
      omega
    · simp at hjw
      omega
    · rw [show 2 ^ (0 + 1 + 1) = 4 by norm_num] at hjw
      omega
    · set X := 2 ^ (j + 1 + 1 + 1) with hX
      have hX8 : 8 ≤ X := by
        rw [hX, show j + 1 + 1 + 1 = j + 3 by ring, pow_add]
        have : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
        norm_num
        omega
      set H := w / 2 with hH
      have hw2 : w = 2 * H + 1 := by omega
      set t := n % 8 with ht
      have hn8 : n = 8 * u + t := by omega
      have hY1 : X * w = 2 * (X * H) + X := by rw [hw2]; ring
      have hs : X - 8 + t < X := by omega
      refine ⟨X * (16 * H + 8) + (X - 8 + t), ?_, ?_, ?_⟩
      · have : X * (16 * H + 8) = 16 * (X * H) + 8 * X := by ring
        omega
      · have e : n = X * (16 * H + 7) + (X - 8 + t) := by
          have : X * (16 * H + 7) = 16 * (X * H) + 7 * X := by ring
          omega
        have hs' : 2 ^ (j + 1 + 1 + 1) - 8 + t < 2 ^ (j + 1 + 1 + 1) := by rw [← hX]; exact hs
        rw [e, hX, A182336_D_lift _ _ hs' hs', A182336_D_self,
          show 16 * H + 7 = 2 ^ 4 * H + 7 by norm_num,
          show 16 * H + 8 = 2 ^ 4 * H + 8 by norm_num,
          A182336_D_lift _ _ (by norm_num) (by norm_num), A182336_D_self]
        decide
      · have : X * (16 * H + 8) = 16 * (X * H) + 8 * X := by ring
        omega

theorem A182336_main (n : ℕ) (hn : 96 < n) :
    n + 1 ≤ A182336_a n ∧ A182336_a n ≤ 9 * n / 8 + 1 := by
  have hspec := Nat.find_spec (A182336_ex n)
  constructor
  · have hne : Nat.find (A182336_ex n) ≠ n := by
      intro h
      rw [h, A182336_D_self] at hspec
      exact absurd hspec.2 (by norm_num)
    unfold A182336_a
    omega
  · obtain ⟨m, hm1, hm2, hm3⟩ := A182336_upper hn
    have : A182336_a n ≤ m := Nat.find_min' (A182336_ex n) ⟨hm1, hm2⟩
    omega
