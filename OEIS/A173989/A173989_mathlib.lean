/-
OEIS A173989 (offset 1): a(n) is the 2-adic valuation of A173300(n), where
A173300(n) is the denominator of x^n + y^n, x = (1+√3)/2, y = (1-√3)/2
(Maple and PARI programs of A173989).  Conjecture (entry text): the terms
follow the pattern A, A, A+1, A with A odd (data: 0, 0, then 1,1,2,1,
3,3,4,3, ... from n = 3 on).

Definitions.
* `s n` : ℤ, s 0 = 2, s 1 = 2, s (n+2) = 2 s (n+1) + 2 s n.
  `s_real`: (s n : ℝ) = (1+√3)^n + (1-√3)^n.
* `A173300 n = ((s n : ℚ) / 2^n).den`; `A173300_real`: that rational, cast
  to ℝ, equals ((1+√3)/2)^n + ((1-√3)/2)^n.  So `A173300 n` is the
  denominator of x^n + y^n, as in the entry.
* `A173989 n = padicValNat 2 (A173300 n)`.

Main theorems.
* `A173989_closed`: for every j ≥ 0,
  a(4j+3) = 2j+1, a(4j+4) = 2j+1, a(4j+5) = 2j+2, a(4j+6) = 2j+1.
* `A173989_pattern`: for every j there is an odd A with
  (a(4j+3), a(4j+4), a(4j+5), a(4j+6)) = (A, A, A+1, A) (the conjecture).
* `A173989_one`, `A173989_two`: a(1) = a(2) = 0.

Proof.  (1+√3)^2 = 2(2+√3), so s(2m) = 2^m T_m and s(2m+1) = 2^m U_m with
T_0 = U_0 = 2, T_{m+1} = T_m + U_m, U_{m+1} = 2T_m + 3U_m.  Induction on m
gives T_{2m} ≡ 2 (mod 4), T_{2m+1} ≡ 4 (mod 8), U_m ≡ 2 (mod 4).  Hence
v2(s(4j)) = 2j+1, v2(s(4j+1)) = 2j+1, v2(s(4j+2)) = 2j+3, v2(s(4j+3)) = 2j+2,
and when s n = 2^e u with u odd and e ≤ n, s n / 2^n = u / 2^(n-e) in lowest
terms, so a(n) = n - e.

Not checked in this file: that the definitions reproduce the OEIS data
terms beyond what the theorems state (certificate/check.py compares
a(1..10000) numerically with the closed form).
-/
import Mathlib

/-- s n = (1+√3)^n + (1-√3)^n, by its integer recurrence. -/
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | (n + 2) => 2 * s (n + 1) + 2 * s n

theorem s_succ_succ (n : ℕ) : s (n + 2) = 2 * s (n + 1) + 2 * s n := rfl

theorem s_real_pair (n : ℕ) :
    (s n : ℝ) = (1 + √3) ^ n + (1 - √3) ^ n ∧
      (s (n + 1) : ℝ) = (1 + √3) ^ (n + 1) + (1 - √3) ^ (n + 1) := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [s]
      norm_num
    · simp [s]
      ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [s_succ_succ]
    push_cast
    rw [ih.1, ih.2]
    linear_combination (-((1 + √3) ^ n + (1 - √3) ^ n)) * h3

theorem s_real (n : ℕ) : (s n : ℝ) = (1 + √3) ^ n + (1 - √3) ^ n := (s_real_pair n).1

/-- A173300(n) = denominator of ((1+√3)/2)^n + ((1-√3)/2)^n. -/
def A173300 (n : ℕ) : ℕ := ((s n : ℚ) / 2 ^ n).den

theorem A173300_real (n : ℕ) :
    ((((s n : ℚ) / 2 ^ n : ℚ)) : ℝ) = ((1 + √3) / 2) ^ n + ((1 - √3) / 2) ^ n := by
  push_cast
  rw [s_real, div_pow, div_pow]
  ring

/-- A173989(n) = 2-adic valuation of A173300(n). -/
def A173989 (n : ℕ) : ℕ := padicValNat 2 (A173300 n)

/-- (T m, U m) with s (2m) = 2^m T m and s (2m+1) = 2^m U m. -/
def tu : ℕ → ℤ × ℤ
  | 0 => (2, 2)
  | (m + 1) => ((tu m).1 + (tu m).2, 2 * (tu m).1 + 3 * (tu m).2)

def T (m : ℕ) : ℤ := (tu m).1

def U (m : ℕ) : ℤ := (tu m).2

theorem T_succ (m : ℕ) : T (m + 1) = T m + U m := rfl

theorem U_succ (m : ℕ) : U (m + 1) = 2 * T m + 3 * U m := rfl

theorem s_TU (m : ℕ) : s (2 * m) = 2 ^ m * T m ∧ s (2 * m + 1) = 2 ^ m * U m := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    have e1 : s (2 * (m + 1)) = 2 * s (2 * m + 1) + 2 * s (2 * m) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, s_succ_succ]
    have e2 : s (2 * (m + 1) + 1) = 2 * s (2 * (m + 1)) + 2 * s (2 * m + 1) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, s_succ_succ]
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    have e1' : s (2 * (m + 1)) = 2 ^ (m + 1) * T (m + 1) := by
      rw [e1, ih.1, ih.2, T_succ]
      ring
    refine ⟨e1', ?_⟩
    rw [e2, e1', ih.2, U_succ, T_succ]
    ring

/-- Residues: T_{2m} ≡ 2 (4), T_{2m+1} ≡ 4 (8), U_{2m}, U_{2m+1} ≡ 2 (4). -/
theorem TU_mod (m : ℕ) :
    T (2 * m) % 4 = 2 ∧ T (2 * m + 1) % 8 = 4 ∧
      U (2 * m) % 4 = 2 ∧ U (2 * m + 1) % 4 = 2 := by
  induction m with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨_, h2, _, h4⟩ := ih
    have a1 : T (2 * (m + 1)) = T (2 * m + 1) + U (2 * m + 1) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, T_succ]
    have a2 : U (2 * (m + 1)) = 2 * T (2 * m + 1) + 3 * U (2 * m + 1) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, U_succ]
    have a3 : T (2 * (m + 1) + 1) = T (2 * (m + 1)) + U (2 * (m + 1)) := T_succ _
    have a4 : U (2 * (m + 1) + 1) = 2 * T (2 * (m + 1)) + 3 * U (2 * (m + 1)) := U_succ _
    rw [a3, a4, a1, a2]
    omega

/-- If s n = 2^e u with u odd and e + b = n, then a(n) = b. -/
theorem A173989_of (n e b : ℕ) (u : ℤ) (hu : u % 2 = 1) (heb : e + b = n)
    (hs : s n = 2 ^ e * u) : A173989 n = b := by
  have hq : (s n : ℚ) / 2 ^ n = (u : ℚ) / ((2 ^ b : ℤ) : ℚ) := by
    rw [hs, ← heb]
    push_cast
    rw [pow_add]
    field_simp
  have hodd : Odd u := Int.odd_iff.mpr hu
  have hcop : Nat.Coprime u.natAbs ((2 : ℤ) ^ b).natAbs := by
    rw [Int.natAbs_pow]
    exact Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hodd))
  have hden := Rat.den_div_eq_of_coprime (by positivity : (0 : ℤ) < 2 ^ b) hcop
  have hden' : A173300 n = 2 ^ b := by
    unfold A173300
    rw [hq]
    exact_mod_cast hden
  rw [A173989, hden']
  exact padicValNat.prime_pow b

/-- a(4j+3) = a(4j+4) = a(4j+6) = 2j+1 and a(4j+5) = 2j+2. -/
theorem A173989_closed (j : ℕ) :
    A173989 (4 * j + 3) = 2 * j + 1 ∧ A173989 (4 * j + 4) = 2 * j + 1 ∧
      A173989 (4 * j + 5) = 2 * j + 2 ∧ A173989 (4 * j + 6) = 2 * j + 1 := by
  have m1 := TU_mod j
  have m2 := TU_mod (j + 1)
  have s3 := (s_TU (2 * j + 1)).2
  have s4 := (s_TU (2 * j + 2)).1
  have s5 := (s_TU (2 * j + 2)).2
  have s6 := (s_TU (2 * j + 3)).1
  rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring] at s3
  rw [show 2 * (2 * j + 2) = 4 * j + 4 by ring] at s4
  rw [show 2 * (2 * j + 2) + 1 = 4 * j + 5 by ring] at s5
  rw [show 2 * (2 * j + 3) = 4 * j + 6 by ring] at s6
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at m2
  rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring] at m2
  obtain ⟨_, _, _, hU1⟩ := m1
  obtain ⟨hT2, hT3, hU2, _⟩ := m2
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ : ∃ u, U (2 * j + 1) = 2 * u := ⟨U (2 * j + 1) / 2, by omega⟩
    refine A173989_of _ (2 * j + 2) _ u (by omega) (by ring) ?_
    rw [s3, hu]
    ring
  · obtain ⟨u, hu⟩ : ∃ u, T (2 * j + 2) = 2 * u := ⟨T (2 * j + 2) / 2, by omega⟩
    refine A173989_of _ (2 * j + 3) _ u (by omega) (by ring) ?_
    rw [s4, hu]
    ring
  · obtain ⟨u, hu⟩ : ∃ u, U (2 * j + 2) = 2 * u := ⟨U (2 * j + 2) / 2, by omega⟩
    refine A173989_of _ (2 * j + 3) _ u (by omega) (by ring) ?_
    rw [s5, hu]
    ring
  · obtain ⟨u, hu⟩ : ∃ u, T (2 * j + 3) = 4 * u := ⟨T (2 * j + 3) / 4, by omega⟩
    refine A173989_of _ (2 * j + 5) _ u (by omega) (by ring) ?_
    rw [s6, hu]
    ring

/-- The conjecture: from n = 3 on the terms come in blocks A, A, A+1, A, A odd. -/
theorem A173989_pattern (j : ℕ) :
    ∃ A : ℕ, Odd A ∧ A173989 (4 * j + 3) = A ∧ A173989 (4 * j + 4) = A ∧
      A173989 (4 * j + 5) = A + 1 ∧ A173989 (4 * j + 6) = A := by
  obtain ⟨h3, h4, h5, h6⟩ := A173989_closed j
  exact ⟨2 * j + 1, ⟨j, rfl⟩, h3, h4, h5, h6⟩

theorem A173989_one : A173989 1 = 0 :=
  A173989_of 1 1 0 1 (by norm_num) (by norm_num) (by rfl)

theorem A173989_two : A173989 2 = 0 := by
  unfold A173989 A173300
  have : (s 2 : ℚ) / 2 ^ 2 = 2 := by
    rw [show s 2 = 8 by rfl]
    norm_num
  rw [this]
  have h2 : (2 : ℚ).den = 1 := rfl
  rw [h2]
  simp
