import OpenProblemsLib

/-
OEIS A218483 (Fermat pseudoprimes to base 2 congruent to 1 mod 8; old name
"of the form 8*p*n + p^2, p prime, n natural").  Conjectures (Marius Coman,
entry), declared true and obvious by Charles R Greathouse IV (Dec 2014):
(1) if a base-2 Fermat pseudoprime P is 8*p*n + p^2 for an integer n and some
    prime factor p, then it is of that form for every prime factor;
(2) if P = p1*p2 (two primes) and P = 8*p1*n + p1^2, then P = 8*p2*(-n) + p2^2;
(3) if P is not of the form for one prime factor, it is not for any.
Also (same entry): no base-2 Fermat pseudoprime is 15 mod 40.

`Rep P p`: ∃ n : ℤ, P = 8 p n + p^2.
Main theorems.
* `rep_iff`: for odd P and a prime p ∣ P, Rep P p ↔ P % 8 = 1
  (P = p m; m ≡ p mod 8 ↔ p m ≡ 1 mod 8 for odd p, checked in ZMod 8).
* `odd_of_psp`: a base-2 Fermat pseudoprime is odd.
* `conj1`, `conj3`, `conj2` (conj2 holds for any naturals p1 ≠ 0, p2).
* `not_15_mod_40`: no base-2 Fermat pseudoprime is 15 mod 40
  (5 ∣ P forces 2^(P-1) ≡ 1 mod 5, but P - 1 ≡ 2 mod 4 gives 2^(P-1) ≡ 4).
Not checked in this file: nothing of the claims.
-/

namespace A218483

/-- P = 8 p n + p^2 for an integer n. -/
def Rep (P p : ℕ) : Prop := ∃ n : ℤ, (P : ℤ) = 8 * p * n + p ^ 2

theorem odd_of_psp {P : ℕ} (h : Nat.FermatPsp P 2) : Odd P := by
  obtain ⟨hpp, -, h1⟩ := h
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have h2 : 2 ∣ 2 ^ (P - 1) - 1 := (even_iff_two_dvd.mp hev).trans hpp
  have h3 : 2 ∣ 2 ^ (P - 1) := dvd_pow_self 2 (by omega)
  have h4 : 1 ≤ 2 ^ (P - 1) := Nat.one_le_two_pow
  omega

theorem zmod8 : ∀ x y : ZMod 8, (x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7) → (x * y = 1 ↔ y = x) := by
  decide

theorem rep_iff (P p : ℕ) (hp : p.Prime) (hpP : p ∣ P) (hP : Odd P) : Rep P p ↔ P % 8 = 1 := by
  obtain ⟨m, rfl⟩ := hpP
  have hpo : Odd p := (Nat.odd_mul.mp hP).1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hx : ((p : ℤ) : ZMod 8) = 1 ∨ ((p : ℤ) : ZMod 8) = 3 ∨ ((p : ℤ) : ZMod 8) = 5 ∨
      ((p : ℤ) : ZMod 8) = 7 := by
    rw [Int.cast_natCast, ← ZMod.natCast_mod]
    have : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hodd : p % 2 = 1 := Nat.odd_iff.mp hpo
    have : p % 8 % 2 = 1 := by omega
    interval_cases h : p % 8 <;> simp_all
  have e1 : Rep (p * m) p ↔ ((m : ℤ) : ZMod 8) = ((p : ℤ) : ZMod 8) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    constructor
    · rintro ⟨n, hn⟩
      have : (m : ℤ) = 8 * n + p := by
        apply mul_left_cancel₀ hp0
        push_cast at hn
        linear_combination hn
      exact ⟨-n, by rw [this]; ring⟩
    · rintro ⟨c, hc⟩
      push_cast at hc
      exact ⟨-c, by push_cast; linear_combination (-(p : ℤ)) * hc⟩
  have e2 : p * m % 8 = 1 ↔ ((p : ℤ) : ZMod 8) * ((m : ℤ) : ZMod 8) = 1 := by
    rw [← Int.cast_mul, ← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    omega
  rw [e1, e2, zmod8 _ _ hx]

theorem conj1 (P p q : ℕ) (hP : Nat.FermatPsp P 2) (hp : p.Prime) (hq : q.Prime)
    (hpP : p ∣ P) (hqP : q ∣ P) (h : Rep P p) : Rep P q := by
  have ho := odd_of_psp hP
  exact (rep_iff P q hq hqP ho).2 ((rep_iff P p hp hpP ho).1 h)

theorem conj3 (P p q : ℕ) (hP : Nat.FermatPsp P 2) (hp : p.Prime) (hq : q.Prime)
    (hpP : p ∣ P) (hqP : q ∣ P) (h : ¬ Rep P p) : ¬ Rep P q :=
  fun hq' => h (conj1 P q p hP hq hp hqP hpP hq')

theorem conj2 (p1 p2 : ℕ) (hp1 : p1 ≠ 0) (n : ℤ)
    (h : ((p1 * p2 : ℕ) : ℤ) = 8 * p1 * n + p1 ^ 2) :
    ((p1 * p2 : ℕ) : ℤ) = 8 * p2 * (-n) + p2 ^ 2 := by
  push_cast at h ⊢
  have h0 : (p1 : ℤ) ≠ 0 := by exact_mod_cast hp1
  have : (p2 : ℤ) = 8 * n + p1 := by
    apply mul_left_cancel₀ h0
    linear_combination h
  rw [this]; ring

theorem pow_mod5 (k : ℕ) : 2 ^ (4 * k + 2) % 5 = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 4 * (k + 1) + 2 = (4 * k + 2) + 4 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem not_15_mod_40 (P : ℕ) (hP : Nat.FermatPsp P 2) : P % 40 ≠ 15 := by
  intro h
  have h5 : 5 ∣ 2 ^ (P - 1) - 1 := (show 5 ∣ P by omega).trans hP.1
  obtain ⟨k, hk⟩ : ∃ k, P - 1 = 4 * k + 2 := ⟨(P - 1) / 4, by omega⟩
  rw [hk] at h5
  have := pow_mod5 k
  have h1 : 1 ≤ 2 ^ (4 * k + 2) := Nat.one_le_two_pow
  omega
