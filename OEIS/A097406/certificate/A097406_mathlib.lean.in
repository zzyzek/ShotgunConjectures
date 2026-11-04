import OpenProblemsLib

/-
OEIS A097406 (Mathlib). Conjectures on the prime factors of 2^n − 1: (1) the largest
primitive prime factor (one dividing no 2^m − 1 with m < n) is of the form kn + 1;
(3) for prime n every prime factor of 2^n − 1 is of the form kn + 1. ((2) is too vague to be
a mathematical statement; README result: misstated, not formalised.) README result: (1) and
(3) true.

Main theorems:
* `A097406_part1`: for n ≥ 1, every primitive prime factor p of 2^n − 1 has n ∣ p − 1
  (so the largest one, in particular, is kn + 1; when there is none, a(n) = 1 = 0·n + 1).
* `A097406_part3`: for prime n, every prime factor p of 2^n − 1 has n ∣ p − 1.
Proof: ord_p(2) = n in (ZMod p)ˣ (Mathlib `orderOf_eq_iff`, `orderOf_eq_prime`) and
ord_p(2) ∣ p − 1 (Fermat, Mathlib `ZMod.orderOf_dvd_card_sub_one`).

Outside Lean: nothing for (1) and (3). (Template certificate/A097406_mathlib.lean.in,
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- `p ∣ 2 ^ m - 1` is `(2 : ZMod p) ^ m = 1`. -/
theorem dvd_iff_zmod (p m : ℕ) : p ∣ 2 ^ m - 1 ↔ (2 : ZMod p) ^ m = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), sub_eq_zero]
  simp

theorem two_ne_zero_of_dvd (p n : ℕ) (hn : 1 ≤ n) (hp : p.Prime) (h : p ∣ 2 ^ n - 1) :
    (2 : ZMod p) ≠ 0 := by
  intro h2
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
  subst hp2
  have h1 : 2 ^ n % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]; simp
  have h3 := Nat.one_le_two_pow (n := n)
  generalize 2 ^ n = x at *
  omega

theorem A097406_part1 (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) (hd : p ∣ 2 ^ n - 1)
    (hprim : ∀ m, 0 < m → m < n → ¬ p ∣ 2 ^ m - 1) : n ∣ p - 1 := by
  have := Fact.mk hp
  have hord : orderOf (2 : ZMod p) = n := by
    rw [orderOf_eq_iff (by omega)]
    refine ⟨(dvd_iff_zmod p n).mp hd, fun m hm hm0 h => hprim m hm0 hm ((dvd_iff_zmod p m).mpr h)⟩
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one (two_ne_zero_of_dvd p n (by omega) hp hd)

theorem A097406_part3 (n p : ℕ) (hn : n.Prime) (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    n ∣ p - 1 := by
  have := Fact.mk hp
  have := Fact.mk hn
  have h2 : (2 : ZMod p) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    have h1 := hp.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · have : p = 2 := by omega
      subst this; simp at this
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
  have hord : orderOf (2 : ZMod p) = n := orderOf_eq_prime ((dvd_iff_zmod p n).mp hd) h2
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one (two_ne_zero_of_dvd p n hn.one_lt.le hp hd)
