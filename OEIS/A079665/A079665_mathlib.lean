import Mathlib

/-
OEIS-A079665 (Mathlib). Conjecture (comment in A079665): (b^s + 1)/(b^r + 1) is an integer
iff 1) r < s/2, 2) if s is odd then r ∣ s, 3) if s = k·2^t with gcd(k, 2^t) = 1 then
r = 2^t·u with u ∣ k. README reading: b ≥ 2 and 1 ≤ r < s. README result: true; classical.

`A079665_classical`: for b ≥ 2, r ≥ 1 (any s): b^r + 1 ∣ b^s + 1 ↔ r ∣ s ∧ s / r odd.
Proof: modulo N = b^r + 1, b^s = (b^r)^q·b^ρ ≡ (-1)^q·b^ρ (s = qr + ρ, ρ < r); for q even
N ∣ b^ρ + 1 < N is impossible, for q odd N ∣ b^ρ - 1 forces ρ = 0; conversely x + 1 ∣ x^q + 1
for odd q (Mathlib `Odd.nat_add_dvd_pow_add_pow`).

Main theorem `A079665_main`: for b ≥ 2 and 1 ≤ r < s, b^r + 1 ∣ b^s + 1 iff
(2r < s) ∧ (s odd → r ∣ s) ∧ (∀ t k, gcd(k, 2^t) = 1 → s = k·2^t → ∃ u, r = 2^t·u ∧ u ∣ k).
Condition 1 "r < s/2" is written 2r < s; condition 3 is quantified over every decomposition
s = k·2^t with gcd(k, 2^t) = 1 (the one with k odd, and t = 0, k = s). This is the README
result in full.

Outside Lean: nothing.
-/

theorem A079665_classical (b r s : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) :
    b ^ r + 1 ∣ b ^ s + 1 ↔ r ∣ s ∧ Odd (s / r) := by
  constructor
  · intro h
    set q := s / r with hq
    set ρ := s % r with hρ
    have hs : s = r * q + ρ := (Nat.div_add_mod s r).symm
    have hρr : ρ < r := Nat.mod_lt _ (by omega)
    have hbr : b ^ ρ < b ^ r := Nat.pow_lt_pow_right (by omega) hρr
    have hb1 : 1 ≤ b ^ ρ := Nat.one_le_pow _ _ (by omega)
    set N := b ^ r + 1 with hN
    have hz : ((b ^ s + 1 : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    have hbr' : ((b : ZMod N)) ^ r = -1 := by
      have : ((b ^ r + 1 : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
      push_cast at this
      exact eq_neg_of_add_eq_zero_left this
    have key : (-1 : ZMod N) ^ q * (b : ZMod N) ^ ρ + 1 = 0 := by
      rw [← hbr', ← pow_mul, ← pow_add, ← hs]
      push_cast at hz
      exact hz
    rcases Nat.even_or_odd q with he | ho
    · exfalso
      rw [he.neg_one_pow, one_mul] at key
      have : ((b ^ ρ + 1 : ℕ) : ZMod N) = 0 := by push_cast; exact key
      have hd := (ZMod.natCast_eq_zero_iff _ _).mp this
      have := Nat.le_of_dvd (by omega) hd
      omega
    · rw [ho.neg_one_pow] at key
      have h1 : ((b ^ ρ : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
        push_cast; linear_combination -key
      rw [ZMod.natCast_eq_natCast_iff'] at h1
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
      have hρ0 : ρ = 0 := by
        rcases Nat.pow_eq_one.mp h1 with h' | h'
        · omega
        · exact h'
      exact ⟨⟨q, by omega⟩, ho⟩
  · rintro ⟨⟨q, rfl⟩, ho⟩
    rw [Nat.mul_div_cancel_left _ (by omega)] at ho
    have := Odd.nat_add_dvd_pow_add_pow (b ^ r) 1 ho
    rw [one_pow, ← pow_mul] at this
    exact this

theorem A079665_main (b r s : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (hrs : r < s) :
    b ^ r + 1 ∣ b ^ s + 1 ↔
      (2 * r < s ∧ (Odd s → r ∣ s) ∧
        ∀ t k : ℕ, Nat.Coprime k (2 ^ t) → s = k * 2 ^ t → ∃ u, r = 2 ^ t * u ∧ u ∣ k) := by
  rw [A079665_classical b r s hb hr]
  constructor
  · rintro ⟨⟨q, hq⟩, ho⟩
    rw [hq, Nat.mul_div_cancel_left _ (by omega)] at ho
    have hq3 : 3 ≤ q := by
      obtain ⟨j, hj⟩ := ho
      rcases j with _ | j
      · subst hj; omega
      · omega
    refine ⟨by nlinarith, fun _ => ⟨q, hq⟩, ?_⟩
    intro t k hk hs
    have hcop : Nat.Coprime (2 ^ t) q :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr ho)
    have hdvd : 2 ^ t ∣ r * q := ⟨k, by rw [← hq, hs]; ring⟩
    obtain ⟨u, hu⟩ := hcop.dvd_of_dvd_mul_right hdvd
    refine ⟨u, hu, ⟨q, ?_⟩⟩
    have : 2 ^ t * (u * q) = 2 ^ t * k := by rw [← mul_assoc, ← hu, ← hq, hs]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
  · rintro ⟨_, _, h3⟩
    obtain ⟨t, k, hk, hs⟩ := Nat.exists_eq_two_pow_mul_odd (n := s) (by omega)
    obtain ⟨u, hu, w, hw⟩ := h3 t k (Nat.Coprime.pow_right _ ((Nat.coprime_two_right).mpr hk))
      (by rw [hs]; ring)
    have hsw : s = r * w := by rw [hs, hw, hu]; ring
    have hu0 : 0 < r := by omega
    refine ⟨⟨w, hsw⟩, ?_⟩
    rw [hsw, Nat.mul_div_cancel_left _ hu0]
    rw [hw] at hk
    exact (Nat.odd_mul.mp hk).2
