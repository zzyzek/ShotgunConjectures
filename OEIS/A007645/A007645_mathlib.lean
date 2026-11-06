import Mathlib

/-
OEIS A007645 (generalized cuban primes: primes of the form x^2 + xy + y^2),
A002383 (primes k^2 + k + 1) and
A162471 (prime divisors of the numbers n^2 + n + 1 that are not in A002383).
Conjecture (A007645, Tisdale 2009): A007645 = A002383 ∪ A162471.

Main theorem.
* `A007645_union`: `InA007645 p ↔ InA002383 p ∨ InA162471 p` for every natural
  number p.

Route.  `form_iff_mod_three`: a prime is x^2 + xy + y^2 (x, y natural) iff
it is 0 or 1 mod 3 (Thue's lemma: pigeonhole on i - s j mod p with
s^2 + s + 1 = 0 mod p, `rep_of_root`; `nat_rep` turns integer solutions into
natural ones).  `dvd_iff_mod_three`: a prime p divides some n^2 + n + 1 iff
p = 0 or 1 mod 3 (n has order 3 in (ZMod p)ˣ, so 3 ∣ p - 1; conversely
Cauchy's theorem gives an element of order 3).  The union is then the set of
primes dividing some n^2 + n + 1, since k^2 + k + 1 divides itself.

Also (A002383 conjecture, easy inclusion only):
* `A002383_sub`: every k^2 + k + 1 with k >= 2 equals 1 + k + k^2 (a base-k
  repunit with 3 digits, A085104 form) and ((k+1)^3 + 1)/((k+1) + 1)
  (A059055 form).  The reverse inclusion is open (see README).

Not checked in this file: agreement with the OEIS data terms (the
definitions are the entries' own).
-/

namespace A007645

/-- A007645: primes of the form x^2 + xy + y^2. -/
def InA007645 (p : ℕ) : Prop := p.Prime ∧ ∃ x y : ℕ, p = x ^ 2 + x * y + y ^ 2

/-- A002383: primes of the form k^2 + k + 1. -/
def InA002383 (p : ℕ) : Prop := p.Prime ∧ ∃ k, p = k ^ 2 + k + 1

/-- A162471: prime divisors of the numbers n^2 + n + 1 that do not occur in A002383. -/
def InA162471 (p : ℕ) : Prop := p.Prime ∧ (∃ n, p ∣ n ^ 2 + n + 1) ∧ ¬ InA002383 p

theorem dvd_iff_mod_three (p : ℕ) (hp : p.Prime) :
    (∃ n, p ∣ n ^ 2 + n + 1) ↔ (p % 3 = 0 ∨ p % 3 = 1) := by
  have := Fact.mk hp
  constructor
  · rintro ⟨n, hn⟩
    by_cases h3 : p = 3
    · left; subst h3; rfl
    right
    have hx : ((n : ZMod p)) ^ 2 + (n : ZMod p) + 1 = 0 := by
      have := (ZMod.natCast_eq_zero_iff (n ^ 2 + n + 1) p).2 hn
      push_cast at this; exact this
    have hx3 : (n : ZMod p) ^ 3 = 1 := by
      have : (n : ZMod p) ^ 3 - 1 = ((n : ZMod p) - 1) * ((n : ZMod p) ^ 2 + (n : ZMod p) + 1) := by
        ring
      rw [hx, mul_zero] at this
      exact sub_eq_zero.1 this
    have hx1 : (n : ZMod p) ≠ 1 := by
      intro h1
      rw [h1] at hx
      have h3' : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hx
      have := (ZMod.natCast_eq_zero_iff 3 p).1 h3'
      exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
    have hx0 : (n : ZMod p) ≠ 0 := by
      intro h0; rw [h0] at hx3; norm_num at hx3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (n : ZMod p) = 3 := orderOf_eq_prime hx3 hx1
    have hd := ZMod.orderOf_dvd_card_sub_one hx0
    rw [hord] at hd
    have := hp.two_le
    omega
  · intro h
    rcases h with h0 | h1
    · have h3 : p = 3 := by
        have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
      exact ⟨1, by rw [h3]; norm_num⟩
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
        rw [ZMod.card_units p]
        have := hp.two_le
        omega
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hcard
      set x : ZMod p := (g : ZMod p) with hxdef
      have hord : orderOf x = 3 := by rw [hxdef, orderOf_units]; exact hg
      have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
      have hx1 : x ≠ 1 := by
        intro h; rw [h, orderOf_one] at hord; norm_num at hord
      have hq : x ^ 2 + x + 1 = 0 := by
        have e : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
        rcases mul_eq_zero.1 e with h | h
        · exact absurd (sub_eq_zero.1 h) hx1
        · exact h
      refine ⟨x.val, (ZMod.natCast_eq_zero_iff _ p).1 ?_⟩
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hq

theorem nat_rep_minus (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∃ x y : ℕ, (x : ℤ) ^ 2 + x * y + y ^ 2 = u ^ 2 - u * v + v ^ 2 := by
  rcases le_total v u with h | h
  · refine ⟨(u - v).toNat, v.toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hv]; ring
  · refine ⟨(v - u).toNat, u.toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg hu]; ring

theorem nat_rep (a b : ℤ) : ∃ x y : ℕ, (x : ℤ) ^ 2 + x * y + y ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · exact ⟨a.toNat, b.toNat, by rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]⟩
  · obtain ⟨x, y, h⟩ := nat_rep_minus a (-b) ha (by omega)
    exact ⟨x, y, by rw [h]; ring⟩
  · obtain ⟨x, y, h⟩ := nat_rep_minus (-a) b (by omega) hb
    exact ⟨x, y, by rw [h]; ring⟩
  · exact ⟨(-a).toNat, (-b).toNat, by
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]; ring⟩

theorem even_both {a b : ℤ} (h : Even (a ^ 2 + a * b + b ^ 2)) : Even a ∧ Even b := by
  rcases Int.even_or_odd a with ha | ⟨c, rfl⟩ <;> rcases Int.even_or_odd b with hb | ⟨d, rfl⟩
  · exact ⟨ha, hb⟩
  · obtain ⟨c, rfl⟩ := ha
    exact absurd h (Int.not_even_iff_odd.2
      ⟨2 * c ^ 2 + 2 * c * d + c + 2 * d ^ 2 + 2 * d, by ring⟩)
  · obtain ⟨d, rfl⟩ := hb
    exact absurd h (Int.not_even_iff_odd.2
      ⟨2 * c ^ 2 + 2 * c + 2 * c * d + d + 2 * d ^ 2, by ring⟩)
  · exact absurd h (Int.not_even_iff_odd.2
      ⟨2 * c ^ 2 + 3 * c + 2 * c * d + 3 * d + 2 * d ^ 2 + 1, by ring⟩)

/-- Thue-type step: a prime `p` with `p ∣ s^2 + s + 1` is `x^2 + xy + y^2`. -/
theorem rep_of_root (p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hs : p ∣ s ^ 2 + s + 1) :
    ∃ x y : ℕ, p = x ^ 2 + x * y + y ^ 2 := by
  have := Fact.mk hp
  set m := Nat.sqrt p with hm
  have hcard : (Finset.univ : Finset (ZMod p)).card < ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).card := by
    rw [Finset.card_univ, ZMod.card, Finset.card_product, Finset.card_range]
    exact Nat.lt_succ_sqrt p
  obtain ⟨⟨i, j⟩, hij, ⟨i', j'⟩, hij', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun q : ℕ × ℕ => ((q.1 : ZMod p) - (s : ZMod p) * q.2)) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.mem_product, Finset.mem_range] at hij hij'
  simp only at heq
  set a : ℤ := (i : ℤ) - i' with ha
  set b : ℤ := (j : ℤ) - j' with hb
  have hab : (a : ZMod p) = (s : ZMod p) * b := by
    rw [ha, hb]; push_cast; linear_combination heq
  have hroot : ((s : ZMod p)) ^ 2 + s + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (s ^ 2 + s + 1) p).2 hs
    push_cast at this; exact this
  have hN : (p : ℤ) ∣ a ^ 2 + a * b + b ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hab]
    linear_combination (b : ZMod p) ^ 2 * hroot
  have hm2 : m * m < p := by
    have hle : m * m ≤ p := Nat.sqrt_le p
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hdvd : m ∣ p := ⟨m, h.symm⟩
      rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
      · rw [h1] at h; exact hp.one_lt.ne (by omega)
      · rw [h1] at h; have := hp.one_lt; nlinarith
  have hai : |a| ≤ m := by rw [ha, abs_le]; constructor <;> omega
  have hbi : |b| ≤ m := by rw [hb, abs_le]; constructor <;> omega
  have hnz : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc; push Not at hc
    apply hne; rw [Prod.mk.injEq]; omega
  set N := a ^ 2 + a * b + b ^ 2 with hNdef
  have hpos : 0 < N := by
    have h4 : 4 * N = (2 * a + b) ^ 2 + 3 * b ^ 2 := by rw [hNdef]; ring
    rcases hnz with h | h
    · rcases eq_or_ne b 0 with hb0 | hb0
      · have : 0 < (2 * a + b) ^ 2 := by
          rw [hb0, add_zero]; have : 2 * a ≠ 0 := by omega
          positivity
        nlinarith [sq_nonneg b]
      · have : 0 < b ^ 2 := by positivity
        nlinarith [sq_nonneg (2 * a + b)]
    · have : 0 < b ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * a + b)]
  have hlt : N < 3 * p := by
    have h1 : a ^ 2 ≤ (m : ℤ) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hai 2
    have h2 : b ^ 2 ≤ (m : ℤ) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hbi 2
    have h3 : a * b ≤ (m : ℤ) ^ 2 := by
      have := abs_mul a b
      have : |a * b| ≤ (m : ℤ) * m := by rw [abs_mul]; exact mul_le_mul hai hbi (abs_nonneg _) (by positivity)
      nlinarith [le_abs_self (a * b)]
    have : ((m * m : ℕ) : ℤ) < p := by exact_mod_cast hm2
    push_cast at this
    nlinarith
  obtain ⟨k, hk⟩ := hN
  have hk1 : 0 < k := by
    by_contra h; push Not at h; have : (p : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h; omega
  have hk3 : k < 3 := by
    by_contra h; push Not at h
    have : (p : ℤ) * 3 ≤ p * k := mul_le_mul_of_nonneg_left h (by positivity)
    omega
  have hk : N = p := by
    interval_cases k
    · rw [hk, mul_one]
    · exfalso
      obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := even_both (a := a) (b := b) ⟨p, by rw [← hNdef, hk]; ring⟩
      have e : N = 4 * (a' ^ 2 + a' * b' + b' ^ 2) := by rw [hNdef, ha', hb']; ring
      have hodd : (p : ℤ) % 2 = 1 := by
        have := hp.eq_one_or_self_of_dvd 2
        rcases Nat.Prime.eq_two_or_odd hp with h | h
        · exact absurd h hp2
        · exact_mod_cast h
      rw [hk] at e
      omega
  obtain ⟨x, y, hxy⟩ := nat_rep a b
  refine ⟨x, y, ?_⟩
  have : ((p : ℕ) : ℤ) = ((x ^ 2 + x * y + y ^ 2 : ℕ) : ℤ) := by push_cast; rw [hxy, ← hNdef, hk]
  exact_mod_cast this

theorem form_mod_three (x y : ℕ) :
    (x ^ 2 + x * y + y ^ 2) % 3 = 0 ∨ (x ^ 2 + x * y + y ^ 2) % 3 = 1 := by
  have key : ∀ r < 3, ∀ t < 3,
      (r ^ 2 + r * t + t ^ 2) % 3 = 0 ∨ (r ^ 2 + r * t + t ^ 2) % 3 = 1 := by decide
  have hx : x % 3 ≡ x [MOD 3] := Nat.mod_modEq x 3
  have hy : y % 3 ≡ y [MOD 3] := Nat.mod_modEq y 3
  have h := ((hx.pow 2).add (hx.mul hy)).add (hy.pow 2)
  unfold Nat.ModEq at h
  rw [← h]
  exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))

theorem form_iff_mod_three (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℕ, p = x ^ 2 + x * y + y ^ 2) ↔ (p % 3 = 0 ∨ p % 3 = 1) := by
  constructor
  · rintro ⟨x, y, rfl⟩; exact form_mod_three x y
  · intro h
    rcases h with h0 | h1
    · have h3 : p = 3 := by
        have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
      exact ⟨1, 1, by rw [h3]; norm_num⟩
    · obtain ⟨s, hs⟩ := (dvd_iff_mod_three p hp).2 (Or.inr h1)
      exact rep_of_root p s hp (by rintro rfl; norm_num at h1) hs

/-- **A007645 conjecture**: A007645 = A002383 ∪ A162471. -/
theorem A007645_union (p : ℕ) : InA007645 p ↔ InA002383 p ∨ InA162471 p := by
  constructor
  · rintro ⟨hp, hform⟩
    have hmod := (form_iff_mod_three p hp).1 hform
    by_cases h : InA002383 p
    · exact Or.inl h
    · exact Or.inr ⟨hp, (dvd_iff_mod_three p hp).2 hmod, h⟩
  · rintro (⟨hp, k, hk⟩ | ⟨hp, hd, -⟩)
    · exact ⟨hp, (form_iff_mod_three p hp).2
        ((dvd_iff_mod_three p hp).1 ⟨k, hk ▸ dvd_refl _⟩)⟩
    · exact ⟨hp, (form_iff_mod_three p hp).2 ((dvd_iff_mod_three p hp).1 hd)⟩

/-- Easy half of the A002383 conjecture: for k ≥ 2, k^2 + k + 1 is a 3-digit base-k repunit
(A085104 form) and equals ((k+1)^3 + 1)/((k+1) + 1) (A059055 form). -/
theorem A002383_sub (k : ℕ) :
    k ^ 2 + k + 1 = ∑ i ∈ Finset.range 3, k ^ i ∧
      ((k + 1) + 1) * (k ^ 2 + k + 1) = (k + 1) ^ 3 + 1 := by
  refine ⟨?_, by ring⟩
  simp [Finset.sum_range_succ]; ring

end A007645

open A007645
