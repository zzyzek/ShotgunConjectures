import Mathlib

/-
OEIS-A227553 (Mathlib). a(n) = number of (x, y, z) ∈ (ℤ/n)^3 with x^2 - y^2 - z^2 = 1, here
`Nat.card` of the subtype of `ZMod n × ZMod n × ZMod n`. README result (the entry's conjecture,
true): a(2) = 4; a(2^s) = 2^(2s-1) for s ≥ 2; a(p^s) = (p+1) p^(2s-1) for primes p ≡ 1 (mod 4)
and a(p^s) = (p-1) p^(2s-1) for primes p ≡ 3 (mod 4), s ≥ 1.

Main theorem `A227553_main`: exactly these four statements.

Proof. Odd p: (x, y, z) ↦ (x - y, x + y, z) turns the equation into uv = 1 + z^2. Split by
whether u, v are units of ℤ/p^s (unit iff nonzero mod p). u a unit: (p-1)p^(s-1) · p^s
solutions. u not a unit, v a unit: (p-1)p^(s-1) times the number of z with p | 1 + z^2, which is
0 (p ≡ 3) or 2p^(s-1) (p ≡ 1, z ≡ ±i mod p). Both non-units: z^2 = uv - 1 ≡ -1 (mod p), no
solution for p ≡ 3; for p ≡ 1 exactly two roots, since squaring is injective on the elements
≡ 1 (mod p) (so every such element is a square) and roots of a unit square are ±z₀. p = 2,
s ≥ 3: fibre over (y, z); x^2 = A := 1 + y^2 + z^2 has 4 roots (x₀, -x₀, ±x₀ + 2^(s-1); the
squaring map on odd x is at most 4-to-1 onto the 2^(s-3) elements ≡ 1 (mod 8)) if A ≡ 1
(mod 8) and none otherwise (squares mod 8); the 8 residue pairs (y, z) mod 8 with
y^2 + z^2 ≡ 0 give 8 · 4^(s-3) pairs. a(2), a(4) by `decide`.

Outside Lean: nothing.
-/

open Finset

/-- a(n): the number of (x, y, z) ∈ (ℤ/n)^3 with x^2 - y^2 - z^2 = 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {t : ZMod n × ZMod n × ZMod n // t.1 ^ 2 - t.2.1 ^ 2 - t.2.2 ^ 2 = 1}

instance neZero_primePow (p s : ℕ) [hp : Fact p.Prime] : NeZero (p ^ s) :=
  ⟨pow_ne_zero _ hp.out.ne_zero⟩

theorem a_eq_card (n : ℕ) [NeZero n] :
    a n = #{t : ZMod n × ZMod n × ZMod n | t.1 ^ 2 - t.2.1 ^ 2 - t.2.2 ^ 2 = 1} := by
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]

section Odd

variable {p : ℕ} [hp : Fact p.Prime] {s : ℕ}

/-- Reduction ℤ/p^s → ℤ/p. -/
abbrev red (hs : s ≠ 0) : ZMod (p ^ s) →+* ZMod p := ZMod.castHom (dvd_pow_self p hs) (ZMod p)

theorem isUnit_iff_red (hs : s ≠ 0) (x : ZMod (p ^ s)) : IsUnit x ↔ red hs x ≠ 0 := by
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow hp.out (Nat.pos_of_ne_zero hs),
    map_natCast, ne_eq, ZMod.natCast_eq_zero_iff]

theorem card_fiber (hs : s ≠ 0) (c : ZMod p) :
    #{x : ZMod (p ^ s) | red hs x = c} = p ^ (s - 1) := by
  have hall : ∀ c, #{x : ZMod (p ^ s) | red hs x = c} = #{x : ZMod (p ^ s) | red hs x = 0} :=
    fun c => AddMonoidHom.card_fiber_eq_of_mem_range (red hs) (ZMod.ringHom_surjective _ c)
      ⟨0, map_zero _⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (ZMod (p ^ s))))
    (t := (univ : Finset (ZMod p))) (f := red hs) (fun _ _ => mem_univ _)
  simp only [hall, sum_const, card_univ, ZMod.card, smul_eq_mul] at hsum
  rw [hall c]
  have : p ^ s = p * p ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_left hp.out.pos (hsum.symm.trans this)

theorem card_nonunits (hs : s ≠ 0) : #{x : ZMod (p ^ s) | ¬IsUnit x} = p ^ (s - 1) := by
  simp_rw [isUnit_iff_red hs, not_not]
  exact card_fiber hs 0

theorem card_units (hs : s ≠ 0) : #{x : ZMod (p ^ s) | IsUnit x} = (p - 1) * p ^ (s - 1) := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (ZMod (p ^ s))))
    (fun x => IsUnit x)
  rw [card_nonunits hs, card_univ, ZMod.card] at h
  have : p ^ s = p * p ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  replace h := h.trans this
  have hp1 := hp.out.one_le
  rw [Nat.sub_mul, one_mul]
  omega

theorem two_ne_zero_of_odd (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
  exact hp2 this

end Odd

section OddCount

variable {p : ℕ} [hp : Fact p.Prime] {s : ℕ}

local notation "R3" => ZMod (p ^ s) × ZMod (p ^ s) × ZMod (p ^ s)

theorem unit_two (hs : s ≠ 0) (hp2 : p ≠ 2) : IsUnit (2 : ZMod (p ^ s)) := by
  rw [isUnit_iff_red hs, map_ofNat]; exact two_ne_zero_of_odd hp2

theorem exists_half (hs : s ≠ 0) (hp2 : p ≠ 2) : ∃ h : ZMod (p ^ s), 2 * h = 1 := by
  obtain ⟨u, hu⟩ := unit_two hs hp2
  exact ⟨↑u⁻¹, by rw [← hu]; simp⟩

/-- (x, y, z) ↦ (x - y, x + y, z) turns x^2 - y^2 - z^2 = 1 into uv = 1 + z^2. -/
theorem card_S_eq (hs : s ≠ 0) (hp2 : p ≠ 2) :
    #{t : R3 | t.1 ^ 2 - t.2.1 ^ 2 - t.2.2 ^ 2 = 1} = #{t : R3 | t.1 * t.2.1 = 1 + t.2.2 ^ 2} := by
  obtain ⟨h, hh⟩ := exists_half hs hp2
  apply card_nbij' (fun t => (t.1 - t.2.1, t.1 + t.2.1, t.2.2))
    (fun t => (h * (t.1 + t.2.1), h * (t.2.1 - t.1), t.2.2))
  · rintro ⟨x, y, z⟩ ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    linear_combination ht
  · rintro ⟨u, v, z⟩ ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    linear_combination ht + (2 * h + 1) * u * v * hh
  · rintro ⟨x, y, z⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨by linear_combination x * hh, by linear_combination y * hh, trivial⟩
  · rintro ⟨u, v, z⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨by linear_combination u * hh, by linear_combination v * hh, trivial⟩

theorem card_A (hs : s ≠ 0) :
    #{t : R3 | t.1 * t.2.1 = 1 + t.2.2 ^ 2 ∧ IsUnit t.1} = (p - 1) * p ^ (s - 1) * p ^ s := by
  have : #{t : R3 | t.1 * t.2.1 = 1 + t.2.2 ^ 2 ∧ IsUnit t.1} =
      #((univ.filter fun u : ZMod (p ^ s) => IsUnit u) ×ˢ (univ : Finset (ZMod (p ^ s)))) := by
    apply card_nbij' (fun t => (t.1, t.2.2)) (fun q => (q.1, q.1⁻¹ * (1 + q.2 ^ 2), q.2))
    · rintro ⟨u, v, z⟩ ht
      simp only [coe_filter, coe_product, coe_univ, mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_prod, Set.mem_univ, and_true] at ht ⊢
      exact ht.2
    · rintro ⟨u, z⟩ ht
      simp only [coe_filter, coe_product, coe_univ, mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_prod, Set.mem_univ, and_true] at ht ⊢
      exact ⟨by rw [← mul_assoc, ZMod.mul_inv_of_unit u ht, one_mul], ht⟩
    · rintro ⟨u, v, z⟩ ht
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [← ht.1, ← mul_assoc, ZMod.inv_mul_of_unit u ht.2, one_mul]
    · rintro ⟨u, z⟩ _
      rfl
  rw [this, card_product, card_units hs, card_univ, ZMod.card]

theorem card_B (hs : s ≠ 0) :
    #{t : R3 | (t.1 * t.2.1 = 1 + t.2.2 ^ 2 ∧ ¬IsUnit t.1) ∧ IsUnit t.2.1} =
      (p - 1) * p ^ (s - 1) * #{z : ZMod (p ^ s) | ¬IsUnit (1 + z ^ 2)} := by
  have : #{t : R3 | (t.1 * t.2.1 = 1 + t.2.2 ^ 2 ∧ ¬IsUnit t.1) ∧ IsUnit t.2.1} =
      #((univ.filter fun v : ZMod (p ^ s) => IsUnit v) ×ˢ
        (univ.filter fun z : ZMod (p ^ s) => ¬IsUnit (1 + z ^ 2))) := by
    apply card_nbij' (fun t => (t.2.1, t.2.2)) (fun q => (q.1⁻¹ * (1 + q.2 ^ 2), q.1, q.2))
    · rintro ⟨u, v, z⟩ ht
      simp only [coe_filter, coe_product, mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_prod] at ht ⊢
      refine ⟨ht.2, fun hw => ht.1.2 ?_⟩
      rw [← ht.1.1] at hw
      exact isUnit_of_mul_isUnit_left hw
    · rintro ⟨v, z⟩ ht
      simp only [coe_filter, coe_product, mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_prod] at ht ⊢
      have e : v⁻¹ * (1 + z ^ 2) * v = 1 + z ^ 2 := by
        rw [mul_comm, ← mul_assoc, ZMod.mul_inv_of_unit v ht.1, one_mul]
      refine ⟨⟨e, fun hu => ht.2 ?_⟩, ht.1⟩
      rw [← e]
      exact hu.mul ht.1
    · rintro ⟨u, v, z⟩ ht
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht
      simp only [Prod.mk.injEq, and_true]
      rw [← ht.1.1, mul_comm u v, ← mul_assoc, ZMod.inv_mul_of_unit v ht.2, one_mul]
    · rintro ⟨v, z⟩ _
      rfl
  rw [this, card_product, card_units hs]

theorem card_C :
    #{t : R3 | (t.1 * t.2.1 = 1 + t.2.2 ^ 2 ∧ ¬IsUnit t.1) ∧ ¬IsUnit t.2.1} =
      ∑ q ∈ (univ.filter fun u : ZMod (p ^ s) => ¬IsUnit u) ×ˢ
        (univ.filter fun u : ZMod (p ^ s) => ¬IsUnit u), #{z : ZMod (p ^ s) | z ^ 2 = q.1 * q.2 - 1} := by
  rw [card_eq_sum_card_fiberwise (f := fun t : R3 => (t.1, t.2.1))]
  · apply sum_congr rfl
    rintro ⟨u, v⟩ huv
    apply card_nbij' (fun t => t.2.2) (fun z => (u, v, z))
    · rintro ⟨u', v', z⟩ ht
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.mk.injEq] at ht ⊢
      obtain ⟨⟨⟨h1, -⟩, -⟩, rfl, rfl⟩ := ht
      rw [h1]; ring
    · intro z hz
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.mk.injEq, and_true, mem_product] at hz huv ⊢
      exact ⟨⟨by linear_combination -hz, huv.1⟩, huv.2⟩
    · rintro ⟨u', v', z⟩ ht
      simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.mk.injEq] at ht
      obtain ⟨-, rfl, rfl⟩ := ht
      rfl
    · intro z _
      rfl
  · rintro ⟨u, v, z⟩ ht
    simp only [coe_filter, coe_product, mem_univ, true_and, Set.mem_ofPred_eq,
      Set.mem_prod] at ht ⊢
    exact ⟨ht.1.2, ht.2⟩

end OddCount

section OddRoots

variable {p : ℕ} [hp : Fact p.Prime] {s : ℕ}

local notation "R3" => ZMod (p ^ s) × ZMod (p ^ s) × ZMod (p ^ s)

theorem red_nonunit (hs : s ≠ 0) {x : ZMod (p ^ s)} (hx : ¬IsUnit x) : red hs x = 0 := by
  rw [isUnit_iff_red hs, not_not] at hx; exact hx

/-- If a * b = 0 and a, b do not both reduce to 0, one of them is 0. -/
theorem zero_of_mul (hs : s ≠ 0) {a b : ZMod (p ^ s)} (h : a * b = 0)
    (hab : red hs a ≠ 0 ∨ red hs b ≠ 0) : a = 0 ∨ b = 0 := by
  rcases hab with ha | hb
  · right; exact ((isUnit_iff_red hs a).2 ha).mul_right_eq_zero.1 h
  · left; exact ((isUnit_iff_red hs b).2 hb).mul_left_eq_zero.1 h

/-- Squares of elements reducing to 1 cover all elements reducing to 1. -/
theorem sq_surj_one (hs : s ≠ 0) (hp2 : p ≠ 2) (b : ZMod (p ^ s)) (hb : red hs b = 1) :
    ∃ w : ZMod (p ^ s), w ^ 2 = b := by
  have key := surj_on_of_inj_on_of_card_le (s := univ.filter fun w : ZMod (p ^ s) => red hs w = 1)
    (t := univ.filter fun w : ZMod (p ^ s) => red hs w = 1) (fun w _ => w ^ 2)
    (by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      rw [map_pow, hw, one_pow])
    (by
      intro w₁ w₂ h₁ h₂ he
      simp only [mem_filter, mem_univ, true_and] at h₁ h₂
      have hm : (w₁ - w₂) * (w₁ + w₂) = 0 := by linear_combination he
      rcases zero_of_mul hs hm (Or.inr (by
        rw [map_add, h₁, h₂]; exact (by norm_num : (1 : ZMod p) + 1 = 2) ▸ two_ne_zero_of_odd hp2))
        with h | h
      · exact sub_eq_zero.1 h
      · exfalso
        have := congrArg (red hs) h
        rw [map_add, h₁, h₂, map_zero] at this
        exact two_ne_zero_of_odd hp2 (by linear_combination this))
    le_rfl b (by simp only [mem_filter, mem_univ, true_and]; exact hb)
  obtain ⟨w, _, hw⟩ := key
  exact ⟨w, hw.symm⟩

theorem sqrt_exists (hs : s ≠ 0) (hp2 : p ≠ 2) {i : ZMod p} (hi : i ^ 2 = -1)
    (c : ZMod (p ^ s)) (hc : red hs c = -1) : ∃ z : ZMod (p ^ s), z ^ 2 = c := by
  obtain ⟨z₁, hz₁⟩ := ZMod.ringHom_surjective (red hs) i
  have hi0 : i ≠ 0 := by
    rintro rfl
    have : (1 : ZMod p) = 0 := by linear_combination hi
    exact one_ne_zero this
  have hu : IsUnit z₁ := (isUnit_iff_red hs z₁).2 (by rw [hz₁]; exact hi0)
  set y := z₁⁻¹ with hy
  have hzy : z₁ * y = 1 := ZMod.mul_inv_of_unit z₁ hu
  have hry : i * red hs y = 1 := by rw [← hz₁, ← map_mul, hzy, map_one]
  obtain ⟨w, hw⟩ := sq_surj_one hs hp2 (c * y ^ 2) (by
    rw [map_mul, map_pow, hc]
    linear_combination (-(red hs y) ^ 2) * hi + (i * red hs y + 1) * hry)
  refine ⟨w * z₁, ?_⟩
  rw [mul_pow, hw]
  linear_combination c * (z₁ * y + 1) * hzy

theorem card_sqrt (hs : s ≠ 0) (hp2 : p ≠ 2) {i : ZMod p} (hi : i ^ 2 = -1)
    (c : ZMod (p ^ s)) (hc : red hs c = -1) : #{z : ZMod (p ^ s) | z ^ 2 = c} = 2 := by
  obtain ⟨z₀, hz₀⟩ := sqrt_exists hs hp2 hi c hc
  have hr : red hs z₀ ≠ 0 := by
    intro h
    have := congrArg (red hs) hz₀
    rw [map_pow, h, hc] at this
    have : (1 : ZMod p) = 0 := by linear_combination this
    exact one_ne_zero this
  have hne : z₀ ≠ -z₀ := by
    intro h
    have := congrArg (red hs) h
    rw [map_neg] at this
    have h2 : (2 : ZMod p) * red hs z₀ = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h2 | h2
    · exact two_ne_zero_of_odd hp2 h2
    · exact hr h2
  have : (univ.filter fun z : ZMod (p ^ s) => z ^ 2 = c) = {z₀, -z₀} := by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hz
      have hm : (z - z₀) * (z + z₀) = 0 := by linear_combination hz - hz₀
      have hab : red hs (z - z₀) ≠ 0 ∨ red hs (z + z₀) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        rw [map_sub] at hcon
        rw [map_add] at hcon
        have h2 : (2 : ZMod p) * red hs z₀ = 0 := by linear_combination hcon.2 - hcon.1
        rcases mul_eq_zero.1 h2 with h2 | h2
        · exact two_ne_zero_of_odd hp2 h2
        · exact hr h2
      rcases zero_of_mul hs hm hab with h | h
      · left; exact sub_eq_zero.1 h
      · right; exact eq_neg_of_add_eq_zero_left h
    · rintro (rfl | rfl)
      · exact hz₀
      · rw [neg_sq]; exact hz₀
  rw [this, card_pair hne]

theorem card_bad_z (hs : s ≠ 0) (hp2 : p ≠ 2) {i : ZMod p} (hi : i ^ 2 = -1) :
    #{z : ZMod (p ^ s) | ¬IsUnit (1 + z ^ 2)} = 2 * p ^ (s - 1) := by
  have hi0 : i ≠ -i := by
    intro h
    have h2 : (2 : ZMod p) * i = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h2 | h2
    · exact two_ne_zero_of_odd hp2 h2
    · rw [h2] at hi
      have : (1 : ZMod p) = 0 := by linear_combination hi
      exact one_ne_zero this
  have : (univ.filter fun z : ZMod (p ^ s) => ¬IsUnit (1 + z ^ 2)) =
      (univ.filter fun z => red hs z = i) ∪ (univ.filter fun z => red hs z = -i) := by
    rw [← filter_or]
    apply filter_congr
    intro z _
    rw [isUnit_iff_red hs, not_not, map_add, map_one, map_pow, ← sq_eq_sq_iff_eq_or_eq_neg]
    constructor
    · intro h; linear_combination h - hi
    · intro h; linear_combination h + hi
  rw [this, card_union_of_disjoint, card_fiber hs, card_fiber hs]
  · ring
  · rw [disjoint_filter]
    intro z _ h1 h2
    exact hi0 (h1.symm.trans h2)

theorem unit_of_three (hs : s ≠ 0) (h3 : p % 4 = 3) (z : ZMod (p ^ s)) : IsUnit (1 + z ^ 2) := by
  rw [isUnit_iff_red hs, map_add, map_one, map_pow]
  intro h
  have : IsSquare (-1 : ZMod p) := ⟨red hs z, by linear_combination -h⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.1 this) h3

theorem a_odd_three (hp2 : p ≠ 2) (h3 : p % 4 = 3) (hs : 1 ≤ s) :
    a (p ^ s) = (p - 1) * p ^ (2 * s - 1) := by
  have hs0 : s ≠ 0 := by omega
  rw [a_eq_card, card_S_eq hs0 hp2]
  have : (univ.filter fun t : R3 => t.1 * t.2.1 = 1 + t.2.2 ^ 2) =
      univ.filter fun t : R3 => t.1 * t.2.1 = 1 + t.2.2 ^ 2 ∧ IsUnit t.1 := by
    apply filter_congr
    intro t _
    constructor
    · intro h
      refine ⟨h, ?_⟩
      have := unit_of_three hs0 h3 t.2.2
      rw [← h] at this
      exact isUnit_of_mul_isUnit_left this
    · exact fun h => h.1
  rw [this, card_A hs0]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  ring

theorem a_odd_one (hp2 : p ≠ 2) (h1 : p % 4 = 1) (hs : 1 ≤ s) :
    a (p ^ s) = (p + 1) * p ^ (2 * s - 1) := by
  have hs0 : s ≠ 0 := by omega
  obtain ⟨i, hi⟩ : ∃ i : ZMod p, i ^ 2 = -1 := by
    obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : p % 4 ≠ 3)
    exact ⟨r, by rw [hr, sq]⟩
  rw [a_eq_card, card_S_eq hs0 hp2,
    ← card_filter_add_card_filter_not (s := univ.filter fun t : R3 => t.1 * t.2.1 = 1 + t.2.2 ^ 2)
      (fun t => IsUnit t.1),
    ← card_filter_add_card_filter_not
      (s := (univ.filter fun t : R3 => t.1 * t.2.1 = 1 + t.2.2 ^ 2).filter fun t => ¬IsUnit t.1)
      (fun t => IsUnit t.2.1)]
  simp only [filter_filter]
  rw [card_A hs0, card_B hs0, card_C, card_bad_z hs0 hp2 hi]
  have hC : ∀ q ∈ (univ.filter fun u : ZMod (p ^ s) => ¬IsUnit u) ×ˢ
      (univ.filter fun u : ZMod (p ^ s) => ¬IsUnit u),
      #{z : ZMod (p ^ s) | z ^ 2 = q.1 * q.2 - 1} = 2 := by
    rintro ⟨u, v⟩ huv
    simp only [mem_product, mem_filter, mem_univ, true_and] at huv
    apply card_sqrt hs0 hp2 hi
    rw [map_sub, map_mul, red_nonunit hs0 huv.1, red_nonunit hs0 huv.2, map_one]
    ring
  rw [sum_congr rfl hC, sum_const, card_product, card_nonunits hs0, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_le; omega⟩
  rw [show k + 1 - 1 = k by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    show q + 1 - 1 = q by omega]
  ring

end OddRoots

section Two

variable {s : ℕ}

theorem card_fiber_dvd {n m : ℕ} [NeZero n] [NeZero m] (h : m ∣ n) (c : ZMod m) :
    #{x : ZMod n | ZMod.castHom h (ZMod m) x = c} * m = n := by
  have hall : ∀ c, #{x : ZMod n | ZMod.castHom h (ZMod m) x = c} =
      #{x : ZMod n | ZMod.castHom h (ZMod m) x = 0} :=
    fun c => AddMonoidHom.card_fiber_eq_of_mem_range (ZMod.castHom h (ZMod m))
      (ZMod.ringHom_surjective _ c) ⟨0, map_zero _⟩
  have hsum := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (ZMod n)))
    (t := (univ : Finset (ZMod m))) (f := ZMod.castHom h (ZMod m)) (fun _ _ => mem_univ _)
  simp only [hall, sum_const, card_univ, ZMod.card, smul_eq_mul] at hsum
  rw [hall c, mul_comm]
  exact hsum.symm

theorem dvd8 (hs : 3 ≤ s) : 8 ∣ 2 ^ s := by
  have := pow_dvd_pow 2 hs
  norm_num at this
  exact this

abbrev r8 (hs : 3 ≤ s) : ZMod (2 ^ s) →+* ZMod 8 := ZMod.castHom (dvd8 hs) (ZMod 8)
abbrev c28 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

theorem red_eq (hs : 3 ≤ s) (x : ZMod (2 ^ s)) :
    red (p := 2) (by omega : s ≠ 0) x = c28 (r8 hs x) := by
  have : red (p := 2) (by omega : s ≠ 0) = c28.comp (r8 hs) := Subsingleton.elim _ _
  rw [this]; rfl

theorem card_fiber8 (hs : 3 ≤ s) (c : ZMod 8) :
    #{x : ZMod (2 ^ s) | r8 hs x = c} = 2 ^ (s - 3) := by
  have h := card_fiber_dvd (dvd8 hs) c
  have e : 2 ^ s = 2 ^ (s - 3) * 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans e)

/-- The element 2^(s-1) of ℤ/2^s. -/
abbrev hh (s : ℕ) : ZMod (2 ^ s) := ((2 ^ (s - 1) : ℕ) : ZMod (2 ^ s))

theorem two_hh (hs : 3 ≤ s) : 2 * hh s = 0 := by
  have : (2 : ZMod (2 ^ s)) * hh s = ((2 ^ s : ℕ) : ZMod (2 ^ s)) := by
    rw [hh, show 2 ^ s = 2 * 2 ^ (s - 1) by rw [← pow_succ']; congr 1; omega]
    push_cast; ring
  rw [this, ZMod.natCast_self]

theorem hh_sq (hs : 3 ≤ s) : hh s * hh s = 0 := by
  rw [hh, ← Nat.cast_mul, show 2 ^ (s - 1) * 2 ^ (s - 1) = 2 ^ s * 2 ^ (s - 2) by
    rw [← pow_add, ← pow_add]; congr 1; omega, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem hh_ne (hs : 3 ≤ s) : hh s ≠ 0 := by
  rw [hh, ne_eq, ZMod.natCast_eq_zero_iff, Nat.pow_dvd_pow_iff_le_right (by norm_num)]
  omega

theorem red_hh (hs : 3 ≤ s) : red (p := 2) (by omega : s ≠ 0) (hh s) = 0 := by
  rw [hh, map_natCast, ZMod.natCast_eq_zero_iff]
  exact dvd_pow_self 2 (by omega)

theorem two_mul_eq_zero (hs : 3 ≤ s) {d : ZMod (2 ^ s)} (hd : 2 * d = 0) : d = 0 ∨ d = hh s := by
  rw [← ZMod.natCast_zmod_val d] at hd ⊢
  have hv := ZMod.val_lt d
  generalize d.val = k at hd hv ⊢
  have : ((2 * k : ℕ) : ZMod (2 ^ s)) = 0 := by push_cast; exact hd
  rw [ZMod.natCast_eq_zero_iff, show 2 ^ s = 2 * 2 ^ (s - 1) by
    rw [← pow_succ']; congr 1; omega] at this
  obtain ⟨j, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hj : j < 2 := by
    rw [show 2 ^ s = 2 ^ (s - 1) * 2 by rw [← pow_succ]; congr 1; omega] at hv
    exact Nat.lt_of_mul_lt_mul_left hv
  interval_cases j
  · left; simp
  · right; simp

theorem even_eq (hs : 3 ≤ s) {d : ZMod (2 ^ s)} (hd : red (p := 2) (by omega : s ≠ 0) d = 0) :
    ∃ w, d = 2 * w := by
  rw [← ZMod.natCast_zmod_val d, map_natCast, ZMod.natCast_eq_zero_iff] at hd
  obtain ⟨k, hk⟩ := hd
  refine ⟨(k : ZMod (2 ^ s)), ?_⟩
  rw [← ZMod.natCast_zmod_val d, hk]
  push_cast; ring

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem sq_eq_cases (hs : 3 ≤ s) {x x₀ : ZMod (2 ^ s)}
    (hx : red (p := 2) (by omega : s ≠ 0) x ≠ 0) (hx₀ : red (p := 2) (by omega : s ≠ 0) x₀ ≠ 0)
    (he : x ^ 2 = x₀ ^ 2) : x = x₀ ∨ x = x₀ + hh s ∨ x = -x₀ ∨ x = -x₀ + hh s := by
  have hs0 : s ≠ 0 := by omega
  have h1 : red (p := 2) hs0 x = 1 := (zmod2_cases _).resolve_left hx
  have h2 : red (p := 2) hs0 x₀ = 1 := (zmod2_cases _).resolve_left hx₀
  obtain ⟨w₁, hw₁⟩ := even_eq hs (d := x - x₀) (by rw [map_sub, h1, h2, sub_self])
  obtain ⟨w₂, hw₂⟩ := even_eq hs (d := x + x₀) (by rw [map_add, h1, h2]; decide)
  have hsum : 2 * (w₁ + w₂ - x) = 0 := by linear_combination -hw₁ - hw₂
  have hred : red (p := 2) hs0 w₁ + red (p := 2) hs0 w₂ = 1 := by
    rcases two_mul_eq_zero hs hsum with h | h
    · have := congrArg (red (p := 2) hs0) h
      rw [map_sub, map_add, h1, map_zero] at this
      linear_combination this
    · have := congrArg (red (p := 2) hs0) h
      rw [map_sub, map_add, h1, red_hh hs] at this
      linear_combination this
  have hm : (2 * w₁) * (2 * w₂) = 0 := by rw [← hw₁, ← hw₂]; linear_combination he
  by_cases hw : red (p := 2) hs0 w₂ = 0
  · have hu : IsUnit w₁ := (isUnit_iff_red hs0 w₁).2 (by rw [hw, add_zero] at hred; rw [hred]; decide)
    have : 2 * (2 * w₂) = 0 := by
      have : (2 * (2 * w₂)) * w₁ = 0 := by linear_combination hm
      exact hu.mul_left_eq_zero.1 this
    rw [← hw₂] at this
    rcases two_mul_eq_zero hs this with h | h
    · right; right; left; linear_combination h
    · right; right; right; linear_combination h
  · have hu : IsUnit w₂ := (isUnit_iff_red hs0 w₂).2 hw
    have : 2 * (2 * w₁) = 0 := by
      have : (2 * (2 * w₁)) * w₂ = 0 := by linear_combination hm
      exact hu.mul_left_eq_zero.1 this
    rw [← hw₁] at this
    rcases two_mul_eq_zero hs this with h | h
    · left; linear_combination h
    · right; left; linear_combination h

end Two

section Two2

variable {s : ℕ}

theorem odd_sq8 : ∀ a : ZMod 8, c28 a ≠ 0 → a ^ 2 = 1 := by decide
theorem even_sq8 : ∀ a : ZMod 8, c28 a = 0 → a ^ 2 ≠ 1 := by decide
theorem sq8_vals : ∀ a b c : ZMod 8, a ^ 2 = 1 + b ^ 2 + c ^ 2 → 1 + b ^ 2 + c ^ 2 = 1 := by
  decide
theorem dist8 : ∀ a b : ZMod 8, c28 a ≠ 0 → 2 * b = 0 →
    2 * a ≠ 0 ∧ 2 * a - b ≠ 0 ∧ 2 * a + b ≠ 0 := by decide
theorem card_T8 : #{q : ZMod 8 × ZMod 8 | 1 + q.1 ^ 2 + q.2 ^ 2 = 1} = 8 := by decide

theorem card_odd (hs : 3 ≤ s) :
    #{x : ZMod (2 ^ s) | red (p := 2) (by omega : s ≠ 0) x ≠ 0} = 2 ^ (s - 1) := by
  have h := card_units (p := 2) (by omega : s ≠ 0)
  simp_rw [isUnit_iff_red (p := 2) (by omega : s ≠ 0)] at h
  rw [h]; simp

theorem root_exists (hs : 3 ≤ s) (A : ZMod (2 ^ s)) (hA : r8 hs A = 1) :
    ∃ x, red (p := 2) (by omega : s ≠ 0) x ≠ 0 ∧ x ^ 2 = A := by
  have hs0 : s ≠ 0 := by omega
  set O := univ.filter fun x : ZMod (2 ^ s) => red (p := 2) hs0 x ≠ 0 with hOdef
  set Y := univ.filter fun x : ZMod (2 ^ s) => r8 hs x = 1 with hYdef
  have hsub : O.image (fun x : ZMod (2 ^ s) => x ^ 2) ⊆ Y := by
    intro b hb
    simp only [O, Y, mem_image, mem_filter, mem_univ, true_and] at hb ⊢
    obtain ⟨x, hx, rfl⟩ := hb
    rw [map_pow]
    exact odd_sq8 _ (by rw [← red_eq hs]; exact hx)
  have hO : #O = 2 ^ (s - 1) := card_odd hs
  have hY : #Y = 2 ^ (s - 3) := card_fiber8 hs 1
  have hle := card_le_mul_card_image (f := fun x : ZMod (2 ^ s) => x ^ 2) O 4 (fun b hb => by
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hb
    simp only [O, mem_filter, mem_univ, true_and] at hx₀
    calc #{x ∈ O | x ^ 2 = x₀ ^ 2}
        ≤ #({x₀, x₀ + hh s, -x₀, -x₀ + hh s} : Finset (ZMod (2 ^ s))) := by
          apply card_le_card
          intro x hx
          simp only [O, mem_filter, mem_univ, true_and] at hx
          rcases sq_eq_cases hs hx.1 hx₀ hx.2 with h | h | h | h <;> simp [h]
      _ ≤ 4 := card_le_four)
  have heq : O.image (fun x : ZMod (2 ^ s) => x ^ 2) = Y := by
    apply eq_of_subset_of_card_le hsub
    rw [hY]
    rw [hO, show 2 ^ (s - 1) = 4 * 2 ^ (s - 3) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega] at hle
    omega
  have hAY : A ∈ Y := by simp only [Y, mem_filter, mem_univ, true_and]; exact hA
  rw [← heq] at hAY
  obtain ⟨x, hx, hx2⟩ := mem_image.1 hAY
  exact ⟨x, (mem_filter.1 hx).2, hx2⟩

theorem card_roots (hs : 3 ≤ s) (A : ZMod (2 ^ s)) (hA : r8 hs A = 1) :
    #{x : ZMod (2 ^ s) | x ^ 2 = A} = 4 := by
  have hs0 : s ≠ 0 := by omega
  obtain ⟨x₀, hx₀, hsq⟩ := root_exists hs A hA
  have hset : (univ.filter fun x : ZMod (2 ^ s) => x ^ 2 = A) =
      {x₀, x₀ + hh s, -x₀, -x₀ + hh s} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hx
      have hxo : red (p := 2) hs0 x ≠ 0 := by
        intro h0
        rw [red_eq hs] at h0
        apply even_sq8 _ h0
        rw [← map_pow, hx, hA]
      exact sq_eq_cases hs hxo hx₀ (hx.trans hsq.symm)
    · rintro (h | h | h | h) <;> rw [h]
      · exact hsq
      · linear_combination hsq + x₀ * two_hh hs + hh_sq hs
      · linear_combination hsq
      · linear_combination hsq - x₀ * two_hh hs + hh_sq hs
  have hodd : c28 (r8 hs x₀) ≠ 0 := by rw [← red_eq hs]; exact hx₀
  have hb : 2 * r8 hs (hh s) = 0 := by rw [← map_ofNat (r8 hs) 2, ← map_mul, two_hh hs, map_zero]
  obtain ⟨d1, d2, d3⟩ := dist8 _ _ hodd hb
  have n1 : x₀ ≠ x₀ + hh s := fun h => hh_ne hs (by linear_combination -h)
  have n2 : x₀ ≠ -x₀ := by
    intro h; have := congrArg (r8 hs) h; rw [map_neg] at this
    exact d1 (by linear_combination this)
  have n3 : x₀ ≠ -x₀ + hh s := by
    intro h; have := congrArg (r8 hs) h; rw [map_add, map_neg] at this
    exact d2 (by linear_combination this)
  have n4 : x₀ + hh s ≠ -x₀ := by
    intro h; have := congrArg (r8 hs) h; rw [map_add, map_neg] at this
    exact d3 (by linear_combination this)
  have n5 : x₀ + hh s ≠ -x₀ + hh s := by
    intro h; have := congrArg (r8 hs) h; rw [map_add, map_add, map_neg] at this
    exact d1 (by linear_combination this)
  have n6 : -x₀ ≠ -x₀ + hh s := fun h => hh_ne hs (by linear_combination -h)
  rw [hset, card_insert_of_notMem (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨n1, n2, n3⟩),
    card_insert_of_notMem (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨n4, n5⟩),
    card_pair n6]

theorem card_pairs8 (hs : 3 ≤ s) :
    #{q : ZMod (2 ^ s) × ZMod (2 ^ s) | r8 hs (1 + q.1 ^ 2 + q.2 ^ 2) = 1} =
      8 * (2 ^ (s - 3) * 2 ^ (s - 3)) := by
  rw [card_eq_sum_card_fiberwise (f := fun q : ZMod (2 ^ s) × ZMod (2 ^ s) => (r8 hs q.1, r8 hs q.2))
    (t := univ.filter fun q : ZMod 8 × ZMod 8 => 1 + q.1 ^ 2 + q.2 ^ 2 = 1)]
  · refine (sum_congr rfl (g := fun _ => 2 ^ (s - 3) * 2 ^ (s - 3)) ?_).trans ?_
    swap
    · rw [sum_const, card_T8, smul_eq_mul]
    rintro ⟨a, b⟩ hab
    simp only [mem_filter, mem_univ, true_and] at hab
    rw [show (2 ^ (s - 3) * 2 ^ (s - 3) : ℕ) = #{x : ZMod (2 ^ s) | r8 hs x = a} *
      #{x : ZMod (2 ^ s) | r8 hs x = b} by rw [card_fiber8 hs a, card_fiber8 hs b], ← card_product]
    congr 1
    ext ⟨y, z⟩
    simp only [mem_filter, mem_univ, true_and, mem_product, Prod.mk.injEq]
    constructor
    · exact fun h => h.2
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, rfl, rfl⟩
      rw [map_add, map_add, map_one, map_pow, map_pow]
      exact hab
  · rintro ⟨y, z⟩ h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h ⊢
    rw [map_add, map_add, map_one, map_pow, map_pow] at h
    exact h

theorem a_two (hs : 3 ≤ s) : a (2 ^ s) = 2 ^ (2 * s - 1) := by
  rw [a_eq_card, card_eq_sum_card_fiberwise
    (f := fun t : ZMod (2 ^ s) × ZMod (2 ^ s) × ZMod (2 ^ s) => (t.2.1, t.2.2))
    (t := univ) (fun _ _ => by simp)]
  have hterm : ∀ q : ZMod (2 ^ s) × ZMod (2 ^ s),
      #{t ∈ (univ.filter fun t : ZMod (2 ^ s) × ZMod (2 ^ s) × ZMod (2 ^ s) =>
        t.1 ^ 2 - t.2.1 ^ 2 - t.2.2 ^ 2 = 1) | (t.2.1, t.2.2) = q} =
      if r8 hs (1 + q.1 ^ 2 + q.2 ^ 2) = 1 then 4 else 0 := by
    rintro ⟨y, z⟩
    have : #{t ∈ (univ.filter fun t : ZMod (2 ^ s) × ZMod (2 ^ s) × ZMod (2 ^ s) =>
        t.1 ^ 2 - t.2.1 ^ 2 - t.2.2 ^ 2 = 1) | (t.2.1, t.2.2) = (y, z)} =
        #{x : ZMod (2 ^ s) | x ^ 2 = 1 + y ^ 2 + z ^ 2} := by
      apply card_nbij' (fun t => t.1) (fun x => (x, y, z))
      · rintro ⟨x, y', z'⟩ ht
        simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
          Prod.mk.injEq] at ht ⊢
        obtain ⟨h1, rfl, rfl⟩ := ht
        linear_combination h1
      · intro x hx
        simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
          Prod.mk.injEq, and_true] at hx ⊢
        linear_combination hx
      · rintro ⟨x, y', z'⟩ ht
        simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq,
          Prod.mk.injEq] at ht
        obtain ⟨-, rfl, rfl⟩ := ht
        rfl
      · intro x _
        rfl
    rw [this]
    split_ifs with h
    · exact card_roots hs _ h
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro x _ hx
      apply h
      have := congrArg (r8 hs) hx
      rw [map_pow, map_add, map_add, map_one, map_pow, map_pow] at this
      rw [map_add, map_add, map_one, map_pow, map_pow]
      exact sq8_vals _ _ _ this
  rw [sum_congr rfl (fun q _ => hterm q), ← sum_filter, sum_const, smul_eq_mul, card_pairs8 hs]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 3 := ⟨s - 3, by omega⟩
  rw [show k + 3 - 3 = k by omega, show 2 * (k + 3) - 1 = 2 * k + 5 by omega]
  ring

end Two2

/-! ### Main theorem -/

theorem a_two_one : a 2 = 4 := by
  rw [a_eq_card]; decide

theorem a_four : a 4 = 8 := by
  rw [a_eq_card]; decide

theorem A227553_main :
    a 2 = 4 ∧
    (∀ s, 2 ≤ s → a (2 ^ s) = 2 ^ (2 * s - 1)) ∧
    (∀ p s, p.Prime → p % 4 = 1 → 1 ≤ s → a (p ^ s) = (p + 1) * p ^ (2 * s - 1)) ∧
    (∀ p s, p.Prime → p % 4 = 3 → 1 ≤ s → a (p ^ s) = (p - 1) * p ^ (2 * s - 1)) := by
  refine ⟨a_two_one, ?_, ?_, ?_⟩
  · intro s hs
    rcases (show s = 2 ∨ 3 ≤ s by omega) with rfl | hs3
    · exact a_four
    · exact a_two hs3
  · intro p s hp h1 hs
    have := Fact.mk hp
    exact a_odd_one (by omega) h1 hs
  · intro p s hp h3 hs
    have := Fact.mk hp
    exact a_odd_three (by omega) h3 hs
