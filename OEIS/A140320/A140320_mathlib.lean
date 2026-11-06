import Mathlib

/-
OEIS A140320 (offset 0): a(n) = A137576((3^n-1)/2), where
A137576(n) = A002326(n) * A006694(n) + 1,
A002326(n) = multiplicative order of 2 mod 2n+1,
A006694(n) = number of cyclotomic cosets of 2 mod 2n+1 (the coset {0} not
counted, as the data and the convention a(0) = 0 show).
Conjecture (entry): a(n) = 2n*3^(n-1) + 1.

Definitions.  `A002326 n = orderOf (2 : ZMod (2n+1))`.  `coset m x` is the
set {x*2^k mod m : k ≥ 0}; `A006694 n` is the number (`Set.ncard`) of
distinct sets `coset (2n+1) x` with 1 ≤ x < 2n+1.

Main theorem.
* `A140320_formula`: A140320 n = 2*n*3^(n-1) + 1 for every n (for n = 0 the
  right side is 1 in ℕ).

Route.
* `ord_two`: 2 has order 2*3^(r-1) mod 3^r (r ≥ 1); the exponent 3^(r-1)
  fails mod 3, the exponent 2*3^(r-2) fails by lifting the exponent
  (`padicValNat.pow_sub_pow`: v_3(4^t - 1) = 1 + v_3(t)).
* `gen`: so the powers of 2 are all units mod 3^r: for u, w prime to 3 there
  is k with u*2^k = w mod 3^r.
* `coset_eq`: for x = 3^j*u with 3 ∤ u, j < r, coset 3^r x = coset 3^r 3^j;
  `val_mod`: every element of coset 3^r (3^j) has 3-adic valuation exactly j,
  so the cosets of 3^j, j < r, are distinct (`coset_inj`).
* `A006694_pow3`: A006694((3^r-1)/2) = r; `A002326_pow3`: = 2*3^(r-1).

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py computes A137576(0..63) and A140320(0..13)).
-/

namespace OEIS140320

/-- A002326: multiplicative order of 2 mod 2n+1. -/
noncomputable def A002326 (n : ℕ) : ℕ := orderOf (2 : ZMod (2 * n + 1))

/-- The cyclotomic coset of 2 mod m containing x. -/
def coset (m x : ℕ) : Set ℕ := {y | ∃ k : ℕ, y = x * 2 ^ k % m}

/-- A006694: number of cyclotomic cosets of 2 mod 2n+1, the coset {0} excluded. -/
noncomputable def A006694 (n : ℕ) : ℕ :=
  Set.ncard {C : Set ℕ | ∃ x, 1 ≤ x ∧ x < 2 * n + 1 ∧ C = coset (2 * n + 1) x}

/-- A137576. -/
noncomputable def A137576 (n : ℕ) : ℕ := A002326 n * A006694 n + 1

/-- A140320. -/
noncomputable def A140320 (n : ℕ) : ℕ := A137576 ((3 ^ n - 1) / 2)

theorem ord_two (r : ℕ) (hr : 1 ≤ r) : orderOf (2 : ZMod (3 ^ r)) = 2 * 3 ^ (r - 1) := by
  have hcop : Nat.Coprime 2 (3 ^ r) := Nat.Coprime.pow_right _ (by norm_num)
  apply orderOf_eq_of_pow_and_pow_div_prime (by positivity)
  · have h := ZMod.pow_totient (ZMod.unitOfCoprime 2 hcop)
    rw [Nat.totient_prime_pow Nat.prime_three (by omega)] at h
    have h2 := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h2
    rw [← h2]
    norm_num [mul_comm]
  · intro p hp hpd
    have hp23 : p = 2 ∨ p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
      · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
    rcases hp23 with rfl | rfl
    · rw [show 2 * 3 ^ (r - 1) / 2 = 3 ^ (r - 1) by omega]
      intro h
      have h3 := congrArg (ZMod.castHom (dvd_pow_self 3 (by omega : r ≠ 0)) (ZMod 3)) h
      simp only [map_pow, map_ofNat, map_one] at h3
      obtain ⟨t, ht⟩ : Odd (3 ^ (r - 1)) := Odd.pow (by decide)
      rw [ht, pow_succ, pow_mul] at h3
      have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
      rw [h4, one_pow, one_mul] at h3
      exact absurd h3 (by decide)
    · have hr2 : 2 ≤ r := by
        by_contra hc
        have : r = 1 := by omega
        subst this
        norm_num at hpd
      have hsplit : 2 * 3 ^ (r - 1) / 3 = 2 * 3 ^ (r - 2) := by
        rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
        omega
      rw [hsplit]
      intro h
      rw [pow_mul] at h
      have h' : ((4 ^ (3 ^ (r - 2)) : ℕ) : ZMod (3 ^ r)) = ((1 : ℕ) : ZMod (3 ^ r)) := by
        push_cast
        rw [← h]
        norm_num
      rw [ZMod.natCast_eq_natCast_iff] at h'
      have hd : 3 ^ r ∣ 4 ^ (3 ^ (r - 2)) - 1 :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h'.symm
      have hv : padicValNat 3 (4 ^ (3 ^ (r - 2)) - 1 ^ (3 ^ (r - 2))) = 1 + (r - 2) := by
        rw [padicValNat.pow_sub_pow (p := 3) (by decide) (by norm_num) (by norm_num) (by norm_num)
          (by positivity)]
        simp
      have hne : 4 ^ (3 ^ (r - 2)) - 1 ≠ 0 := by
        have := Nat.one_lt_pow (n := 3 ^ (r - 2)) (by positivity) (by norm_num : 1 < 4)
        omega
      have := (padicValNat_dvd_iff_le hne).1 hd
      rw [one_pow] at hv
      omega

theorem gen (r : ℕ) (hr : 1 ≤ r) (u w : ℕ) (hu : ¬ 3 ∣ u) (hw : ¬ 3 ∣ w) :
    ∃ k, u * 2 ^ k % 3 ^ r = w % 3 ^ r := by
  have hcop : ∀ a, ¬ 3 ∣ a → Nat.Coprime a (3 ^ r) := fun a ha =>
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ha).symm
  let g : (ZMod (3 ^ r))ˣ := ZMod.unitOfCoprime 2 (hcop 2 (by omega))
  have hord : orderOf g = 2 * 3 ^ (r - 1) := by
    rw [← orderOf_units]
    simpa [g] using ord_two r hr
  have hcard : Fintype.card (ZMod (3 ^ r))ˣ = 2 * 3 ^ (r - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_three (by omega)]
    ring
  have hall : ∀ x : (ZMod (3 ^ r))ˣ, x ∈ Submonoid.powers g := by
    have h1 : Fintype.card (Submonoid.powers g) = Fintype.card (ZMod (3 ^ r))ˣ := by
      rw [← orderOf_eq_card_powers, hord, hcard]
    intro x
    have hb := (Fintype.bijective_iff_injective_and_card
      (Subtype.val : Submonoid.powers g → (ZMod (3 ^ r))ˣ)).2 ⟨Subtype.val_injective, h1⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := hb.2 x
    exact hy
  set U := ZMod.unitOfCoprime u (hcop u hu)
  set W := ZMod.unitOfCoprime w (hcop w hw)
  obtain ⟨k, hk⟩ := hall (U⁻¹ * W)
  refine ⟨k, ?_⟩
  have hk' : g ^ k = U⁻¹ * W := hk
  have h2 : U * g ^ k = W := by rw [hk', mul_inv_cancel_left]
  have h3 := congrArg Units.val h2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, U, W, g, ZMod.coe_unitOfCoprime] at h3
  have h4 : ((u * 2 ^ k : ℕ) : ZMod (3 ^ r)) = ((w : ℕ) : ZMod (3 ^ r)) := by
    push_cast
    exact h3
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h4

theorem mod_scale (j r a b : ℕ) (hj : j ≤ r) (h : a % 3 ^ (r - j) = b % 3 ^ (r - j)) :
    3 ^ j * a % 3 ^ r = 3 ^ j * b % 3 ^ r := by
  have e : 3 ^ r = 3 ^ j * 3 ^ (r - j) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, h]

theorem coset_eq (r j u : ℕ) (hj : j < r) (hu : ¬ 3 ∣ u) :
    coset (3 ^ r) (3 ^ j * u) = coset (3 ^ r) (3 ^ j) := by
  ext y
  simp only [coset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, rfl⟩
    have hu2 : ¬ 3 ∣ u * 2 ^ k := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
      · exact hu h
      · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; omega
    obtain ⟨l, hl⟩ := gen (r - j) (by omega) 1 (u * 2 ^ k) (by omega) hu2
    refine ⟨l, ?_⟩
    rw [mul_assoc]
    rw [one_mul] at hl
    exact mod_scale j r _ _ hj.le hl.symm
  · rintro ⟨l, rfl⟩
    have h2 : ¬ 3 ∣ 2 ^ l := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; omega
    obtain ⟨k, hk⟩ := gen (r - j) (by omega) u (2 ^ l) hu h2
    refine ⟨k, ?_⟩
    rw [mul_assoc]
    exact mod_scale j r _ _ hj.le hk.symm

theorem val_mod (r j k : ℕ) (hj : j < r) :
    3 ^ j ∣ 3 ^ j * 2 ^ k % 3 ^ r ∧ ¬ 3 ^ (j + 1) ∣ 3 ^ j * 2 ^ k % 3 ^ r := by
  have d1 : 3 ^ j ∣ 3 ^ r := Nat.pow_dvd_pow 3 hj.le
  have d2 : 3 ^ (j + 1) ∣ 3 ^ r := Nat.pow_dvd_pow 3 hj
  refine ⟨(Nat.dvd_mod_iff d1).2 (dvd_mul_right _ _), ?_⟩
  rw [Nat.dvd_mod_iff d2, pow_succ]
  intro h
  have h' := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h'
  omega

theorem coset_inj (r j j' : ℕ) (hj : j < r) (hj' : j' < r)
    (h : coset (3 ^ r) (3 ^ j) = coset (3 ^ r) (3 ^ j')) : j = j' := by
  have hmem : 3 ^ j ∈ coset (3 ^ r) (3 ^ j') := by
    rw [← h]
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)]
  obtain ⟨k, hk⟩ := hmem
  obtain ⟨h1, h2⟩ := val_mod r j' k hj'
  rw [← hk] at h1 h2
  have a := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h1
  have b : ¬ j' + 1 ≤ j := fun hle => h2 (Nat.pow_dvd_pow 3 hle)
  omega

theorem A006694_pow3 (r : ℕ) : A006694 ((3 ^ r - 1) / 2) = r := by
  have hm : 2 * ((3 ^ r - 1) / 2) + 1 = 3 ^ r := by
    have : 3 ^ r % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
    have : 1 ≤ 3 ^ r := Nat.one_le_pow _ _ (by norm_num)
    omega
  unfold A006694
  rw [hm]
  have hS : {C : Set ℕ | ∃ x, 1 ≤ x ∧ x < 3 ^ r ∧ C = coset (3 ^ r) x} =
      ↑((Finset.range r).image (fun j => coset (3 ^ r) (3 ^ j))) := by
    ext C
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨x, hx1, hx2, rfl⟩
      obtain ⟨e, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : x ≠ 0) 3 (by norm_num)
      have he : e < r := by
        have hu0 : 1 ≤ u := by
          rcases Nat.eq_zero_or_pos u with h | h
          · subst h; simp at hx1
          · exact h
        have : 3 ^ e < 3 ^ r := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hu0) hx2
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
      exact ⟨e, he, (coset_eq r e u he hu).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨3 ^ j, Nat.one_le_pow _ _ (by norm_num), Nat.pow_lt_pow_right (by norm_num) hj, rfl⟩
  rw [hS, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  intro j hj j' hj' h
  exact coset_inj r j j' (by simpa using hj) (by simpa using hj') h

theorem A002326_pow3 (r : ℕ) (hr : 1 ≤ r) : A002326 ((3 ^ r - 1) / 2) = 2 * 3 ^ (r - 1) := by
  have hm : 2 * ((3 ^ r - 1) / 2) + 1 = 3 ^ r := by
    have : 3 ^ r % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
    have : 1 ≤ 3 ^ r := Nat.one_le_pow _ _ (by norm_num)
    omega
  unfold A002326
  rw [hm]
  exact ord_two r hr

/-- **A140320**: a(n) = 2n*3^(n-1) + 1. -/
theorem A140320_formula (n : ℕ) : A140320 n = 2 * n * 3 ^ (n - 1) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [A140320, A137576, A002326, A006694, pow_zero, Nat.sub_self, Nat.zero_div,
      mul_zero, zero_add]
    have : {C : Set ℕ | ∃ x, 1 ≤ x ∧ x < 1 ∧ C = coset 1 x} = ∅ := by
      ext C; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, h1, h2, -⟩; omega
    rw [this, Set.ncard_empty]
    simp
  · unfold A140320 A137576
    rw [A002326_pow3 n hn, A006694_pow3 n]
    ring
