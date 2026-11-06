/-
OEIS A094358: squarefree products of factors of Fermat numbers. Comment: "Conjectured (by Munafo)
to be the same as: numbers n such that 2^^n == 1 mod n", where 2^^n = A014221(n).

Checked here (Lean + Mathlib, no sorry, no native_decide):
* `munafo_iff`: for n >= 1, 2^^n == 1 (mod n) iff n divides 2^(2^j) - 1 for some j.
* `A094358_subset_munafo`: every term of A094358 satisfies 2^^n == 1 (mod n) (unconditional).
* `munafo_conjecture_iff`: Munafo's conjecture (A094358 = {n >= 1 : 2^^n == 1 mod n}) holds
  iff every Fermat number is squarefree.
So the conjecture is equivalent to the open problem "are all Fermat numbers squarefree?";
nothing here decides that problem.
Membership in A094358: `InSeq n` = n squarefree and every prime factor of n divides some
Fermat number (n = 1 included, as a(1) = 1 in the entry).
Declarations live in namespace A094358 (left open so the axiom check can name them).
-/
import Mathlib

open Finset

namespace A094358

/-- The tower 2^^k (A014221): 1, 2, 4, 16, 65536, ... -/
def tow : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ tow k

/-- Membership in A094358. -/
def InSeq (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p, p.Prime → p ∣ n → ∃ k, p ∣ Nat.fermatNumber k

lemma tow_ge (k : ℕ) : k + 1 ≤ tow k := by
  induction k with
  | zero => simp [tow]
  | succ k ih =>
    have := Nat.lt_two_pow_self (n := tow k)
    simp only [tow]
    omega

lemma prod_fermat (j : ℕ) : ∏ k ∈ range j, Nat.fermatNumber k = 2 ^ (2 ^ j) - 1 := by
  rw [Nat.prod_fermatNumber, Nat.fermatNumber]
  omega

/-- 2^^n == 1 (mod n) iff n divides some 2^(2^j) - 1. -/
theorem munafo_iff (n : ℕ) (hn : 1 ≤ n) :
    tow n ≡ 1 [MOD n] ↔ ∃ j, n ∣ 2 ^ (2 ^ j) - 1 := by
  obtain rfl | ⟨m, rfl⟩ : n = 1 ∨ ∃ m, n = m + 2 := by
    rcases n with _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · exact ⟨fun _ => ⟨0, by simp⟩, fun _ => Nat.modEq_one⟩
  constructor
  · intro h
    refine ⟨tow m, ?_⟩
    have h1 : 1 ≤ tow (m + 2) := by have := tow_ge (m + 2); omega
    have := (Nat.modEq_iff_dvd' h1).mp h.symm
    simpa [tow] using this
  · rintro ⟨j, hj⟩
    have hN : NeZero (m + 2) := ⟨by omega⟩
    have h2 : (2 : ZMod (m + 2)) ^ (2 ^ j) = 1 := by
      have h := (ZMod.natCast_eq_zero_iff (2 ^ (2 ^ j) - 1) (m + 2)).mpr hj
      rw [Nat.cast_sub (Nat.one_le_two_pow), sub_eq_zero] at h
      simpa using h
    have hunit : IsUnit (2 : ZMod (m + 2)) := by
      refine isUnit_iff_exists_inv.mpr ⟨(2 : ZMod (m + 2)) ^ (2 ^ j - 1), ?_⟩
      rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow, h2]
    set u := hunit.unit with hu
    have hu2 : u ^ (2 ^ j) = 1 := by
      ext
      simp [hu, h2]
    obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu2)
    have hle : orderOf u < m + 2 := by
      calc orderOf u ≤ Fintype.card (ZMod (m + 2))ˣ := orderOf_le_card_univ
        _ = Nat.totient (m + 2) := ZMod.card_units_eq_totient _
        _ < m + 2 := Nat.totient_lt _ (by omega)
    have hi2 : i ≤ tow m := by
      have := Nat.lt_two_pow_self (n := i)
      have := tow_ge m
      omega
    have hdiv : orderOf u ∣ tow (m + 1) := by
      rw [hoi]
      exact Nat.pow_dvd_pow 2 hi2
    have hpow : u ^ tow (m + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
    have hz : (2 : ZMod (m + 2)) ^ tow (m + 1) = 1 := by
      have := congrArg (fun w : (ZMod (m + 2))ˣ => (w : ZMod (m + 2))) hpow
      simpa [hu] using this
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [tow] at hz ⊢
    push_cast
    exact hz

lemma seq_to_dvd {n : ℕ} (h : InSeq n) : ∃ j, n ∣ 2 ^ (2 ^ j) - 1 := by
  classical
  obtain ⟨hsq, hp⟩ := h
  have hk : ∀ p ∈ n.primeFactors, ∃ k, p ∣ Nat.fermatNumber k := fun p hp' =>
    hp p (Nat.prime_of_mem_primeFactors hp') (Nat.dvd_of_mem_primeFactors hp')
  choose! f hf using hk
  refine ⟨n.primeFactors.sup f + 1, ?_⟩
  rw [← prod_fermat]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
  refine Finset.prod_primes_dvd _ (fun p hp' => (Nat.prime_of_mem_primeFactors hp').prime) ?_
  intro p hp'
  exact (hf p hp').trans (dvd_prod_of_mem _ (mem_range.mpr
    (Nat.lt_succ_of_le (Finset.le_sup (f := f) hp'))))

/-- Every term of A094358 satisfies 2^^n == 1 (mod n). -/
theorem A094358_subset_munafo (n : ℕ) (hn : 1 ≤ n) (h : InSeq n) : tow n ≡ 1 [MOD n] :=
  (munafo_iff n hn).mpr (seq_to_dvd h)

lemma sqf_prod (hF : ∀ k, Squarefree (Nat.fermatNumber k)) (j : ℕ) :
    Squarefree (∏ k ∈ range j, Nat.fermatNumber k) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, Nat.squarefree_mul_iff]
    refine ⟨?_, ih, hF j⟩
    exact Nat.Coprime.prod_left fun k hk =>
      Nat.coprime_fermatNumber_fermatNumber (by simp at hk; omega)

lemma dvd_to_seq (hF : ∀ k, Squarefree (Nat.fermatNumber k)) {n j : ℕ}
    (h : n ∣ 2 ^ (2 ^ j) - 1) : InSeq n := by
  rw [← prod_fermat] at h
  refine ⟨(sqf_prod hF j).squarefree_of_dvd h, fun p hp hpn => ?_⟩
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp (hpn.trans h)
  exact ⟨k, hk⟩

/-- Munafo's conjecture holds iff every Fermat number is squarefree. -/
theorem munafo_conjecture_iff :
    (∀ n, 1 ≤ n → (InSeq n ↔ tow n ≡ 1 [MOD n])) ↔ ∀ k, Squarefree (Nat.fermatNumber k) := by
  constructor
  · intro h k
    by_contra hk
    rw [Nat.squarefree_iff_prime_squarefree] at hk
    simp only [not_forall, not_not] at hk
    obtain ⟨p, hp, hpp⟩ := hk
    have hn : 1 ≤ p * p := Nat.mul_pos hp.pos hp.pos
    have hd : p * p ∣ 2 ^ (2 ^ (k + 1)) - 1 := by
      rw [← prod_fermat]
      exact hpp.trans (dvd_prod_of_mem _ (mem_range.mpr (Nat.lt_succ_self k)))
    have hs := ((h (p * p) hn).mpr ((munafo_iff _ hn).mpr ⟨_, hd⟩)).1
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) p hp dvd_rfl
  · intro hF n hn
    rw [munafo_iff n hn]
    exact ⟨seq_to_dvd, fun ⟨j, hj⟩ => dvd_to_seq hF hj⟩
