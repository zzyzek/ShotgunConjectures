import Mathlib

/-
OEIS A166102: odd numbers k such that A166100((k-1)/2)/k is not an integer, where
A166100((k-1)/2) = S(k) = sum of the 1 <= i <= k with Jacobi symbol J(i, k) = 1.
OEIS A166103 = squares of A166104 (numbers whose prime factors are all = 3 or 5 mod 6).
Conjecture: A166102(n) = 3 A166103(n).

Main theorem.
* `A166102_iff k (Odd k)`: ¬ k ∣ S(k) ↔ ∃ m, k = 3 m^2 ∧ every prime factor of m is 3 or = 5 (mod 6).
  (Both sequences are increasing, so this set equality is the conjecture.)
Route.
* `mul_invariant`, `mul_invariant_gen`: for J(u, k) = 1 (or a predicate invariant under
  i ↦ u i mod M), u * S = S in ZMod.  `dvd_three_S`: k ∣ 3 S(k) (u = 4).
* `dvd_S_of_witness`: some u with J(u, k) = 1, u = 2 (mod 3) gives k ∣ S(k).
* `witness_even`, `witness_nonsq` (with `exists_jac_neg_one`: a non-residue mod a prime of odd
  exponent, CRT): such u exists unless k = 3^(2b+1) n^2.
* `square_case`: for k = 3^(2b+1) n^2 (3 ∤ n), J(i, k) = 1 iff i = 1 mod 3 and gcd(i, n) = 1
  (`jac_cond`); splitting [0, k) into blocks of length 3n (`block_sum`), k ∣ S iff 3n ∣ S_{3n};
  n ∣ S_{3n} (`n_dvd_SP`), S_{3n} = #R = phi(n) mod 3 (`SP_mod_three`, `card_cond`), and
  3 ∣ phi(n) iff n has a prime factor = 1 mod 3 (`three_dvd_totient`).
Checked: all of the above.  Not checked: agreement with the OEIS data (certificate/check.py).
-/

namespace OEIS_A166103

open Finset

/-- A166100 with k = 2n+1: sum of those 1 ≤ i ≤ k with Jacobi symbol J(i, k) = 1. -/
def S (k : ℕ) : ℕ := ∑ i ∈ Icc 1 k, if jacobiSym i k = 1 then i else 0

/-- The same sum over 0 ≤ i < k. -/
def S' (k : ℕ) : ℕ := ∑ i ∈ range k, if jacobiSym i k = 1 then i else 0

theorem S_eq (k : ℕ) (hk : 1 ≤ k) : S k = S' k + (if jacobiSym k k = 1 then k else 0) := by
  unfold S S'
  have h1 : Icc 1 k = (Ico 1 k) ∪ {k} := by
    ext x; simp; omega
  have h2 : range k = insert 0 (Ico 1 k) := by
    ext x; simp; omega
  rw [h1, h2, Finset.sum_union (by simp), Finset.sum_insert (by simp)]
  simp

theorem S_modeq (k : ℕ) (hk : 1 ≤ k) : (S k : ZMod k) = (S' k : ZMod k) := by
  rw [S_eq k hk]
  split_ifs <;> simp

theorem jac_mod (k a : ℕ) : jacobiSym ((a % k : ℕ) : ℤ) k = jacobiSym (a : ℤ) k := by
  rw [Int.natCast_mod, ← jacobiSym.mod_left]

theorem coprime_of_jac (k u : ℕ) (hk : 1 ≤ k) (hu : jacobiSym u k = 1) : Nat.Coprime u k := by
  have hne : NeZero k := ⟨by omega⟩
  have := (jacobiSym.eq_zero_iff_not_coprime (a := (u : ℤ)) (b := k)).not.mp (by rw [hu]; norm_num)
  rw [not_not, Int.gcd_natCast_natCast] at this
  exact this

/-- Multiplying by u with J(u, k) = 1 permutes {i < k : J(i, k) = 1} mod k. -/
theorem mul_invariant (k u : ℕ) (hk : 1 ≤ k) (hu : jacobiSym u k = 1) :
    ((u : ZMod k) * S' k : ZMod k) = S' k := by
  have hcop := coprime_of_jac k u hk hu
  have : NeZero k := ⟨by omega⟩
  set w := ZMod.unitOfCoprime u hcop
  set v : ℕ := ((w⁻¹ : (ZMod k)ˣ) : ZMod k).val
  have hvu : ((v : ℕ) : ZMod k) * (u : ZMod k) = 1 := by
    have hne : NeZero k := ⟨by omega⟩
    simp only [v, ZMod.natCast_val, ZMod.cast_id', id]
    have : ((w⁻¹ : (ZMod k)ˣ) : ZMod k) * (w : ZMod k) = 1 := by simp
    simp [w]
  have key : ∀ i ∈ range k, (((if jacobiSym ((u * i % k : ℕ) : ℤ) k = 1 then u * i % k else 0 : ℕ)) :
      ZMod k) = (u : ZMod k) * ((if jacobiSym (i : ℤ) k = 1 then i else 0 : ℕ) : ZMod k) := by
    intro i _
    rw [jac_mod, Nat.cast_mul, jacobiSym.mul_left, hu, one_mul]
    split_ifs
    · simp
    · simp
  unfold S'
  rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_congr rfl key, ← Nat.cast_sum, ← Nat.cast_sum]
  congr 1
  apply Finset.sum_nbij' (fun i => u * i % k) (fun i => v * i % k)
  · intro i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [← ZMod.val_natCast_of_lt hi, ← ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega : 0 < k))]
    congr 1
    push_cast [ZMod.natCast_mod]
    rw [← mul_assoc, hvu, one_mul, ZMod.natCast_zmod_val]
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [← ZMod.val_natCast_of_lt hi, ← ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega : 0 < k))]
    congr 1
    push_cast [ZMod.natCast_mod]
    rw [← mul_assoc, mul_comm (u : ZMod k), hvu, one_mul, ZMod.natCast_zmod_val]
  · intro i _
    rfl

theorem S_three (k : ℕ) (hk : Odd k) : ((3 : ZMod k) * S k) = 0 := by
  have hk1 : 1 ≤ k := hk.pos
  have h4 := mul_invariant k 4 hk1 (by exact_mod_cast jacobiSym.at_four hk)
  rw [S_modeq k hk1]
  push_cast at h4
  linear_combination h4

/-- k ∣ 3 S(k) for every odd k. -/
theorem dvd_three_S (k : ℕ) (hk : Odd k) : k ∣ 3 * S k := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact S_three k hk

/-- If some u with J(u, k) = 1 has u ≡ 2 (mod 3), then k ∣ S(k). -/
theorem dvd_S_of_witness (k u : ℕ) (hk : Odd k) (hu : jacobiSym u k = 1) (hu3 : u % 3 = 2) :
    k ∣ S k := by
  have hk1 : 1 ≤ k := hk.pos
  have h3 := S_three k hk
  have hu' := mul_invariant k u hk1 hu
  rw [← S_modeq k hk1] at hu'
  rw [← ZMod.natCast_eq_zero_iff]
  obtain ⟨t, ht⟩ : ∃ t, u = 3 * t + 2 := ⟨u / 3, by omega⟩
  rw [ht] at hu'
  push_cast at hu'
  linear_combination hu' - (t : ZMod k) * h3

/-- If 3 ∤ k then k ∣ S(k). -/
theorem dvd_S_of_not_three (k : ℕ) (hk : Odd k) (h3 : ¬ 3 ∣ k) : k ∣ S k := by
  have hcop : Nat.Coprime k 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  exact hcop.dvd_of_dvd_mul_left (dvd_three_S k hk)

/-! ### General invariance and the case k = 3^(2b+1) n^2 -/

/-- Sum of the i < M satisfying P. -/
def SP (M : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ := ∑ i ∈ range M, if P i then i else 0

theorem mul_invariant_gen (M u : ℕ) (P : ℕ → Prop) [DecidablePred P] (hM : 1 ≤ M)
    (hcop : Nat.Coprime u M) (hP : ∀ i, P (u * i % M) ↔ P i) :
    ((u : ZMod M) * SP M P : ZMod M) = SP M P := by
  have : NeZero M := ⟨by omega⟩
  set w := ZMod.unitOfCoprime u hcop
  set v : ℕ := ((w⁻¹ : (ZMod M)ˣ) : ZMod M).val
  have hvu : ((v : ℕ) : ZMod M) * (u : ZMod M) = 1 := by
    simp only [v, ZMod.natCast_val, ZMod.cast_id', id]
    have : ((w⁻¹ : (ZMod M)ˣ) : ZMod M) * (w : ZMod M) = 1 := by simp
    simp [w]
  have key : ∀ i ∈ range M, (((if P (u * i % M) then u * i % M else 0 : ℕ)) : ZMod M) =
      (u : ZMod M) * ((if P i then i else 0 : ℕ) : ZMod M) := by
    intro i _
    by_cases h : P i
    · have h' : P (u * i % M) := (hP i).mpr h
      simp [h, h']
    · have h' : ¬ P (u * i % M) := fun h' => h ((hP i).mp h')
      simp [h, h']
  unfold SP
  rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_congr rfl key, ← Nat.cast_sum, ← Nat.cast_sum]
  congr 1
  apply Finset.sum_nbij' (fun i => u * i % M) (fun i => v * i % M)
  · intro i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [← ZMod.val_natCast_of_lt hi, ← ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega : 0 < M))]
    congr 1
    push_cast [ZMod.natCast_mod]
    rw [← mul_assoc, hvu, one_mul, ZMod.natCast_zmod_val]
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [← ZMod.val_natCast_of_lt hi, ← ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega : 0 < M))]
    congr 1
    push_cast [ZMod.natCast_mod]
    rw [← mul_assoc, mul_comm (u : ZMod M), hvu, one_mul, ZMod.natCast_zmod_val]
  · intro i _
    rfl

/-- The condition J(i, 3^(2b+1) n^2) = 1, as a predicate periodic mod 3n. -/
def cond (n i : ℕ) : Prop := i % 3 = 1 ∧ Nat.Coprime i n

instance (n : ℕ) : DecidablePred (cond n) := fun i => by unfold cond; infer_instance

theorem cond_shift (n i j : ℕ) : cond n (i + j * (3 * n)) ↔ cond n i := by
  unfold cond
  have h1 : (i + j * (3 * n)) % 3 = i % 3 := by
    rw [show j * (3 * n) = 3 * (j * n) by ring, Nat.add_mul_mod_self_left]
  rw [h1, show j * (3 * n) = n * (3 * j) by ring, Nat.coprime_add_mul_left_left]

theorem jac_three (i : ℕ) : jacobiSym i 3 = 1 ↔ i % 3 = 1 := by
  rw [jacobiSym.mod_left]
  have : (i : ℤ) % ((3 : ℕ) : ℤ) = ((i % 3 : ℕ) : ℤ) := by push_cast; rfl
  rw [this]
  have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : i % 3 <;> norm_num [jacobiSym]

theorem jac_cond (b n i : ℕ) (hn : 1 ≤ n) :
    jacobiSym i (3 ^ (2 * b + 1) * n ^ 2) = 1 ↔ cond n i := by
  have : NeZero (3 ^ (2 * b + 1)) := ⟨by positivity⟩
  have : NeZero (n ^ 2) := ⟨by positivity⟩
  rw [jacobiSym.mul_right, jacobiSym.pow_right, jacobiSym.pow_right]
  unfold cond
  rw [← jac_three]
  have h3 := jacobiSym.trichotomy (i : ℤ) 3
  by_cases hc : Nat.Coprime i n
  · have hsq : jacobiSym i n ^ 2 = 1 := jacobiSym.sq_one (by
      rw [Int.gcd_natCast_natCast]; exact hc)
    rw [hsq, mul_one, pow_succ, pow_mul]
    rcases h3 with h | h | h <;> rw [h] <;> norm_num
    exact hc
  · have hne : NeZero n := ⟨by omega⟩
    have h0 : jacobiSym i n = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr (by
      rw [Int.gcd_natCast_natCast]; exact hc)
    simp [h0, hc]

/-- Block decomposition: k = B M with a condition periodic mod M = 3n. -/
theorem block_sum (n B : ℕ) :
    (∑ i ∈ range (B * (3 * n)), if cond n i then i else 0) * 2 =
      B * (B - 1) * (3 * n) * ((range (3 * n)).filter (cond n)).card + 2 * B * SP (3 * n) (cond n) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [show (B + 1) * (3 * n) = B * (3 * n) + 3 * n by ring, Finset.sum_range_add]
    have e : ∀ x ∈ range (3 * n), (if cond n (B * (3 * n) + x) then B * (3 * n) + x else 0) =
        (if cond n x then B * (3 * n) else 0) + (if cond n x then x else 0) := by
      intro x _
      have hx : cond n (B * (3 * n) + x) ↔ cond n x := by
        rw [show B * (3 * n) + x = x + B * (3 * n) by ring]; exact cond_shift n x B
      by_cases hc : cond n x
      · simp only [hx, hc, ↓reduceIte]
      · simp only [hx, hc, ↓reduceIte, add_zero]
    have hconst : (∑ x ∈ range (3 * n), if cond n x then B * (3 * n) else 0) =
        ((range (3 * n)).filter (cond n)).card * (B * (3 * n)) := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, hconst, add_mul, add_mul, ih]
    unfold SP
    rcases B with _ | B
    · simp; ring
    · simp only [Nat.add_sub_cancel]
      ring

theorem coprime_iff_mod (a n : ℕ) : Nat.Coprime a n ↔ Nat.Coprime (a % n) n := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm a n, Nat.gcd_rec n a]

theorem card_cond (n : ℕ) (hn : 1 ≤ n) (h3 : ¬ 3 ∣ n) :
    ((range (3 * n)).filter (cond n)).card = n.totient := by
  have co : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_bij' (fun r _ => r % n) (fun s _ => (Nat.chineseRemainder co 1 s : ℕ))
  · intro r hr
    simp only [mem_filter, mem_range, cond] at hr ⊢
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have := (coprime_iff_mod r n).mp hr.2.2
    exact this.symm
  · intro s hs
    simp only [mem_filter, mem_range, cond] at hs ⊢
    have hc := (Nat.chineseRemainder co 1 s).2
    refine ⟨Nat.chineseRemainder_lt_mul co 1 s (by norm_num) (by omega), ?_, ?_⟩
    · have := hc.1; unfold Nat.ModEq at this; rw [this]
    · rw [coprime_iff_mod]
      have := hc.2; unfold Nat.ModEq at this; rw [this]
      exact (coprime_iff_mod s n).mp hs.2.symm
  · intro r hr
    simp only [mem_filter, mem_range, cond] at hr
    have hc := (Nat.chineseRemainder co 1 (r % n)).2
    have hlt := Nat.chineseRemainder_lt_mul co 1 (r % n) (by norm_num) (by omega)
    have h1 : (Nat.chineseRemainder co 1 (r % n) : ℕ) ≡ r [MOD 3 * n] := by
      rw [← Nat.modEq_and_modEq_iff_modEq_mul co]
      refine ⟨?_, ?_⟩
      · have := hc.1; unfold Nat.ModEq at this ⊢; rw [this, hr.2.1]
      · have := hc.2; unfold Nat.ModEq at this ⊢; rw [this, Nat.mod_mod]
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hr.1] at h1
  · intro s hs
    simp only [mem_filter, mem_range] at hs
    have := (Nat.chineseRemainder co 1 s).2.2
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hs.1]

theorem SP_mod_three (n : ℕ) : SP (3 * n) (cond n) % 3 = ((range (3 * n)).filter (cond n)).card % 3 := by
  unfold SP
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Finset.sum_nat_mod, Finset.sum_nat_mod (s := filter _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_filter] at hr
  rw [Nat.mod_mod, hr.2.1]

theorem n_dvd_SP (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) : n ∣ SP (3 * n) (cond n) := by
  have hcop4 : Nat.Coprime 4 (3 * n) := by
    have : Nat.Coprime 2 (3 * n) := (Nat.coprime_two_left).mpr (Nat.odd_mul.mpr ⟨by decide, hodd⟩)
    exact Nat.Coprime.pow_left 2 this
  have h := mul_invariant_gen (3 * n) 4 (cond n) (by omega) hcop4 (by
    intro i
    unfold cond
    have h1 : 4 * i % (3 * n) % 3 = i % 3 := by
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 3 n)]; omega
    have h2 : Nat.Coprime (4 * i % (3 * n)) n ↔ Nat.Coprime i n := by
      rw [coprime_iff_mod, Nat.mod_mod_of_dvd _ (dvd_mul_left n 3), ← coprime_iff_mod,
        Nat.coprime_mul_iff_left]
      have : Nat.Coprime 4 n := by
        have : Nat.Coprime 2 n := (Nat.coprime_two_left).mpr hodd
        exact Nat.Coprime.pow_left 2 this
      exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩
    rw [h1, h2])
  have h3 : ((3 * SP (3 * n) (cond n) : ℕ) : ZMod (3 * n)) = 0 := by
    push_cast
    linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) h3

theorem three_dvd_totient (n : ℕ) (hn : 1 ≤ n) (h3 : ¬ 3 ∣ n) :
    3 ∣ n.totient ↔ ∃ p, p.Prime ∧ p ∣ n ∧ p % 3 = 1 := by
  have hmul := Nat.totient_mul_prod_primeFactors n
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hnotP : ¬ 3 ∣ ∏ p ∈ n.primeFactors, p := by
    intro h
    obtain ⟨p, hp, h3p⟩ := (Prime.dvd_finsetProd_iff hp3.prime _).mp h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : p = 3 := ((Nat.prime_dvd_prime_iff_eq hp3 hpp).mp h3p).symm
    exact h3 (this ▸ Nat.dvd_of_mem_primeFactors hp)
  constructor
  · intro h
    have : 3 ∣ n * ∏ p ∈ n.primeFactors, (p - 1) := by rw [← hmul]; exact Dvd.dvd.mul_right h _
    rcases (Nat.Prime.dvd_mul hp3).mp this with h' | h'
    · exact absurd h' h3
    · obtain ⟨p, hp, h3p⟩ := (Prime.dvd_finsetProd_iff hp3.prime _).mp h'
      have hpp := Nat.prime_of_mem_primeFactors hp
      refine ⟨p, hpp, Nat.dvd_of_mem_primeFactors hp, ?_⟩
      have := hpp.two_le
      omega
  · rintro ⟨p, hpp, hpn, hp1⟩
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpn, by omega⟩
    have : 3 ∣ ∏ q ∈ n.primeFactors, (q - 1) :=
      (Prime.dvd_finsetProd_iff hp3.prime _).mpr ⟨p, hmem, by have := hpp.two_le; omega⟩
    have h2 : 3 ∣ n.totient * ∏ p ∈ n.primeFactors, p := by rw [hmul]; exact Dvd.dvd.mul_left this _
    rcases (Nat.Prime.dvd_mul hp3).mp h2 with h' | h'
    · exact h'
    · exact absurd h' hnotP

theorem dvd_S_iff_S' (k : ℕ) (hk : 1 ≤ k) : k ∣ S k ↔ k ∣ S' k := by
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, S_modeq k hk]

/-- The case k = 3^(2b+1) n^2 (3 ∤ n): k ∣ S(k) iff n has a prime factor ≡ 1 (mod 3). -/
theorem square_case (b n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) (h3 : ¬ 3 ∣ n) :
    (3 ^ (2 * b + 1) * n ^ 2) ∣ S (3 ^ (2 * b + 1) * n ^ 2) ↔ ∃ p, p.Prime ∧ p ∣ n ∧ p % 3 = 1 := by
  have hk1 : 1 ≤ 3 ^ (2 * b + 1) * n ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [dvd_S_iff_S' _ hk1]
  have hS' : S' (3 ^ (2 * b + 1) * n ^ 2) =
      ∑ i ∈ range (3 ^ (2 * b + 1) * n ^ 2), if cond n i then i else 0 := by
    unfold S'
    apply Finset.sum_congr rfl
    intro i _
    simp only [jac_cond b n i hn]
  set B := 3 ^ (2 * b) * n with hB
  have hk : 3 ^ (2 * b + 1) * n ^ 2 = B * (3 * n) := by rw [hB]; ring
  have hBpos : 0 < B := by positivity
  rw [hS']
  set T := ∑ i ∈ range (3 ^ (2 * b + 1) * n ^ 2), if cond n i then i else 0 with hT
  have hblock : T * 2 = B * (B - 1) * (3 * n) * ((range (3 * n)).filter (cond n)).card +
      2 * B * SP (3 * n) (cond n) := by
    have := block_sum n B; rw [← hk] at this; exact this
  rw [hk]
  set C := ((range (3 * n)).filter (cond n)).card
  set SM := SP (3 * n) (cond n)
  have hkodd : Odd (B * (3 * n)) := by
    rw [← hk]; exact Odd.mul (Odd.pow (by decide)) (Odd.pow hodd)
  have h2cop : Nat.Coprime (B * (3 * n)) 2 := (Nat.coprime_two_left.mpr hkodd).symm
  have step1 : B * (3 * n) ∣ T ↔ B * (3 * n) ∣ T * 2 := (h2cop.dvd_mul_right).symm
  have step2 : B * (3 * n) ∣ T * 2 ↔ 3 * n ∣ 2 * SM := by
    rw [hblock]
    have hd : B * (3 * n) ∣ B * (B - 1) * (3 * n) * C := ⟨(B - 1) * C, by ring⟩
    rw [Nat.dvd_add_right hd, show 2 * B * SM = B * (2 * SM) by ring]
    exact Nat.mul_dvd_mul_iff_left hBpos
  have h3n : Nat.Coprime (3 * n) 2 := (Nat.coprime_two_left.mpr (Odd.mul (by decide) hodd)).symm
  have step3 : 3 * n ∣ 2 * SM ↔ 3 * n ∣ SM := h3n.dvd_mul_left
  have hnSM := n_dvd_SP n hn hodd
  have co : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have step4 : 3 * n ∣ SM ↔ 3 ∣ SM :=
    ⟨fun h => dvd_trans (dvd_mul_right 3 n) h, fun h => co.mul_dvd_of_dvd_of_dvd h hnSM⟩
  have step5 : 3 ∣ SM ↔ 3 ∣ C := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, SP_mod_three]
  have step6 : C = n.totient := card_cond n hn h3
  rw [step1, step2, step3, step4, step5, step6]
  exact three_dvd_totient n hn h3

theorem jac_split (u e N : ℕ) (hN : 1 ≤ N) :
    jacobiSym u (3 ^ e * N) = jacobiSym u 3 ^ e * jacobiSym u N := by
  have : NeZero (3 ^ e) := ⟨by positivity⟩
  have : NeZero N := ⟨by omega⟩
  rw [jacobiSym.mul_right, jacobiSym.pow_right]

theorem jac_of_mod_one (u N c : ℕ) (h : u = 1 + N * c) : jacobiSym u N = 1 := by
  rw [jacobiSym.mod_left' (a₂ := 1) (by subst h; push_cast; simp [Int.add_mul_emod_self_left]),
    jacobiSym.one_left]

theorem jac_two_mod_three (u : ℕ) (h : u % 3 = 2) : jacobiSym u 3 = -1 := by
  rw [jacobiSym.mod_left]
  have : (u : ℤ) % ((3 : ℕ) : ℤ) = 2 := by push_cast; omega
  rw [this]; norm_num [jacobiSym]

/-- Witness when the exponent of 3 is even. -/
theorem witness_even (e N : ℕ) (hN : 1 ≤ N) (h3 : ¬ 3 ∣ N) (he : Even e) :
    ∃ u : ℕ, jacobiSym u (3 ^ e * N) = 1 ∧ u % 3 = 2 := by
  have hr : N % 3 = 1 ∨ N % 3 = 2 := by omega
  obtain ⟨u, hu, hu3⟩ : ∃ u, (u = 1 + N * 1 ∨ u = 1 + N * 2) ∧ u % 3 = 2 := by
    rcases hr with h | h
    · exact ⟨1 + N * 1, Or.inl rfl, by omega⟩
    · exact ⟨1 + N * 2, Or.inr rfl, by omega⟩
  refine ⟨u, ?_, hu3⟩
  rw [jac_split u e N hN, jac_two_mod_three u hu3]
  rcases hu with h | h <;> rw [jac_of_mod_one u N _ h, he.neg_one_pow] <;> norm_num

/-- A Jacobi symbol value -1 modulo an odd non-square. -/
theorem exists_jac_neg_one (N : ℕ) (hN : 1 ≤ N) (hodd : Odd N) (hsq : ¬ IsSquare N) :
    ∃ v : ℕ, jacobiSym v N = -1 := by
  rw [Nat.isSquare_iff_even_factorization] at hsq
  push Not at hsq
  obtain ⟨p, hp, hpo⟩ := hsq
  rw [Nat.not_even_iff_odd] at hpo
  have : Fact p.Prime := ⟨hp⟩
  set a := N.factorization p
  have ha : 1 ≤ a := by rcases hpo with ⟨t, ht⟩; omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ N := (Nat.dvd_of_factorization_pos (by omega))
    rcases hodd with ⟨t, ht⟩; omega
  obtain ⟨w, hw⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hleg : legendreSym p (w.val : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]; simpa using hw
  have hwJ : jacobiSym (w.val : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]; exact hleg
  set r := N / p ^ a
  have hNr : p ^ a * r = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hco : Nat.Coprime (p ^ a) r := Nat.Coprime.pow_left a (Nat.coprime_ordCompl hp (by omega))
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, mul_zero] at hNr; omega
    · exact h
  obtain ⟨v, hv1, hv2⟩ := Nat.chineseRemainder hco w.val 1
  refine ⟨v, ?_⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero r := ⟨by omega⟩
  rw [← hNr, jacobiSym.mul_right, jacobiSym.pow_right]
  have hvp : jacobiSym v p = -1 := by
    rw [← hwJ]
    apply jacobiSym.mod_left'
    have : v ≡ w.val [MOD p] := Nat.ModEq.of_dvd (dvd_pow_self p (by omega)) hv1
    unfold Nat.ModEq at this
    exact_mod_cast this
  have hvr : jacobiSym v r = 1 := by
    have h2 := hv2
    unfold Nat.ModEq at h2
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast h2), jacobiSym.one_left]
  rw [hvp, hvr, hpo.neg_one_pow]; norm_num

/-- Witness when the exponent of 3 is odd and the 3-free part is not a square. -/
theorem witness_nonsq (e N : ℕ) (hN : 1 ≤ N) (hodd : Odd N) (h3 : ¬ 3 ∣ N) (he : Odd e)
    (hsq : ¬ IsSquare N) : ∃ u : ℕ, jacobiSym u (3 ^ e * N) = 1 ∧ u % 3 = 2 := by
  obtain ⟨v, hv⟩ := exists_jac_neg_one N hN hodd hsq
  have hc : v % 3 = 2 ∨ (v + N * 1) % 3 = 2 ∨ (v + N * 2) % 3 = 2 := by
    have h1 : N % 3 = 1 ∨ N % 3 = 2 := by omega
    have h2 : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
    have e1 : (v + N * 1) % 3 = (v % 3 + N % 3) % 3 := by rw [mul_one, Nat.add_mod]
    have e2 : (v + N * 2) % 3 = (v % 3 + 2 * (N % 3)) % 3 := by
      rw [Nat.add_mod, Nat.mul_mod, mul_comm]; simp [Nat.mul_mod]
    rw [e1, e2]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> simp [h1, h2]
  have key : ∀ c, (v + N * c) % 3 = 2 → ∃ u : ℕ, jacobiSym u (3 ^ e * N) = 1 ∧ u % 3 = 2 := by
    intro c hc
    refine ⟨v + N * c, ?_, hc⟩
    rw [jac_split _ e N hN, jac_two_mod_three _ hc, he.neg_one_pow]
    have : jacobiSym (v + N * c : ℕ) N = jacobiSym v N := by
      apply jacobiSym.mod_left'; push_cast; simp [Int.add_mul_emod_self_left]
    rw [this, hv]; norm_num
  rcases hc with h | h | h
  · exact key 0 (by simpa using h)
  · exact key 1 h
  · exact key 2 h

/-- A166102 = 3 · A166103: an odd k fails k ∣ A166100((k-1)/2) = S(k) exactly when
k = 3 m^2 with every prime factor of m equal to 3 or ≡ 5 (mod 6), i.e. m ∈ A166104. -/
theorem A166102_iff (k : ℕ) (hk : Odd k) :
    ¬ k ∣ S k ↔ ∃ m, k = 3 * m ^ 2 ∧ ∀ p, p.Prime → p ∣ m → p = 3 ∨ p % 6 = 5 := by
  have hk0 : k ≠ 0 := by rcases hk with ⟨t, ht⟩; omega
  constructor
  · intro hnd
    set e := k.factorization 3
    set N := k / 3 ^ e
    have hkN : 3 ^ e * N = k := Nat.ordProj_mul_ordCompl_eq_self k 3
    have hN3 : ¬ 3 ∣ N := Nat.not_dvd_ordCompl Nat.prime_three hk0
    have hN1 : 1 ≤ N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h, mul_zero] at hkN; omega
      · exact h
    have hNodd : Odd N := Odd.of_dvd_nat hk ⟨3 ^ e, by rw [← hkN]; ring⟩
    have he : Odd e := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨u, hu, hu3⟩ := witness_even e N hN1 hN3 hev
      exact hnd (dvd_S_of_witness k u hk (by rw [← hkN]; exact hu) hu3)
    have hsq : IsSquare N := by
      by_contra hns
      obtain ⟨u, hu, hu3⟩ := witness_nonsq e N hN1 hNodd hN3 he hns
      exact hnd (dvd_S_of_witness k u hk (by rw [← hkN]; exact hu) hu3)
    obtain ⟨n, hn⟩ := hsq
    obtain ⟨b, hb⟩ := he
    have hnodd : Odd n := (Nat.odd_mul.mp (hn ▸ hNodd)).1
    have hn1 : 1 ≤ n := hnodd.pos
    have hn3 : ¬ 3 ∣ n := fun h => hN3 (hn ▸ Dvd.dvd.mul_right h n)
    have hk' : k = 3 ^ (2 * b + 1) * n ^ 2 := by rw [← hkN, hn, hb]; ring
    have hsc := square_case b n hn1 hnodd hn3
    rw [← hk'] at hsc
    have hnone : ¬ ∃ p, p.Prime ∧ p ∣ n ∧ p % 3 = 1 := fun h => hnd (hsc.mpr h)
    refine ⟨3 ^ b * n, by rw [hk']; ring, ?_⟩
    intro p hp hpm
    rcases (Nat.Prime.dvd_mul hp).mp hpm with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    · right
      have hp3 : p ≠ 3 := fun h' => hn3 (h' ▸ h)
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr h)
      have h1 : p % 3 ≠ 1 := fun h' => hnone ⟨p, hp, h, h'⟩
      have h0 : p % 3 ≠ 0 := fun h' =>
        hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h')).symm
      have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      omega
  · rintro ⟨m, hm, hmp⟩ hdvd
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hk0 hm
    set b := m.factorization 3
    set n := m / 3 ^ b
    have hmn : 3 ^ b * n = m := Nat.ordProj_mul_ordCompl_eq_self m 3
    have hn3 : ¬ 3 ∣ n := Nat.not_dvd_ordCompl Nat.prime_three hm0
    have hmodd : Odd m := Odd.of_dvd_nat hk ⟨3 * m, by rw [hm]; ring⟩
    have hnodd : Odd n := Odd.of_dvd_nat hmodd ⟨3 ^ b, by rw [← hmn]; ring⟩
    have hn1 : 1 ≤ n := hnodd.pos
    have hk' : k = 3 ^ (2 * b + 1) * n ^ 2 := by rw [hm, ← hmn]; ring
    obtain ⟨p, hp, hpn, hp1⟩ := (square_case b n hn1 hnodd hn3).mp (hk' ▸ hdvd)
    rcases hmp p hp (dvd_trans hpn ⟨3 ^ b, by rw [← hmn]; ring⟩) with h | h
    · exact hn3 (h ▸ hpn)
    · omega

end OEIS_A166103

open OEIS_A166103
