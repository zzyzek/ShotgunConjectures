import Mathlib.NumberTheory.FermatPsp
import Mathlib.Algebra.Order.Ring.GeomSum

/-!
# Cipolla's pseudoprimes

For `b ≥ 2` and a prime `p > 2` with `p ∤ b (b² - 1)`,
`N = (b ^ (2p) - 1) / (b ² - 1) = ((b ^ p - 1)/(b - 1)) · ((b ^ p + 1)/(b + 1))`
is a Fermat pseudoprime to base `b`, and `N > p` (Cipolla 1904).

The proofs are Mathlib's (`Mathlib/NumberTheory/FermatPsp.lean`, Apache 2.0, author
Niels Voss), where these lemmas are `private`; they are copied here under public names,
with the identity `cipollaNum_eq` exposed.

* `cipollaNum b p := (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))`
* `cipollaNum_eq`: for odd `p`, `cipollaNum b p = (b ^ (2 * p) - 1) / (b ^ 2 - 1)`
* `cipolla_fermatPsp`, `cipolla_gt`, `cipolla`
-/

namespace OpenProblemsLib

open Nat

theorem a_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : b < (a ^ b - 1) / (a - 1) := by
  rw [← Nat.geomSum_eq ha]
  calc
    b = ∑ _ ∈ Finset.range b, (1 : ℕ) := by simp
    _ < _ := by
      refine Finset.sum_lt_sum (fun i hi => Nat.one_le_pow _ _ (by lia)) ?_
      exact ⟨1, Finset.mem_range.mpr (by lia), by simpa using! ha⟩

theorem b_id_helper {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : 2 ≤ (a ^ b + 1) / (a + 1) := by
  rw [Nat.le_div_iff_mul_le (Nat.zero_lt_succ _)]
  apply Nat.succ_le_succ
  calc
    2 * a + 1 ≤ a ^ 2 * a := by nlinarith
    _ = a ^ 3 := by rw [Nat.pow_succ a 2]
    _ ≤ a ^ b := pow_right_mono₀ (Nat.le_of_succ_le ha) hb

theorem AB_id_helper (b p : ℕ) (_ : 2 ≤ b) (hp : Odd p) :
    (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1)) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := by
  have q₁ : b - 1 ∣ b ^ p - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow b 1 p
  have q₂ : b + 1 ∣ b ^ p + 1 := by simpa only [one_pow] using hp.nat_add_dvd_pow_add_pow b 1
  convert Nat.div_mul_div_comm q₁ q₂ using 2 <;> rw [mul_comm (_ - 1), ← Nat.sq_sub_sq]
  ring_nf

/-- Used in the proof of `psp_from_prime_psp`
-/
theorem bp_helper {b p : ℕ} (hb : 0 < b) (hp : 1 ≤ p) :
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) :=
  have hi_bsquared : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  calc
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b ^ (2 * p) - (1 + (b ^ 2 - 1)) := by rw [Nat.sub_sub]
    _ = b ^ (2 * p) - (1 + b ^ 2 - 1) := by rw [Nat.add_sub_assoc hi_bsquared]
    _ = b ^ (2 * p) - b ^ 2 := by rw [Nat.add_sub_cancel_left]
    _ = b ^ (p * 2) - b ^ 2 := by rw [mul_comm]
    _ = (b ^ p) ^ 2 - b ^ 2 := by rw [pow_mul]
    _ = (b ^ p + b) * (b ^ p - b) := by rw [Nat.sq_sub_sq]
    _ = (b ^ p - b) * (b ^ p + b) := by rw [mul_comm]
    _ = (b ^ (p - 1 + 1) - b) * (b ^ p + b) := by rw [Nat.sub_add_cancel hp]
    _ = (b * b ^ (p - 1) - b) * (b ^ p + b) := by rw [pow_succ']
    _ = (b * b ^ (p - 1) - b * 1) * (b ^ p + b) := by rw [mul_one]
    _ = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by rw [Nat.mul_sub_left_distrib]

/-- Cipolla's number `((b ^ p - 1)/(b - 1)) · ((b ^ p + 1)/(b + 1))`. -/
def cipollaNum (b p : ℕ) : ℕ :=
  (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))

theorem cipollaNum_eq {b p : ℕ} (hb : 2 ≤ b) (hp : Odd p) :
    cipollaNum b p = (b ^ (2 * p) - 1) / (b ^ 2 - 1) :=
  AB_id_helper b p hb hp

theorem cipolla_fermatPsp {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_prime : p.Prime)
    (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b * (b ^ 2 - 1)) : FermatPsp (cipollaNum b p) b := by
  unfold cipollaNum
  set A := (b ^ p - 1) / (b - 1)
  set B := (b ^ p + 1) / (b + 1)
  -- Inequalities
  have hA : p < A := a_id_helper b_ge_two p_gt_two
  have hi_A : 1 < A := by lia
  have hi_B : 1 < B := b_id_helper b_ge_two p_gt_two
  have hi_b : 0 < b := by lia
  have hi_bsquared : 0 < b ^ 2 - 1 := by
    have := Nat.pow_le_pow_left b_ge_two 2
    lia
  have hi_bpowtwop : 1 ≤ b ^ (2 * p) := Nat.one_le_pow (2 * p) b hi_b
  have hi_bpowpsubone : 1 ≤ b ^ (p - 1) := Nat.one_le_pow (p - 1) b hi_b
  -- Other useful facts
  have p_odd : Odd p := p_prime.odd_of_ne_two p_gt_two.ne.symm
  have AB_not_prime : ¬Nat.Prime (A * B) := Nat.not_prime_mul hi_A.ne' hi_B.ne'
  have AB_id : A * B = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := AB_id_helper _ _ b_ge_two p_odd
  have hd : b ^ 2 - 1 ∣ b ^ (2 * p) - 1 := by
    simpa only [one_pow, pow_mul] using Nat.sub_dvd_pow_sub_pow _ 1 p
  -- We know that `A * B` is not prime, and that `1 < A * B`. Since two conditions of being
  -- pseudoprime are satisfied, we only need to show that `A * B` is probable prime to base `b`
  refine ⟨?_, AB_not_prime, one_lt_mul'' hi_A hi_B⟩
  -- Used to prove that `2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1)`.
  have ha₁ : (b ^ 2 - 1) * (A * B - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by
    apply_fun fun x => x * (b ^ 2 - 1) at AB_id
    rw [Nat.div_mul_cancel hd] at AB_id
    apply_fun fun x => x - (b ^ 2 - 1) at AB_id
    nth_rw 2 [← one_mul (b ^ 2 - 1)] at AB_id
    rw [← Nat.mul_sub_right_distrib, mul_comm] at AB_id
    rw [AB_id]
    exact bp_helper hi_b (by grind)
  -- If `b` is even, then `b^p` is also even, so `2 ∣ b^p + b`
  -- If `b` is odd, then `b^p` is also odd, so `2 ∣ b^p + b`
  have ha₂ : 2 ∣ b ^ p + b := by
    rw [← even_iff_two_dvd, Nat.even_add, Nat.even_pow' p_prime.ne_zero]
  -- Since `b` isn't divisible by `p`, `b` is coprime with `p`. we can use Fermat's Little Theorem
  -- to prove this.
  have ha₃ : p ∣ b ^ (p - 1) - 1 := by
    have : ¬p ∣ b := mt (fun h : p ∣ b => dvd_mul_of_dvd_left h _) not_dvd
    have : p.Coprime b := Or.resolve_right (Nat.coprime_or_dvd_of_prime p_prime b) this
    have : IsCoprime (b : ℤ) ↑p := this.symm.isCoprime
    have : ↑b ^ (p - 1) ≡ 1 [ZMOD ↑p] := Int.ModEq.pow_card_sub_one_eq_one p_prime this
    have : ↑p ∣ ↑b ^ (p - 1) - ↑1 := mod_cast Int.ModEq.dvd (Int.ModEq.symm this)
    exact mod_cast this
  -- Because `p - 1` is even, there is a `c` such that `2 * c = p - 1`. `Nat.sub_dvd_pow_sub_pow`
  -- implies that `b ^ c - 1 ∣ (b ^ c) ^ 2 - 1`, and `(b ^ c) ^ 2 = b ^ (p - 1)`.
  have ha₄ : b ^ 2 - 1 ∣ b ^ (p - 1) - 1 := by
    obtain ⟨k, hk⟩ := p_odd
    have : 2 ∣ p - 1 := ⟨k, by simp [hk]⟩
    obtain ⟨c, hc⟩ := this
    have : b ^ 2 - 1 ∣ (b ^ 2) ^ c - 1 := by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow _ 1 c
    have : b ^ 2 - 1 ∣ b ^ (2 * c) - 1 := by rwa [← pow_mul] at this
    rwa [← hc] at this
  -- Used to prove that `2 * p` divides `A * B - 1`
  have ha₅ : 2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1) := by
    suffices q : 2 * p * (b ^ 2 - 1) ∣ b * (b ^ (p - 1) - 1) * (b ^ p + b) by rwa [ha₁]
    -- We already proved that `b ^ 2 - 1 ∣ b ^ (p - 1) - 1`.
    -- Since `2 ∣ b ^ p + b` and `p ∣ b ^ p + b`, if we show that 2 and p are coprime, then we
    -- know that `2 * p ∣ b ^ p + b`
    have q₁ : Nat.Coprime p (b ^ 2 - 1) :=
      haveI q₂ : ¬p ∣ b ^ 2 - 1 := by
        rw [mul_comm] at not_dvd
        exact mt (fun h : p ∣ b ^ 2 - 1 => dvd_mul_of_dvd_left h _) not_dvd
      (Nat.Prime.coprime_iff_not_dvd p_prime).mpr q₂
    have q₂ : p * (b ^ 2 - 1) ∣ b ^ (p - 1) - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd q₁ ha₃ ha₄
    have q₃ : p * (b ^ 2 - 1) * 2 ∣ (b ^ (p - 1) - 1) * (b ^ p + b) := mul_dvd_mul q₂ ha₂
    have q₄ : p * (b ^ 2 - 1) * 2 ∣ b * ((b ^ (p - 1) - 1) * (b ^ p + b)) :=
      dvd_mul_of_dvd_right q₃ _
    rwa [mul_assoc, mul_comm, mul_assoc b]
  have ha₆ : 2 * p ∣ A * B - 1 := by
    rw [mul_comm] at ha₅
    exact Nat.dvd_of_mul_dvd_mul_left hi_bsquared ha₅
  -- `A * B` divides `b ^ (2 * p) - 1` because `A * B * (b ^ 2 - 1) = b ^ (2 * p) - 1`.
  -- This can be proven by multiplying both sides of `AB_id` by `b ^ 2 - 1`.
  have ha₇ : A * B ∣ b ^ (2 * p) - 1 := by
    use b ^ 2 - 1
    have : A * B * (b ^ 2 - 1) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) * (b ^ 2 - 1) :=
      congr($AB_id * (b ^ 2 - 1))
    simpa only [add_comm, Nat.div_mul_cancel hd, Nat.sub_add_cancel hi_bpowtwop] using this.symm
  -- Since `2 * p ∣ A * B - 1`, there is a number `q` such that `2 * p * q = A * B - 1`.
  -- By `Nat.sub_dvd_pow_sub_pow`, we know that `b ^ (2 * p) - 1 ∣ b ^ (2 * p * q) - 1`.
  -- This means that `b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1`.
  obtain ⟨q, hq⟩ := ha₆
  have ha₈ : b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1 := by
    simpa only [one_pow, pow_mul, hq] using Nat.sub_dvd_pow_sub_pow _ 1 q
  -- We have proved that `A * B ∣ b ^ (2 * p) - 1` and `b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1`.
  -- Therefore, `A * B ∣ b ^ (A * B - 1) - 1`.
  exact dvd_trans ha₇ ha₈

theorem cipolla_gt {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_gt_two : 2 < p) :
    p < cipollaNum b p := by
  unfold cipollaNum
  set A := (b ^ p - 1) / (b - 1)
  set B := (b ^ p + 1) / (b + 1)
  have hA : p < A := a_id_helper b_ge_two p_gt_two
  have hB : 0 < B := by
    have : 1 < B := b_id_helper b_ge_two p_gt_two
    lia
  exact hA.trans_le (Nat.le_mul_of_pos_right _ hB)

/-- **Cipolla**: `(b ^ (2p) - 1)/(b ^ 2 - 1)` is a Fermat pseudoprime to base `b`, larger
than `p`, for `b ≥ 2` and a prime `p > 2` not dividing `b (b ^ 2 - 1)`. -/
theorem cipolla {b p : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (hp2 : 2 < p)
    (hnd : ¬p ∣ b * (b ^ 2 - 1)) :
    FermatPsp ((b ^ (2 * p) - 1) / (b ^ 2 - 1)) b ∧ p < (b ^ (2 * p) - 1) / (b ^ 2 - 1) := by
  rw [← cipollaNum_eq hb (hp.odd_of_ne_two (by omega))]
  exact ⟨cipolla_fermatPsp hb hp hp2 hnd, cipolla_gt hb hp2⟩

end OpenProblemsLib
