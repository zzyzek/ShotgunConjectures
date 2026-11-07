/-
OEIS A202150 / A202146: odd coefficients of A(q) = Sum q^n (q;q)_n/(q;q^2)_{n+1} sit at 3m(m+1).

Checked here.
* Gaussian binomials: `qb_prod`, `qb_symm`, `qb_rule2`; integer lower index `qz` with
  `qz_symm`, `qz_rule1`, `qz_rule2`, and the two-step rules `two_step_A`, `two_step_B`.
* E_b(n) = Sum_j (-1)^j q^(3j^2+bj) [2n+1, n-2j] (`E w1`, `E w3`, finsum over ℤ):
  recurrences `E1_succ`, `E3_succ` and closed forms `E_closed`
  (E_1(n) = (-q;q)_n, E_3(n) = q^n (-q;q)_n).
* `bailey_pair`: E_1(n) + E_3(n) = (-q;q)_n (1 + q^n), the defining identity of the Bailey
  pair relative to a = q used in README step 2.
* `A202146` (the entry's g.f. written as Sum q^n (q;q)_n/(q;q^2)_{n+1}), `mod2_reduction`
  (A202146(k) ≡ [q^k] Sum (-q)^n (-q;q)_n/(q;q^2)_{n+1} mod 2), and
  `A202146_parity_of_star`: given identity (*) (`sumS TL = theta`), A202146(k) is odd iff
  k = 3m(m+1).
* `A202146_entry` (the coefficients of the entry's g.f.
  1/(1-x) + Sum_{n>=1} x^n/(1-x) Product_{k=1..n} (1-x^k)/(1-x^(2k+1)), written literally with
  `entryTerm`) and `A202146_entry_eq` (it equals `A202146`).
* Identity (*) `star : sumS TL = theta`, i.e.
  Sum_n (-q)^n (-q;q)_n/(q;q^2)_{n+1} = Sum_m (-1)^m q^{3m(m+1)}, by Bailey's lemma with
  a = q, rho1 = q, rho2 = -1: `TL_succ` (the Bailey pair `bailey_pair` with the alpha_n of
  README step 2 as the terms W_t, W_{-t-1}), `sum_TL` (interchange of the sums), `In_pos`,
  `In_zero` (inner sums from the library q-Gauss sum `OpenProblemsLib.QSeries.qGaussSum_mul`),
  `pair_zero`, `pair_succ` (pairing into (-1)^t q^{3t(t+1)}); infinite sums by truncation mod X^M.
* Main theorem `A202146_entry_parity`: A202146(k) is odd iff k = 3m(m+1); hence A202150, defined
  by a(n) = A202146(3n(n+1)), lists exactly the odd terms of A202146.
Not checked here: nothing beyond reading the entry's g.f. as `entryTerm`.
-/
import Mathlib
import OpenProblemsLib.QSeries

open Polynomial Finset

namespace A202150

/-- (q;q)_n = (1-q)(1-q^2)...(1-q^n). -/
noncomputable def qp (n : ℕ) : ℤ[X] := ∏ i ∈ range n, (1 - X ^ (i + 1))

/-- Gaussian binomial [N, k] by the rule [N+1, k+1] = [N, k] + q^(k+1) [N, k+1]. -/
noncomputable def qb : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | N + 1, k + 1 => qb N k + X ^ (k + 1) * qb N (k + 1)

lemma qb_succ_succ (N k : ℕ) : qb (N + 1) (k + 1) = qb N k + X ^ (k + 1) * qb N (k + 1) := rfl

lemma qb_eq_zero (N k : ℕ) (h : N < k) : qb N k = 0 := by
  induction N generalizing k with
  | zero => obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; rfl
  | succ N ih =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [qb_succ_succ, ih k (by omega), ih (k + 1) (by omega)]; simp

lemma qp_succ (n : ℕ) : qp (n + 1) = qp n * (1 - X ^ (n + 1)) := by
  unfold qp; rw [prod_range_succ]

lemma one_sub_X_pow_ne_zero (i : ℕ) : (1 - X ^ (i + 1) : ℤ[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 2) h
  simp at this
  have h2 : (1 : ℤ) < 2 ^ (i + 1) := one_lt_pow₀ (by norm_num) (by omega)
  omega

lemma qp_ne_zero (n : ℕ) : qp n ≠ 0 := by
  unfold qp
  rw [prod_ne_zero_iff]
  intro i _; exact one_sub_X_pow_ne_zero i

lemma qb_prod (N k : ℕ) (h : k ≤ N) : qb N k * qp k * qp (N - k) = qp N := by
  induction N generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this; simp [qb, qp]
  | succ N ih =>
    rcases k with _ | k
    · simp [qb, qp]
    · rw [qb_succ_succ, show N + 1 - (k + 1) = N - k by omega]
      rcases Nat.lt_or_ge k N with hk | hk
      · have h1 := ih k (by omega)
        have h2 := ih (k + 1) (by omega)
        set a := N - (k + 1) with ha
        have e : N - k = a + 1 := by omega
        rw [e] at h1 ⊢
        have hq : qp (a + 1) = qp a * (1 - X ^ (a + 1)) := qp_succ a
        have T1 : qb N k * (qp k * (1 - X ^ (k + 1))) * qp (a + 1) = qp N * (1 - X ^ (k + 1)) := by
          rw [← h1]; ring
        have T2 : X ^ (k + 1) * qb N (k + 1) * (qp k * (1 - X ^ (k + 1))) * qp (a + 1) =
            X ^ (k + 1) * (1 - X ^ (a + 1)) * qp N := by
          rw [← qp_succ k, hq, ← h2]; ring
        have e2 : (X : ℤ[X]) ^ (k + 1) * X ^ (a + 1) = X ^ (N + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [qp_succ k, qp_succ N]
        linear_combination T1 + T2 - qp N * e2
      · have hkN : k = N := by omega
        subst hkN
        rw [qb_eq_zero k (k + 1) (by omega), Nat.sub_self, qp_succ]
        have h1 := ih k le_rfl
        rw [Nat.sub_self] at h1
        linear_combination (1 - X ^ (k + 1)) * h1

lemma ite_t {α : Type*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

lemma qb_zero (N : ℕ) : qb N 0 = 1 := by cases N <;> rfl

lemma qb_symm (N k : ℕ) (h : k ≤ N) : qb N k = qb N (N - k) := by
  have h1 := qb_prod N k h
  have h2 := qb_prod N (N - k) (by omega)
  rw [show N - (N - k) = k by omega] at h2
  have hne : qp k * qp (N - k) ≠ 0 := mul_ne_zero (qp_ne_zero _) (qp_ne_zero _)
  apply mul_right_cancel₀ hne
  calc qb N k * (qp k * qp (N - k)) = qp N := by rw [← h1]; ring
    _ = qb N (N - k) * (qp k * qp (N - k)) := by rw [← h2]; ring

lemma qb_rule2 (N k : ℕ) : qb (N + 1) (k + 1) = X ^ (N - k) * qb N k + qb N (k + 1) := by
  rcases Nat.lt_or_ge N k with hk | hk
  · rw [qb_eq_zero _ _ (by omega), qb_eq_zero N k hk, qb_eq_zero N (k + 1) (by omega)]; ring
  have hne : qp (k + 1) * qp (N - k) ≠ 0 := mul_ne_zero (qp_ne_zero _) (qp_ne_zero _)
  apply mul_right_cancel₀ hne
  have hL := qb_prod (N + 1) (k + 1) (by omega)
  rw [show N + 1 - (k + 1) = N - k by omega] at hL
  have h1 := qb_prod N k hk
  rw [← mul_assoc, hL, qp_succ N]
  rcases Nat.lt_or_ge k N with hkN | hkN
  · have h2 := qb_prod N (k + 1) (by omega)
    have e : N - k = (N - (k + 1)) + 1 := by omega
    rw [e] at h1 ⊢
    have e2 : (X : ℤ[X]) ^ (N - (k + 1) + 1) * X ^ (k + 1) = X ^ (N + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [qp_succ k, qp_succ (N - (k + 1))]
    rw [qp_succ] at h1
    rw [qp_succ k] at h2
    linear_combination (-(X ^ (N - (k + 1) + 1) * (1 - X ^ (k + 1)))) * h1
      - (1 - X ^ (N - (k + 1) + 1)) * h2 + qp N * e2
  · have hkN' : k = N := by omega
    subst hkN'
    rw [qb_eq_zero k (k + 1) (by omega), Nat.sub_self] at *
    rw [qp_succ k]
    linear_combination (-(1 - X ^ (k + 1))) * h1

/-- Gaussian binomial with an integer lower index (0 outside 0..N). -/
noncomputable def qz (N : ℕ) (k : ℤ) : ℤ[X] := if 0 ≤ k then qb N k.toNat else 0

lemma qz_neg (N : ℕ) (k : ℤ) (h : k < 0) : qz N k = 0 := by simp [qz]; omega

lemma qz_big (N : ℕ) (k : ℤ) (h : (N : ℤ) < k) : qz N k = 0 := by
  rw [qz, ite_t (by omega)]; exact qb_eq_zero _ _ (by omega)

lemma qz_symm (N : ℕ) (k : ℤ) : qz N k = qz N (N - k) := by
  rcases lt_or_ge k 0 with h | h
  · rw [qz_neg N k h, qz_big N _ (by omega)]
  rcases lt_or_ge (N : ℤ) k with h' | h'
  · rw [qz_big N k h', qz_neg N _ (by omega)]
  rw [qz, qz, ite_t h, ite_t (by omega), qb_symm N k.toNat (by omega)]
  congr 1; omega

lemma qz_rule1 (N : ℕ) (k : ℤ) :
    qz (N + 1) (k + 1) = qz N k + X ^ (k + 1).toNat * qz N (k + 1) := by
  rcases lt_or_ge k (-1) with h | h
  · rw [qz_neg _ _ (by omega), qz_neg _ _ (by omega), qz_neg _ _ (by omega)]; ring
  rcases eq_or_lt_of_le h with h | h
  · subst h; simp [qz, qb_zero]
  rw [qz, qz, qz, ite_t (by omega), ite_t (by omega), ite_t (by omega),
    show (k + 1).toNat = k.toNat + 1 by omega, qb_succ_succ]

lemma qz_rule2 (N : ℕ) (k : ℤ) :
    qz (N + 1) (k + 1) = X ^ ((N : ℤ) - k).toNat * qz N k + qz N (k + 1) := by
  rcases lt_or_ge k (-1) with h | h
  · rw [qz_neg _ _ (by omega), qz_neg _ _ (by omega), qz_neg _ _ (by omega)]; ring
  rcases eq_or_lt_of_le h with h | h
  · subst h; simp [qz, qb_zero]
  rw [qz, qz, qz, ite_t (by omega), ite_t (by omega), ite_t (by omega),
    show (k + 1).toNat = k.toNat + 1 by omega, qb_rule2,
    show ((N : ℤ) - k).toNat = N - k.toNat by omega]

/-! ## The finite identities E_1(n) = (-q;q)_n and E_3(n) = q^n (-q;q)_n -/

/-- (-1)^j as a polynomial. -/
noncomputable def sg (j : ℤ) : ℤ[X] := if Even j then 1 else -1

lemma sg_neg (j : ℤ) : sg (-j) = sg j := by simp [sg, even_neg]

lemma sg_succ (j : ℤ) : sg (j + 1) = - sg j := by
  unfold sg; by_cases h : Even j <;> simp [h]

/-- Weights (-1)^j q^(3j^2+bj), b = 1, 3. -/
noncomputable def w1 (j : ℤ) : ℤ[X] := sg j * X ^ (3 * (j * j) + j).toNat
noncomputable def w3 (j : ℤ) : ℤ[X] := sg j * X ^ (3 * (j * j) + 3 * j).toNat

/-- E_w(n) = Sum_j w(j) [2n+1, n-2j]. -/
noncomputable def E (w : ℤ → ℤ[X]) (n : ℕ) : ℤ[X] := ∑ᶠ j : ℤ, w j * qz (2 * n + 1) (n - 2 * j)

lemma qz_ne (N : ℕ) (k : ℤ) (h : qz N k ≠ 0) : 0 ≤ k ∧ k ≤ N := by
  constructor
  · by_contra h'; exact h (qz_neg N k (by omega))
  · by_contra h'; exact h (qz_big N k (by omega))

lemma fin_supp (f : ℤ → ℤ[X]) (N : ℕ) (c : ℤ) :
    (Function.support fun j => f j * qz N (c - 2 * j)).Finite := by
  apply (Set.finite_Icc (-(|c| + N)) (|c| + N)).subset
  intro j hj
  rw [Function.mem_support] at hj
  have h := qz_ne N _ (fun h0 => hj (by rw [h0, mul_zero]))
  rw [Set.mem_Icc]; constructor <;> cases abs_cases c <;> omega

lemma xpow (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = c) :
    (X : ℤ[X]) ^ a.toNat * X ^ b.toNat = X ^ c.toNat := by
  rw [← pow_add]; congr 1; omega

lemma e1 (j : ℤ) : 0 ≤ 3 * (j * j) + j := by nlinarith [sq_nonneg (j : ℤ), sq_nonneg (j + 1)]
lemma e3 (j : ℤ) : 0 ≤ 3 * (j * j) + 3 * j := by nlinarith [sq_nonneg (j : ℤ), sq_nonneg (j + 1)]

/-- Reindexing by i ↦ -i-1 and i ↦ -i. -/
def eNegSucc : ℤ ≃ ℤ := ⟨fun i => -i - 1, fun i => -i - 1, fun i => by ring, fun i => by ring⟩
def eNeg : ℤ ≃ ℤ := ⟨fun i => -i, fun i => -i, fun i => by ring, fun i => by ring⟩

lemma finsum_reindex (e : ℤ ≃ ℤ) (f : ℤ → ℤ[X]) : ∑ᶠ j, f j = ∑ᶠ i, f (e i) :=
  (finsum_comp_equiv e).symm

/-- Pieces of the two-step recurrences. -/
lemma P_sym (n : ℕ) (j : ℤ) : qz (2 * n + 1) (n - 1 - 2 * j) = qz (2 * n + 1) (n - 2 * (-j - 1)) := by
  rw [qz_symm]; congr 1; push_cast; ring

lemma P_sym' (n : ℕ) (j : ℤ) : qz (2 * n + 1) (n + 1 - 2 * j) = qz (2 * n + 1) (n - 2 * (-j)) := by
  rw [qz_symm]; congr 1; push_cast; ring

lemma two_step_B (N : ℕ) (k : ℤ) : qz (N + 1 + 1) (k + 1) =
    X ^ ((N : ℤ) - (k - 1)).toNat * qz N (k - 1) + qz N k +
    X ^ (k + 1).toNat * (X ^ ((N : ℤ) - k).toNat * qz N k + qz N (k + 1)) := by
  rw [qz_rule1 (N + 1) k, qz_rule2 N k]
  have h := qz_rule2 N (k - 1)
  rw [sub_add_cancel] at h
  rw [h]

lemma two_step_A (N : ℕ) (k : ℤ) : qz (N + 1 + 1) (k + 1) =
    qz N (k - 1) + X ^ k.toNat * qz N k + X ^ (k + 1).toNat * (qz N k + X ^ (k + 1).toNat * qz N (k + 1)) := by
  rw [qz_rule1 (N + 1) k, qz_rule1 N k]
  have h := qz_rule1 N (k - 1)
  rw [sub_add_cancel] at h
  rw [h]

lemma E_succ_arg (n : ℕ) (j : ℤ) :
    qz (2 * (n + 1) + 1) (((n + 1 : ℕ) : ℤ) - 2 * j) = qz (2 * n + 1 + 1 + 1) ((n - 2 * j) + 1) := by
  congr 1
  push_cast; ring

lemma sym1 (n : ℕ) (i : ℤ) : qz (2 * n + 1) (n + 2 * i + 1) = qz (2 * n + 1) (n - 2 * i) := by
  rw [qz_symm]; congr 1; push_cast; ring

lemma fin_supp2 (f : ℤ → ℤ[X]) (N : ℕ) (g : ℤ → ℤ) (a : ℤ) (hg : ∀ j, |j| > a → (g j < 0 ∨ (N : ℤ) < g j)) :
    (Function.support fun j => f j * qz N (g j)).Finite := by
  apply (Set.finite_Icc (-a) a).subset
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Icc]
  by_contra hc
  have : |j| > a := by rw [gt_iff_lt, lt_abs]; omega
  rcases hg j this with h | h
  · exact hj (by rw [qz_neg _ _ h, mul_zero])
  · exact hj (by rw [qz_big _ _ h, mul_zero])

lemma xpow2 (a b c : ℤ) (m : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b = m + c) :
    (X : ℤ[X]) ^ a.toNat * X ^ b.toNat = X ^ m * X ^ c.toNat := by
  rw [← pow_add, ← pow_add]; congr 1; omega

lemma xpow1 (a c : ℤ) (m : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c) (h : a = m + c) :
    (X : ℤ[X]) ^ a.toNat = X ^ m * X ^ c.toNat := by
  rw [← pow_add]; congr 1; omega

lemma neg_sq' (i : ℤ) : 0 ≤ 3 * ((-(i + 1)) * (-(i + 1))) + -(i + 1) := by nlinarith [sq_nonneg (i + 1)]
lemma neg_sq3 (i : ℤ) : 0 ≤ 3 * ((-(i + 1)) * (-(i + 1))) + 3 * -(i + 1) := by
  rcases le_or_gt 0 i with h | h <;> nlinarith
lemma negi1 (i : ℤ) : 0 ≤ 3 * ((-i) * (-i)) + -i := by nlinarith [sq_nonneg i]
lemma negi3 (i : ℤ) : 0 ≤ 3 * ((-i) * (-i)) + 3 * -i := by
  rcases le_or_gt 1 i with h | h <;> nlinarith

/-! Pieces for E_1(n+1). N = 2n+1, k = n - 2j. -/

lemma pA1 (n : ℕ) : ∑ᶠ j : ℤ, (w1 j * X ^ (((2 * n + 1 : ℕ) : ℤ) - ((n - 2 * j) - 1)).toNat) *
    qz (2 * n + 1) ((n - 2 * j) - 1) = -(X ^ (n + 2) * E w3 n) := by
  rw [finsum_reindex eNegSucc, E, mul_finsum, ← finsum_neg_distrib]
  congr 1; funext i
  simp only [eNegSucc, Equiv.coe_fn_mk]
  rw [show ((n : ℤ) - 2 * (-i - 1)) - 1 = n + 2 * i + 1 by ring, sym1]
  by_cases hz : qz (2 * n + 1) (n - 2 * i) = 0
  · simp [hz]
  have hb := qz_ne _ _ hz
  push_cast at hb ⊢
  unfold w1 w3
  rw [show -i - 1 = -(i + 1) by ring, sg_neg, sg_succ]
  have key := xpow2 (3 * ((-(i + 1)) * (-(i + 1))) + -(i + 1)) (2 * n + 1 - (n + 2 * i + 1))
    (3 * (i * i) + 3 * i) (n + 2) (neg_sq' i) (by omega) (e3 i) (by push_cast; ring)
  linear_combination (-sg i * qz (2 * n + 1) (n - 2 * i)) * key

lemma pB1 (n : ℕ) : ∑ᶠ j : ℤ, w1 j * qz (2 * n + 1) (n - 2 * j) = E w1 n := rfl

lemma pC1 (n : ℕ) : ∑ᶠ j : ℤ, (w1 j * (X ^ ((n - 2 * j) + 1).toNat *
    X ^ (((2 * n + 1 : ℕ) : ℤ) - (n - 2 * j)).toNat)) * qz (2 * n + 1) (n - 2 * j) =
    X ^ (2 * n + 2) * E w1 n := by
  rw [E, mul_finsum]
  congr 1; funext j
  by_cases hz : qz (2 * n + 1) (n - 2 * j) = 0
  · simp [hz]
  have hb := qz_ne _ _ hz
  push_cast at hb ⊢
  have key : (X : ℤ[X]) ^ ((n - 2 * j) + 1).toNat * X ^ (2 * (n : ℤ) + 1 - (n - 2 * j)).toNat =
      X ^ (2 * n + 2) := by
    rw [← pow_add]; congr 1; omega
  unfold w1
  linear_combination (sg j * X ^ (3 * (j * j) + j).toNat * qz (2 * n + 1) (n - 2 * j)) * key

lemma pD1 (n : ℕ) : ∑ᶠ j : ℤ, (w1 j * X ^ ((n - 2 * j) + 1).toNat) * qz (2 * n + 1) ((n - 2 * j) + 1) =
    X ^ (n + 1) * E w1 n := by
  rw [finsum_reindex eNeg, E, mul_finsum]
  congr 1; funext i
  simp only [eNeg, Equiv.coe_fn_mk]
  rw [show ((n : ℤ) - 2 * -i) + 1 = n + 2 * i + 1 by ring, sym1]
  by_cases hz : qz (2 * n + 1) (n - 2 * i) = 0
  · simp [hz]
  have hb := qz_ne _ _ hz
  push_cast at hb ⊢
  unfold w1
  rw [sg_neg]
  have key := xpow2 (3 * ((-i) * (-i)) + -i) (n + 2 * i + 1) (3 * (i * i) + i) (n + 1)
    (negi1 i) (by omega) (e1 i) (by push_cast; ring)
  linear_combination (sg i * qz (2 * n + 1) (n - 2 * i)) * key

/-! Pieces for E_3(n+1). -/

lemma pA3 (n : ℕ) : ∑ᶠ j : ℤ, w3 j * qz (2 * n + 1) ((n - 2 * j) - 1) = -E w3 n := by
  rw [finsum_reindex eNegSucc, E, ← finsum_neg_distrib]
  congr 1; funext i
  simp only [eNegSucc, Equiv.coe_fn_mk]
  rw [show ((n : ℤ) - 2 * (-i - 1)) - 1 = n + 2 * i + 1 by ring, sym1]
  unfold w3
  rw [show -i - 1 = -(i + 1) by ring, sg_neg, sg_succ,
    show 3 * ((-(i + 1)) * (-(i + 1))) + 3 * -(i + 1) = 3 * (i * i) + 3 * i by ring]
  ring

lemma pB3 (n : ℕ) : ∑ᶠ j : ℤ, (w3 j * X ^ (n - 2 * j).toNat) * qz (2 * n + 1) (n - 2 * j) =
    X ^ n * E w1 n := by
  rw [E, mul_finsum]
  congr 1; funext j
  by_cases hz : qz (2 * n + 1) (n - 2 * j) = 0
  · simp [hz]
  have hb := qz_ne _ _ hz
  push_cast at hb
  unfold w1 w3
  have key := xpow2 (3 * (j * j) + 3 * j) (n - 2 * j) (3 * (j * j) + j) n (e3 j) (by omega) (e1 j)
    (by ring)
  linear_combination (sg j * qz (2 * n + 1) (n - 2 * j)) * key

lemma pC3 (n : ℕ) : ∑ᶠ j : ℤ, (w3 j * X ^ ((n - 2 * j) + 1).toNat) * qz (2 * n + 1) (n - 2 * j) =
    X ^ (n + 1) * E w1 n := by
  rw [E, mul_finsum]
  congr 1; funext j
  by_cases hz : qz (2 * n + 1) (n - 2 * j) = 0
  · simp [hz]
  have hb := qz_ne _ _ hz
  push_cast at hb
  unfold w1 w3
  have key := xpow2 (3 * (j * j) + 3 * j) (n - 2 * j + 1) (3 * (j * j) + j) (n + 1) (e3 j) (by omega)
    (e1 j) (by push_cast; ring)
  linear_combination (sg j * qz (2 * n + 1) (n - 2 * j)) * key

lemma pD3 (n : ℕ) : ∑ᶠ j : ℤ, (w3 j * (X ^ ((n - 2 * j) + 1).toNat * X ^ ((n - 2 * j) + 1).toNat)) *
    qz (2 * n + 1) ((n - 2 * j) + 1) = X ^ (2 * n + 2) * E w1 n := by
  rw [finsum_reindex eNeg, E, mul_finsum]
  congr 1; funext i
  simp only [eNeg, Equiv.coe_fn_mk]
  rw [show ((n : ℤ) - 2 * -i) + 1 = n + 2 * i + 1 by ring, sym1]
  by_cases hz : qz (2 * n + 1) (n - 2 * i) = 0
  · simp [hz]
  have hb := qz_ne _ _ hz
  push_cast at hb
  unfold w1 w3
  rw [sg_neg]
  have k1 : (X : ℤ[X]) ^ (3 * ((-i) * (-i)) + 3 * -i).toNat * (X ^ ((n : ℤ) + 2 * i + 1).toNat *
      X ^ ((n : ℤ) + 2 * i + 1).toNat) = X ^ (2 * n + 2) * X ^ (3 * (i * i) + i).toNat := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1
    have := negi3 i; have := e1 i
    have h : 3 * ((-i) * (-i)) + 3 * -i + 2 * ((n : ℤ) + 2 * i + 1) = 2 * n + 2 + (3 * (i * i) + i) := by
      ring
    omega
  linear_combination (sg i * qz (2 * n + 1) (n - 2 * i)) * k1

lemma supp (f : ℤ → ℤ[X]) (n : ℕ) (c : ℤ) (hc : -1 ≤ c ∧ c ≤ 1) :
    (Function.support fun j => f j * qz (2 * n + 1) ((n - 2 * j) + c)).Finite :=
  fin_supp2 f (2 * n + 1) (fun j => (n - 2 * j) + c) (n + 2) (by
    intro j hj
    rcases abs_cases j with ⟨h1, _⟩ | ⟨h1, _⟩ <;> push_cast <;> omega)

lemma finsum_add4 (f1 f2 f3 f4 : ℤ → ℤ[X]) (h1 : (Function.support f1).Finite)
    (h2 : (Function.support f2).Finite) (h3 : (Function.support f3).Finite)
    (h4 : (Function.support f4).Finite) :
    ∑ᶠ j, (f1 j + f2 j + f3 j + f4 j) = ∑ᶠ j, f1 j + ∑ᶠ j, f2 j + ∑ᶠ j, f3 j + ∑ᶠ j, f4 j := by
  have h12 : (Function.support fun j => f1 j + f2 j).Finite :=
    (h1.union h2).subset (Function.support_add _ _)
  have h123 : (Function.support fun j => f1 j + f2 j + f3 j).Finite :=
    (h12.union h3).subset (Function.support_add _ _)
  rw [finsum_add_distrib h123 h4, finsum_add_distrib h12 h3, finsum_add_distrib h1 h2]

theorem E1_succ (n : ℕ) : E w1 (n + 1) =
    -(X ^ (n + 2) * E w3 n) + E w1 n + X ^ (2 * n + 2) * E w1 n + X ^ (n + 1) * E w1 n := by
  rw [← pA1, ← pB1, ← pC1, ← pD1]
  have hpt : ∀ j : ℤ, w1 j * qz (2 * (n + 1) + 1) (((n + 1 : ℕ) : ℤ) - 2 * j) =
      (w1 j * X ^ (((2 * n + 1 : ℕ) : ℤ) - ((n - 2 * j) - 1)).toNat) * qz (2 * n + 1) ((n - 2 * j) - 1)
      + w1 j * qz (2 * n + 1) (n - 2 * j)
      + (w1 j * (X ^ ((n - 2 * j) + 1).toNat * X ^ (((2 * n + 1 : ℕ) : ℤ) - (n - 2 * j)).toNat)) *
          qz (2 * n + 1) (n - 2 * j)
      + (w1 j * X ^ ((n - 2 * j) + 1).toNat) * qz (2 * n + 1) ((n - 2 * j) + 1) := by
    intro j
    rw [E_succ_arg, two_step_B]
    ring
  rw [E]
  simp_rw [hpt]
  have s1 := supp (fun j => w1 j * X ^ (((2 * n + 1 : ℕ) : ℤ) - ((n - 2 * j) - 1)).toNat) n (-1)
    (by norm_num)
  have s2 := supp w1 n 0 (by norm_num)
  have s3 := supp (fun j => w1 j * (X ^ ((n - 2 * j) + 1).toNat *
    X ^ (((2 * n + 1 : ℕ) : ℤ) - (n - 2 * j)).toNat)) n 0 (by norm_num)
  have s4 := supp (fun j => w1 j * X ^ ((n - 2 * j) + 1).toNat) n 1 (by norm_num)
  simp only [add_zero, ← sub_eq_add_neg] at s1 s2 s3 s4
  exact finsum_add4 _ _ _ _ s1 s2 s3 s4

theorem E3_succ (n : ℕ) : E w3 (n + 1) =
    -E w3 n + X ^ n * E w1 n + X ^ (n + 1) * E w1 n + X ^ (2 * n + 2) * E w1 n := by
  rw [← pA3, ← pB3, ← pC3, ← pD3]
  have hpt : ∀ j : ℤ, w3 j * qz (2 * (n + 1) + 1) (((n + 1 : ℕ) : ℤ) - 2 * j) =
      w3 j * qz (2 * n + 1) ((n - 2 * j) - 1)
      + (w3 j * X ^ (n - 2 * j).toNat) * qz (2 * n + 1) (n - 2 * j)
      + (w3 j * X ^ ((n - 2 * j) + 1).toNat) * qz (2 * n + 1) (n - 2 * j)
      + (w3 j * (X ^ ((n - 2 * j) + 1).toNat * X ^ ((n - 2 * j) + 1).toNat)) *
          qz (2 * n + 1) ((n - 2 * j) + 1) := by
    intro j
    rw [E_succ_arg, two_step_A]
    ring
  rw [E]
  simp_rw [hpt]
  have s1 := supp w3 n (-1) (by norm_num)
  have s2 := supp (fun j => w3 j * X ^ (n - 2 * j).toNat) n 0 (by norm_num)
  have s3 := supp (fun j => w3 j * X ^ ((n - 2 * j) + 1).toNat) n 0 (by norm_num)
  have s4 := supp (fun j => w3 j * (X ^ ((n - 2 * j) + 1).toNat * X ^ ((n - 2 * j) + 1).toNat)) n 1
    (by norm_num)
  simp only [add_zero, ← sub_eq_add_neg] at s1 s2 s3 s4
  exact finsum_add4 _ _ _ _ s1 s2 s3 s4

/-- (-q;q)_n. -/
noncomputable def pm (n : ℕ) : ℤ[X] := ∏ i ∈ range n, (1 + X ^ (i + 1))

lemma E_zero (w : ℤ → ℤ[X]) (hw : w 0 = 1) : E w 0 = 1 := by
  rw [E, finsum_eq_single _ 0]
  · simp [hw, qz, qb_zero]
  · intro j hj
    have : qz (2 * 0 + 1) ((0 : ℕ) - 2 * j) = 0 := by
      rcases lt_or_gt_of_ne hj with h | h
      · exact qz_big _ _ (by push_cast; omega)
      · exact qz_neg _ _ (by push_cast; omega)
    rw [this, mul_zero]

/-- The finite identities: E_1(n) = (-q;q)_n and E_3(n) = q^n (-q;q)_n. -/
theorem E_closed (n : ℕ) : E w1 n = pm n ∧ E w3 n = X ^ n * pm n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [E_zero w1 (by simp [w1, sg])]; simp [pm]
    · rw [E_zero w3 (by simp [w3, sg])]; simp [pm]
  | succ n ih =>
    have hp : pm (n + 1) = pm n * (1 + X ^ (n + 1)) := by unfold pm; rw [prod_range_succ]
    refine ⟨?_, ?_⟩
    · rw [E1_succ, ih.1, ih.2, hp]; ring
    · rw [E3_succ, ih.1, ih.2, hp]; ring

/-- The Bailey-pair identity: Sum_j (-1)^j (q^(3j^2+j) + q^(3j^2+3j)) [2n+1, n-2j] = (-q;q)_n (1+q^n). -/
theorem bailey_pair (n : ℕ) : E w1 n + E w3 n = pm n * (1 + X ^ n) := by
  rw [(E_closed n).1, (E_closed n).2]; ring

/-! ## The g.f. of A202146 and the reduction mod 2 -/

/-- (q;q^2)_{n+1} = (1-q)(1-q^3)...(1-q^(2n+1)) as a power series. -/
noncomputable def den (n : ℕ) : PowerSeries ℤ := ∏ i ∈ range (n + 1), (1 - PowerSeries.X ^ (2 * i + 1))

lemma den_const (n : ℕ) : PowerSeries.constantCoeff (den n) = ((1 : ℤˣ) : ℤ) := by
  unfold den; rw [map_prod]; simp

/-- 1/(q;q^2)_{n+1}. -/
noncomputable def denInv (n : ℕ) : PowerSeries ℤ := PowerSeries.invOfUnit (den n) 1

/-- The n-th term q^n (q;q)_n/(q;q^2)_{n+1} of the A202146 g.f. -/
noncomputable def TA (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ n * (∏ i ∈ range n, (1 - PowerSeries.X ^ (i + 1))) * denInv n

/-- The n-th term (-q)^n (-q;q)_n/(q;q^2)_{n+1} of the left side of (*). -/
noncomputable def TL (n : ℕ) : PowerSeries ℤ :=
  (-PowerSeries.X) ^ n * (∏ i ∈ range n, (1 + PowerSeries.X ^ (i + 1))) * denInv n

/-- Sum of a sequence of power series whose n-th term has order >= n (taken coefficientwise). -/
noncomputable def sumS (T : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => ∑ n ∈ range (k + 1), PowerSeries.coeff k (T n)

/-- A202146: a(k) = [q^k] Sum_n q^n (q;q)_n/(q;q^2)_{n+1}
(= 1/(1-q) + Sum_{n>=1} q^n/(1-q) prod_{k<=n} (1-q^k)/(1-q^(2k+1)), the entry's g.f.). -/
noncomputable def A202146 (k : ℕ) : ℤ := PowerSeries.coeff k (sumS TA)

lemma map_TA_TL (n : ℕ) : PowerSeries.map (Int.castRingHom (ZMod 2)) (TA n) =
    PowerSeries.map (Int.castRingHom (ZMod 2)) (TL n) := by
  unfold TA TL
  simp only [map_mul, map_pow, map_prod, map_sub, map_add, map_one, map_neg, PowerSeries.map_X]
  have h1 : ∀ y : PowerSeries (ZMod 2), -y = y := fun y => by
    ext k; rw [map_neg]; exact ZMod.neg_eq_self_mod_two _
  rw [h1]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  rw [sub_eq_add_neg, h1]

/-- The reduction mod 2: A202146 ≡ [q^k] LHS(*) (mod 2). -/
theorem mod2_reduction (k : ℕ) :
    ((A202146 k : ℤ) : ZMod 2) = ((PowerSeries.coeff k (sumS TL) : ℤ) : ZMod 2) := by
  unfold A202146 sumS
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  have := congrArg (PowerSeries.coeff k) (map_TA_TL n)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at this
  exact this

/-- Right side of (*): Sum_m (-1)^m q^(3m(m+1)). -/
noncomputable def theta : PowerSeries ℤ :=
  PowerSeries.mk fun k => ∑ m ∈ range (k + 1), if k = 3 * m * (m + 1) then (-1) ^ m else 0

/-- Parity of A202146, given identity (*) (sumS TL = theta), proved on paper from
`bailey_pair` by Bailey's lemma. -/
theorem A202146_parity_of_star (hstar : sumS TL = theta) (k : ℕ) :
    Odd (A202146 k) ↔ ∃ m, k = 3 * m * (m + 1) := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd, mod2_reduction, hstar, theta, PowerSeries.coeff_mk]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    apply h
    rw [Finset.sum_eq_zero (fun m _ => by rw [ite_eq_right_iff.2 (fun h' => absurd h' (hne m))])]
    simp
  · rintro ⟨m, rfl⟩
    have hm : m ∈ range (3 * m * (m + 1) + 1) := by
      rw [mem_range]; nlinarith
    rw [Finset.sum_eq_single m]
    · simp only [↓reduceIte]; push_cast
      exact pow_ne_zero _ (by decide)
    · intro b _ hb
      have : 3 * m * (m + 1) ≠ 3 * b * (b + 1) := by
        intro h; apply hb
        rcases lt_trichotomy b m with h' | h' | h'
        · have : 3 * b * (b + 1) < 3 * m * (m + 1) := by nlinarith
          omega
        · exact h'
        · have : 3 * m * (m + 1) < 3 * b * (b + 1) := by nlinarith
          omega
      simp [this]
    · intro h; exact absurd hm h

/-! ## The entry's g.f. exactly as written in OEIS A202146 -/

/-- 1/(1 - q^e) (for e ≥ 1) as a power series. -/
noncomputable def invOneSub (e : ℕ) : PowerSeries ℤ := PowerSeries.invOfUnit (1 - PowerSeries.X ^ e) 1

lemma mul_invOneSub (e : ℕ) (he : 1 ≤ e) : (1 - PowerSeries.X ^ e) * invOneSub e = 1 := by
  apply PowerSeries.mul_invOfUnit
  rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]; simp

/-- The n-th summand of the entry's g.f.
1/(1-x) + Sum_{n>=1} x^n/(1-x) * Product_{k=1..n} (1 - x^k)/(1 - x^(2*k+1))
(n = 0 gives 1/(1-x); the product index is written k+1, k < n). -/
noncomputable def entryTerm (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ n * invOneSub 1 *
    ∏ k ∈ range n, ((1 - PowerSeries.X ^ (k + 1)) * invOneSub (2 * (k + 1) + 1))

/-- a(k) read off the entry's g.f.: [x^k] (1/(1-x) + Sum_{n=1..k} entryTerm n)
(summands with n > k are multiples of x^n and do not contribute). -/
noncomputable def A202146_entry (k : ℕ) : ℤ :=
  PowerSeries.coeff k (invOneSub 1) + ∑ n ∈ range k, PowerSeries.coeff k (entryTerm (n + 1))

lemma inv_unique {a b c : PowerSeries ℤ} (h1 : a * b = 1) (h2 : a * c = 1) : b = c := by
  calc b = b * (a * c) := by rw [h2, mul_one]
    _ = (a * b) * c := by ring
    _ = c := by rw [h1, one_mul]

lemma entryTerm_eq (n : ℕ) : entryTerm n = TA n := by
  have hden : den n * (invOneSub 1 * ∏ k ∈ range n, invOneSub (2 * (k + 1) + 1)) = 1 := by
    unfold den
    rw [prod_range_succ']
    simp only [mul_zero, zero_add]
    have h1 := mul_invOneSub 1 le_rfl
    have h2 : (∏ k ∈ range n, (1 - PowerSeries.X ^ (2 * (k + 1) + 1))) *
        ∏ k ∈ range n, invOneSub (2 * (k + 1) + 1) = 1 := by
      rw [← prod_mul_distrib]
      exact prod_eq_one (fun k _ => mul_invOneSub _ (by omega))
    linear_combination (∏ k ∈ range n, (1 - PowerSeries.X ^ (2 * (k + 1) + 1))) *
      (∏ k ∈ range n, invOneSub (2 * (k + 1) + 1)) * h1 + h2
  have hinv : den n * denInv n = 1 := PowerSeries.mul_invOfUnit _ _ (den_const n)
  have e := inv_unique hden hinv
  unfold entryTerm TA
  rw [← e, prod_mul_distrib]
  ring

/-- The entry's g.f. gives the same coefficients as `A202146` (Sum q^n (q;q)_n/(q;q^2)_{n+1}). -/
theorem A202146_entry_eq (k : ℕ) : A202146_entry k = A202146 k := by
  unfold A202146_entry A202146 sumS
  rw [PowerSeries.coeff_mk, sum_range_succ']
  rw [add_comm]
  congr 1
  · apply sum_congr rfl; intro n _; rw [entryTerm_eq]
  · rw [← entryTerm_eq 0]; simp [entryTerm]

/-! ## Identity (*) from the Bailey pair, Bailey's lemma (a = q, rho1 = q, rho2 = -1)

With `E_1 + E_3 = (-q;q)_n (1 + q^n)` (`bailey_pair`) the n-th term of LHS(*) (n ≥ 1) is
`Σ_j W_j D_n / ((q;q)_{n-2j} (q;q)_{n+2j+1})`, `D_n = (-q)^n (-q;q)_{n-1} (q;q)_n`,
`W_j = (-1)^j (q^{3j^2+j} + q^{3j^2+3j})`. Interchanging the sums, the inner sum over n for
`r = 2j` (j ≥ 0) or `r = -2j-1` (j < 0) is `(-q)^r (-q;q)_{r-1} G_r` with
`G_r = qGaussSum r = 1/(-q;q)_{r+1}` (library, `qGaussSum_mul`). The terms j = t and j = -t-1
then add up to `(-1)^t q^{3t(t+1)}`. All infinite sums are handled by truncation mod `X^M`. -/

section Star

open OpenProblemsLib.QSeries

lemma ite_f {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

local notation "qq" => (PowerSeries.X : PowerSeries ℤ)

noncomputable abbrev ι : ℤ[X] →+* PowerSeries ℤ := Polynomial.coeToPowerSeries.ringHom

lemma ι_X : ι X = qq := by simp

lemma ι_qp (n : ℕ) : ι (qp n) = qpS n := by
  unfold qp qpS; simp [map_prod]

lemma ι_pm (n : ℕ) : ι (pm n) = ppS 1 n := by
  unfold pm ppS; simp only [map_prod, map_add, map_one, map_pow, ι_X]
  exact prod_congr rfl (fun i _ => by rw [add_comm i 1])

lemma ppS_one_succ (n : ℕ) : ppS 1 (n + 1) = ppS 1 n * (1 + qq ^ (n + 1)) := by
  unfold ppS; rw [prod_range_succ, add_comm 1 n]

lemma den_mul (n : ℕ) : den n * (qpS n * ppS 1 n) = qpS (2 * n + 1) := by
  induction n with
  | zero => simp [den, qpS, ppS]
  | succ n ih =>
    rw [show den (n + 1) = den n * (1 - qq ^ (2 * (n + 1) + 1)) from prod_range_succ _ _,
      show qpS (n + 1) = qpS n * (1 - qq ^ (n + 1)) from prod_range_succ _ _, ppS_one_succ,
      show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by ring,
      show qpS (2 * n + 1 + 1 + 1) = qpS (2 * n + 1) * (1 - qq ^ (2 * n + 1 + 1)) *
        (1 - qq ^ (2 * n + 1 + 1 + 1)) by
          rw [show qpS (2 * n + 1 + 1 + 1) = qpS (2 * n + 1 + 1) * (1 - qq ^ (2 * n + 1 + 1 + 1))
            from prod_range_succ _ _, show qpS (2 * n + 1 + 1) = qpS (2 * n + 1) *
            (1 - qq ^ (2 * n + 1 + 1)) from prod_range_succ _ _]]
    linear_combination (1 - qq ^ (2 * n + 1 + 1 + 1)) * (1 - qq ^ (n + 1)) * (1 + qq ^ (n + 1)) * ih

lemma inv1_mul (a b : PowerSeries ℤ) (ha : PowerSeries.constantCoeff a = 1)
    (hb : PowerSeries.constantCoeff b = 1) : inv1 (a * b) = inv1 a * inv1 b := by
  apply inv_unique (a := a * b)
  · exact mul_inv1 _ (by rw [map_mul, ha, hb, one_mul])
  · rw [show a * b * (inv1 a * inv1 b) = (a * inv1 a) * (b * inv1 b) by ring, mul_inv1 a ha,
      mul_inv1 b hb, one_mul]

lemma TL_eq (n : ℕ) : TL n = (-qq) ^ n * ppS 1 n * ppS 1 n * qpS n * inv1 (qpS (2 * n + 1)) := by
  have h1 : den n * denInv n = 1 := PowerSeries.mul_invOfUnit _ _ (den_const n)
  have h2 : den n * (qpS n * ppS 1 n * inv1 (qpS (2 * n + 1))) = 1 := by
    rw [← mul_assoc, den_mul, mul_inv1 _ (cc_qpS _)]
  have e := inv_unique h1 h2
  unfold TL
  rw [e, show (∏ i ∈ range n, (1 + qq ^ (i + 1))) = ppS 1 n from
    prod_congr rfl (fun i _ => by rw [add_comm i 1])]
  ring

/-- `1/(q;q)_m`, zero for negative `m`. -/
noncomputable def iq (m : ℤ) : PowerSeries ℤ := if 0 ≤ m then inv1 (qpS m.toNat) else 0

lemma iq_nat (m : ℕ) : iq m = inv1 (qpS m) := by simp [iq]

lemma qz_inv (N : ℕ) (k : ℤ) : ι (qz N k) * inv1 (qpS N) = iq k * iq (N - k) := by
  rcases lt_or_ge k 0 with h | h
  · rw [qz_neg N k h, iq, ite_f (by omega)]; simp
  rcases lt_or_ge (N : ℤ) k with h' | h'
  · rw [qz_big N k h', iq, iq, ite_f (show ¬ (0 ≤ (N : ℤ) - k) by omega)]; simp
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, k = K := ⟨k.toNat, by omega⟩
  have hK : K ≤ N := by omega
  rw [show (N : ℤ) - K = ((N - K : ℕ) : ℤ) by omega, iq_nat, iq_nat, qz, ite_t h,
    Int.toNat_natCast]
  have e := congrArg ι (qb_prod N K hK)
  rw [map_mul, map_mul, ι_qp, ι_qp, ι_qp] at e
  have hu := mul_inv1 (qpS K) (cc_qpS _)
  have hv := mul_inv1 (qpS (N - K)) (cc_qpS _)
  have hw := mul_inv1 (qpS N) (cc_qpS _)
  linear_combination (-(ι (qb N K) * inv1 (qpS N) * qpS (N - K) * inv1 (qpS (N - K)))) * hu -
    ι (qb N K) * inv1 (qpS N) * hv + inv1 (qpS K) * inv1 (qpS (N - K)) * inv1 (qpS N) * e +
    inv1 (qpS K) * inv1 (qpS (N - K)) * hw

/-- `W_j = (-1)^j (q^{3j^2+j} + q^{3j^2+3j})`. -/
noncomputable def W (j : ℤ) : PowerSeries ℤ := ι (w1 j + w3 j)

/-- `D_n = (-q)^n (-q;q)_{n-1} (q;q)_n`. -/
noncomputable def D (n : ℕ) : PowerSeries ℤ := (-qq) ^ n * ppS 1 (n - 1) * qpS n

lemma TL_succ (n B : ℕ) (hB : n + 2 ≤ B) :
    TL (n + 1) = ∑ t ∈ range B,
      (W t * (D (n + 1) * (iq (((n + 1 : ℕ) : ℤ) - 2 * t) * iq (((n + 1 : ℕ) : ℤ) + 2 * t + 1))) +
       W (-(t : ℤ) - 1) * (D (n + 1) * (iq (((n + 1 : ℕ) : ℤ) - 2 * (-(t : ℤ) - 1)) *
         iq (((n + 1 : ℕ) : ℤ) + 2 * (-(t : ℤ) - 1) + 1)))) := by
  set m := n + 1 with hm
  have hbp := bailey_pair m
  have hf1 := fin_supp w1 (2 * m + 1) m
  have hf3 := fin_supp w3 (2 * m + 1) m
  unfold E at hbp
  rw [← finsum_add_distrib hf1 hf3] at hbp
  have hsum : (fun j : ℤ => w1 j * qz (2 * m + 1) (m - 2 * j) + w3 j * qz (2 * m + 1) (m - 2 * j)) =
      fun j => (w1 j + w3 j) * qz (2 * m + 1) (m - 2 * j) := by funext j; ring
  rw [hsum, finsum_int_range _ B (fun j hj => by
    have := qz_ne _ _ (fun h0 => hj (by rw [h0, mul_zero])); omega)] at hbp
  have hι := congrArg ι hbp
  rw [map_sum] at hι
  simp only [map_mul, map_add, map_one, map_pow, ι_X, ι_pm] at hι
  rw [TL_eq, show ppS 1 m = ppS 1 n * (1 + qq ^ m) from ppS_one_succ n]
  have e1 : (-qq) ^ m * (ppS 1 n * (1 + qq ^ m)) * (ppS 1 n * (1 + qq ^ m)) * qpS m *
      inv1 (qpS (2 * m + 1)) = D m * ((ppS 1 n * (1 + qq ^ m)) * (1 + qq ^ m)) *
      inv1 (qpS (2 * m + 1)) := by
    unfold D; rw [hm, Nat.add_sub_cancel]; ring
  rw [e1, ← ppS_one_succ, ← hm, ← hι, mul_sum, sum_mul]
  apply sum_congr rfl
  intro t _
  have q1 := qz_inv (2 * m + 1) ((m : ℤ) - 2 * t)
  have q2 := qz_inv (2 * m + 1) ((m : ℤ) - 2 * (-(t : ℤ) - 1))
  rw [show (((2 * m + 1 : ℕ) : ℤ) - ((m : ℤ) - 2 * t)) = (m : ℤ) + 2 * t + 1 by push_cast; ring]
    at q1
  rw [show (((2 * m + 1 : ℕ) : ℤ) - ((m : ℤ) - 2 * (-(t : ℤ) - 1))) =
    (m : ℤ) + 2 * (-(t : ℤ) - 1) + 1 by push_cast; ring] at q2
  unfold W
  simp only [map_add]
  rw [← q1, ← q2]
  ring

/-- Inner sums `In M r = Σ_{n<M} D_{n+1} / ((q;q)_{n+1-r} (q;q)_{n+r+2})`. -/
noncomputable def In (M r : ℕ) : PowerSeries ℤ :=
  ∑ n ∈ range M, D (n + 1) * (iq ((n : ℤ) + 1 - r) * iq ((n : ℤ) + r + 2))

lemma sum_TL (M : ℕ) : ∑ n ∈ range M, TL (n + 1) =
    ∑ t ∈ range (M + 2), (W t * In M (2 * t) + W (-(t : ℤ) - 1) * In M (2 * t + 1)) := by
  rw [sum_congr rfl (fun n hn => TL_succ n (M + 2) (by rw [mem_range] at hn; omega)), sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_add_distrib, In, In, mul_sum, mul_sum]
  have e1 : ∀ n : ℕ, ((n + 1 : ℕ) : ℤ) - 2 * (t : ℤ) = (n : ℤ) + 1 - ((2 * t : ℕ) : ℤ) := by
    intro n; push_cast; ring
  have e2 : ∀ n : ℕ, ((n + 1 : ℕ) : ℤ) + 2 * (t : ℤ) + 1 = (n : ℤ) + ((2 * t : ℕ) : ℤ) + 2 := by
    intro n; push_cast; ring
  have e3 : ∀ n : ℕ, ((n + 1 : ℕ) : ℤ) - 2 * (-(t : ℤ) - 1) = (n : ℤ) + ((2 * t + 1 : ℕ) : ℤ) + 2 := by
    intro n; push_cast; ring
  have e4 : ∀ n : ℕ, ((n + 1 : ℕ) : ℤ) + 2 * (-(t : ℤ) - 1) + 1 = (n : ℤ) + 1 - ((2 * t + 1 : ℕ) : ℤ) := by
    intro n; push_cast; ring
  simp only [e1, e2, e3, e4]
  rw [add_left_cancel_iff.mpr]
  apply sum_congr rfl; intro n _
  rw [mul_comm (iq ((n : ℤ) + ((2 * t + 1 : ℕ) : ℤ) + 2))]

lemma lower (M : ℕ) {a b : PowerSeries ℤ} (h : modX (M + 1) a = modX (M + 1) b) :
    modX M a = modX M b :=
  modX_eq_of_coeff M (fun k hk => coeff_eq_of_modX (M + 1) h k (by omega))

lemma lower' (M L : ℕ) (hL : M ≤ L) {a b : PowerSeries ℤ} (h : modX L a = modX L b) :
    modX M a = modX M b :=
  modX_eq_of_coeff M (fun k hk => coeff_eq_of_modX L h k (by omega))

lemma modX_shift (M r : ℕ) (P A B : PowerSeries ℤ) (h : modX (M - r) A = modX (M - r) B) :
    modX M ((-qq) ^ r * P * A) = modX M ((-qq) ^ r * P * B) := by
  rw [← sub_eq_zero, ← map_sub, show (-qq) ^ r * P * A - (-qq) ^ r * P * B =
    (-qq) ^ r * (P * (A - B)) by ring]
  apply modX_neg_X_pow_mul
  rw [map_mul, map_sub, h, sub_self, mul_zero]

lemma cc_one_add (r : ℕ) (hr : 1 ≤ r) : PowerSeries.constantCoeff (1 + qq ^ r) = 1 := by
  simp [zero_pow (show r ≠ 0 by omega)]

/-- `Γ_r = (-q)^r / ((1 + q^r)(1 + q^{r+1}))`. -/
noncomputable def Γ (r : ℕ) : PowerSeries ℤ :=
  (-qq) ^ r * inv1 ((1 + qq ^ r) * (1 + qq ^ (r + 1)))

lemma ppS_split (r k : ℕ) (hr : 1 ≤ r) : ppS 1 (r - 1 + k) = ppS 1 (r - 1) * ppS r k := by
  unfold ppS; rw [prod_range_add]; congr 1
  apply prod_congr rfl; intro i _; congr 2; omega

lemma key_term (r k : ℕ) (hr : 1 ≤ r) :
    D (r + k) * (inv1 (qpS k) * inv1 (qpS (2 * r + k + 1))) = (-qq) ^ r * ppS 1 (r - 1) * sS r k := by
  unfold D sS
  rw [show r + k - 1 = r - 1 + k by omega, ppS_split r k hr, inv1_mul _ _ (cc_qpS _) (cc_qpS _),
    show k + r = r + k by ring]
  ring

lemma G_inv (r : ℕ) (hr : 1 ≤ r) :
    ppS 1 (r - 1) * qGaussSum r = inv1 ((1 + qq ^ r) * (1 + qq ^ (r + 1))) := by
  have h := qGaussSum_mul r
  have hp : ppS 1 (r + 1) = (1 + qq ^ r) * (1 + qq ^ (r + 1)) * ppS 1 (r - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel, ppS_one_succ, ppS_one_succ]; ring
  apply inv_unique (a := (1 + qq ^ r) * (1 + qq ^ (r + 1)))
  · rw [← mul_assoc, ← hp]; exact h
  · exact mul_inv1 _ (by rw [map_mul, cc_one_add r hr, cc_one_add (r + 1) (by omega), one_mul])

lemma In_pos (M r : ℕ) (hr : 1 ≤ r) : modX M (In M r) = modX M (Γ r) := by
  rcases lt_or_ge M r with hM | hM
  · have h0 : In M r = 0 := by
      apply sum_eq_zero; intro n hn; rw [mem_range] at hn
      rw [iq, ite_f (by omega)]; ring
    have := modX_neg_X_pow_mul M r (inv1 ((1 + qq ^ r) * (1 + qq ^ (r + 1))))
      (by rw [show M - r = 0 by omega]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp))
    rw [h0, Γ, map_zero, this]
  have hIn : In M r = (-qq) ^ r * ppS 1 (r - 1) * ∑ k ∈ range (M - (r - 1)), sS r k := by
    unfold In
    rw [← sum_range_add_sum_Ico _ (show r - 1 ≤ M by omega), sum_eq_zero (fun n hn => by
      rw [mem_range] at hn; rw [iq, ite_f (by omega)]; ring), zero_add, sum_Ico_eq_sum_range,
      mul_sum]
    apply sum_congr rfl
    intro k _
    rw [← key_term r k hr, show r - 1 + k + 1 = r + k by omega,
      show ((r - 1 + k : ℕ) : ℤ) + 1 - r = ((k : ℕ) : ℤ) by omega,
      show ((r - 1 + k : ℕ) : ℤ) + r + 2 = ((2 * r + k + 1 : ℕ) : ℤ) by push_cast; omega,
      iq_nat, iq_nat]
  rw [hIn, Γ, ← G_inv r hr, ← mul_assoc]
  apply modX_shift
  have h := modX_qGaussSum r (M - r + 1)
  rw [show M - (r - 1) = M - r + 1 by omega]
  exact (lower _ h).symm

lemma G_zero : qGaussSum 0 = inv1 (1 + qq) := by
  apply inv_unique (a := 1 + qq)
  · have h := qGaussSum_mul 0
    rwa [show ppS 1 (0 + 1) = 1 + qq by simp [ppS]] at h
  · exact mul_inv1 _ (by simp)

lemma In_zero (M : ℕ) : modX M (2 * In M 0) = modX M (inv1 (1 + qq) - inv1 (1 - qq)) := by
  have hs : ∑ k ∈ range (M + 1), sS 0 k = inv1 (1 - qq) + 2 * In M 0 := by
    rw [sum_range_succ', add_comm, In, mul_sum]
    congr 1
    · unfold sS; simp [qpS, ppS]
    · apply sum_congr rfl
      intro n _
      unfold sS D
      have hp : ppS 0 (n + 1) = 2 * ppS 1 n := by
        unfold ppS; rw [prod_range_succ', pow_zero, mul_comm]
        rw [show (1 : PowerSeries ℤ) + 1 = 2 by norm_num]
        congr 1; apply prod_congr rfl; intro i _; rw [show 0 + (i + 1) = 1 + i by ring]
      rw [hp, show ((n : ℤ) + 1 - ((0 : ℕ) : ℤ)) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        show ((n : ℤ) + ((0 : ℕ) : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) by push_cast; ring, iq_nat, iq_nat,
        Nat.add_sub_cancel, show 2 * 0 + (n + 1) + 1 = n + 2 by ring, show n + 1 + 0 = n + 1 by ring,
        inv1_mul _ _ (cc_qpS _) (cc_qpS _)]
      ring
  have h := lower _ (modX_qGaussSum 0 (M + 1))
  rw [hs, G_zero] at h
  rw [show inv1 (1 + qq) - inv1 (1 - qq) = (inv1 (1 - qq) + 2 * In M 0) - inv1 (1 - qq) +
    (inv1 (1 + qq) - (inv1 (1 - qq) + 2 * In M 0)) by ring, map_add, map_sub (modX M) (inv1 (1 + qq)),
    ← h, sub_self, add_zero]
  ring_nf

lemma sg_nat (n : ℕ) : sg (n : ℤ) = (-1) ^ n := by
  induction n with
  | zero => simp [sg]
  | succ n ih => rw [Nat.cast_succ, sg_succ, ih, pow_succ]; ring

lemma W_nat (s : ℕ) : W s = (-1) ^ s * (qq ^ (3 * s * s + s) + qq ^ (3 * s * s + s) * qq ^ (2 * s)) := by
  unfold W w1 w3
  rw [show (3 * ((s : ℤ) * s) + s).toNat = 3 * s * s + s by
      rw [show (3 * ((s : ℤ) * s) + s) = ((3 * s * s + s : ℕ) : ℤ) by push_cast; ring]; rfl,
    show (3 * ((s : ℤ) * s) + 3 * s).toNat = (3 * s * s + s) + 2 * s by
      rw [show (3 * ((s : ℤ) * s) + 3 * s) = (((3 * s * s + s) + 2 * s : ℕ) : ℤ) by push_cast; ring]
      rfl, sg_nat]
  simp only [map_add, map_mul, map_pow, map_neg, map_one, ι_X, pow_add]
  ring

lemma W_neg (s : ℕ) : W (-(s : ℤ) - 1) = (-1) ^ (s + 1) *
    (qq ^ (3 * s * s + s) * qq ^ (4 * s + 2) + qq ^ (3 * s * s + s) * qq ^ (2 * s)) := by
  unfold W w1 w3
  rw [show (3 * ((-(s : ℤ) - 1) * (-(s : ℤ) - 1)) + (-(s : ℤ) - 1)).toNat =
      (3 * s * s + s) + (4 * s + 2) by
      rw [show (3 * ((-(s : ℤ) - 1) * (-(s : ℤ) - 1)) + (-(s : ℤ) - 1)) =
        (((3 * s * s + s) + (4 * s + 2) : ℕ) : ℤ) by push_cast; ring]; rfl,
    show (3 * ((-(s : ℤ) - 1) * (-(s : ℤ) - 1)) + 3 * (-(s : ℤ) - 1)).toNat =
      (3 * s * s + s) + 2 * s by
      rw [show (3 * ((-(s : ℤ) - 1) * (-(s : ℤ) - 1)) + 3 * (-(s : ℤ) - 1)) =
        (((3 * s * s + s) + 2 * s : ℕ) : ℤ) by push_cast; ring]; rfl,
    show -(s : ℤ) - 1 = -((s + 1 : ℕ) : ℤ) by push_cast; ring, sg_neg, sg_nat]
  simp only [map_add, map_mul, map_pow, map_neg, map_one, ι_X, pow_add]
  ring

lemma pair_zero : inv1 (1 - qq) + (inv1 (1 + qq) - inv1 (1 - qq)) + W (-((0 : ℕ) : ℤ) - 1) * Γ 1 = 1 := by
  rw [W_neg, Γ, inv1_mul _ _ (by simp) (by simp)]
  have ha := mul_inv1 (1 + qq) (by simp)
  have hb := mul_inv1 (1 + qq ^ (1 + 1)) (by simp)
  simp only [pow_one] at *
  linear_combination ha + qq * inv1 (1 + qq) * hb

lemma pair_succ (s : ℕ) (hs : 1 ≤ s) :
    W s * Γ (2 * s) + W (-(s : ℤ) - 1) * Γ (2 * s + 1) = (-1) ^ s * qq ^ (3 * s * (s + 1)) := by
  rw [W_nat, W_neg, Γ, Γ, inv1_mul _ _ (cc_one_add _ (by omega)) (cc_one_add _ (by omega)),
    inv1_mul _ _ (cc_one_add _ (by omega)) (cc_one_add _ (by omega)),
    show 3 * s * (s + 1) = (3 * s * s + s) + 2 * s by ring, (even_two_mul s).neg_pow,
    (odd_two_mul_add_one s).neg_pow]
  have hA := mul_inv1 (1 + qq ^ (2 * s)) (cc_one_add _ (by omega))
  have hB := mul_inv1 (1 + qq ^ (2 * s + 1)) (cc_one_add _ (by omega))
  have hC := mul_inv1 (1 + qq ^ (2 * s + 1 + 1)) (cc_one_add _ (by omega))
  set E := qq ^ (3 * s * s + s)
  linear_combination (-1) ^ s * E * qq ^ (2 * s) * (inv1 (1 + qq ^ (2 * s + 1)) * hA +
    qq ^ (2 * s + 1) * inv1 (1 + qq ^ (2 * s + 1)) * hC + hB)

lemma coeff_sgn_pow (t e k : ℕ) :
    PowerSeries.coeff k ((-1 : PowerSeries ℤ) ^ t * qq ^ e) = if k = e then (-1) ^ t else 0 := by
  rcases Nat.even_or_odd t with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_mul, PowerSeries.coeff_X_pow]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_mul, map_neg, PowerSeries.coeff_X_pow]
    split_ifs <;> simp

lemma TL_zero : TL 0 = inv1 (1 - qq) := by
  simp [TL, denInv, den]

/-- **Identity (*)**: Σ_{n≥0} (-q)^n (-q;q)_n/(q;q^2)_{n+1} = Σ_{m≥0} (-1)^m q^{3m(m+1)}. -/
theorem star : sumS TL = theta := by
  apply eq_of_modX
  intro M
  have hos : sumS TL = osum TL := by ext k; simp [sumS, osum, map_sum]
  have hTL : ∀ L k, L ≤ k → modX L (TL k) = 0 := by
    intro L k hk
    unfold TL
    rw [mul_assoc]
    exact modX_neg_X_pow_mul L k _
      (by rw [show L - k = 0 by omega]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp))
  have h1 : modX M (sumS TL) = modX M (TL 0 + ∑ t ∈ range (M + 2),
      (W t * In M (2 * t) + W (-(t : ℤ) - 1) * In M (2 * t + 1))) := by
    rw [hos, ← sum_TL, add_comm, ← sum_range_succ' (fun n => TL n) M]
    exact lower _ (modX_osum TL hTL (M + 1))
  set T := ∑ t ∈ range (M + 2), (-1 : PowerSeries ℤ) ^ t * qq ^ (3 * t * (t + 1)) with hT
  have h2 : modX M (TL 0 + ∑ t ∈ range (M + 2),
      (W t * In M (2 * t) + W (-(t : ℤ) - 1) * In M (2 * t + 1))) = modX M T := by
    rw [hT, sum_range_succ' _ (M + 1), sum_range_succ' _ (M + 1)]
    have hp0 : modX M (W ((0 : ℕ) : ℤ) * In M (2 * 0) + W (-((0 : ℕ) : ℤ) - 1) * In M (2 * 0 + 1)) =
        modX M (inv1 (1 + qq) - inv1 (1 - qq) + W (-((0 : ℕ) : ℤ) - 1) * Γ 1) := by
      have hW0 : W ((0 : ℕ) : ℤ) = 2 := by rw [W_nat]; norm_num
      rw [hW0, show 2 * 0 = 0 from rfl, show 2 * 0 + 1 = 1 from rfl, map_add,
        map_mul (modX M) (W _) (In M 1), In_pos M 1 le_rfl, ← map_mul, In_zero, ← map_add]
    have hps : ∀ t ∈ range (M + 1), modX M (W ((t + 1 : ℕ) : ℤ) * In M (2 * (t + 1)) +
        W (-((t + 1 : ℕ) : ℤ) - 1) * In M (2 * (t + 1) + 1)) =
        modX M ((-1 : PowerSeries ℤ) ^ (t + 1) * qq ^ (3 * (t + 1) * (t + 1 + 1))) := by
      intro t _
      rw [map_add, map_mul, map_mul, In_pos M _ (by omega), In_pos M _ (by omega), ← map_mul,
        ← map_mul, ← map_add, pair_succ (t + 1) (by omega)]
    rw [← add_assoc, map_add, map_add, map_sum, sum_congr rfl hps, hp0]
    conv_rhs => rw [map_add, map_sum]
    have h0 : modX M (TL 0) + modX M (inv1 (1 + qq) - inv1 (1 - qq) + W (-((0 : ℕ) : ℤ) - 1) * Γ 1) =
        modX M ((-1 : PowerSeries ℤ) ^ 0 * qq ^ (3 * 0 * (0 + 1))) := by
      rw [← map_add, TL_zero, ← add_assoc, pair_zero]; simp
    linear_combination h0
  rw [h1, h2]
  apply modX_eq_of_coeff
  intro k hk
  rw [hT, map_sum, theta, PowerSeries.coeff_mk]
  simp only [coeff_sgn_pow]
  rw [← sum_range_add_sum_Ico _ (show k + 1 ≤ M + 2 by omega), sum_eq_zero (s := Ico _ _)
    (fun t ht => by
      have := (mem_Ico.mp ht).1
      rw [ite_f (by nlinarith)]), add_zero]

/-- **A202150 / A202146 parity**, unconditionally: A202146(k), read from the entry's g.f., is odd
iff k = 3m(m+1) for some m; so A202150(n) = A202146(3n(n+1)) lists exactly the odd terms. -/
theorem A202146_entry_parity (k : ℕ) : Odd (A202146_entry k) ↔ ∃ m, k = 3 * m * (m + 1) := by
  rw [A202146_entry_eq]
  exact A202146_parity_of_star star k

end Star
