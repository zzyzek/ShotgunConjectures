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
Not checked here: identity (*) itself, i.e. Bailey's lemma (q-Gauss summation) applied to
`bailey_pair` with rho1 = q, rho2 = -1 (README step 3); the regrouping of E_1 + E_3 into the
alpha_n of README step 2 is immediate but not stated in Lean; the rewriting of the entry's
g.f. 1/(1-x) + Sum_{n>=1} ... as Sum q^n (q;q)_n/(q;q^2)_{n+1}.
-/
import Mathlib

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
