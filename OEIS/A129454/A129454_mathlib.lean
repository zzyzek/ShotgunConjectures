/-
OEIS A129454, Mathlib proof.

A129454(n) = ∏_{i,j,k = 1..n-1} gcd(i, j, k) (offset 0). Conjecture:
ord_p(a(n)) = Σ_{t ≥ 1} floor(n/p^t)^3. As printed this is off by one
(README); the statement proved here is the shifted one.

Main theorem `A129454_main`: for every prime p and every n ≥ 1,
  padicValNat p (a(n)) = Σ_{t = 1}^{n} floor((n-1)/p^t)^3
(terms with p^t > n - 1 vanish, so this is the full sum over t ≥ 1), and
the literal formula fails: padicValNat 3 (a(3)) = 0 while
Σ_{t=1}^{3} floor(3/3^t)^3 = 1. This is the README result.

Proof: v_p(g) = #{t ∈ [1, N] : p^t ∣ g} for 1 ≤ g ≤ N
(`Nat.factorization_eq_card_pow_dvd_of_lt`), swap the sums, and count
multiples of p^t up to N (`Nat.Ioc_filter_dvd_card_eq_div`).
Nothing is outside Lean.
-/
import Mathlib

/-- A129454(n) = ∏_{i,j,k ∈ [1, n-1]} gcd(i, j, k). -/
def A129454 (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 (n - 1), ∏ j ∈ Finset.Icc 1 (n - 1), ∏ k ∈ Finset.Icc 1 (n - 1),
    Nat.gcd (Nat.gcd i j) k

theorem A129454_val (p N : ℕ) (hp : p.Prime) :
    (A129454 (N + 1)).factorization p = ∑ t ∈ Finset.Icc 1 N, (N / p ^ t) ^ 3 := by
  have hpos : ∀ i ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      0 < Nat.gcd (Nat.gcd i j) k := by
    intro i hi j _ k _
    simp only [Finset.mem_Icc] at hi
    exact Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ (by omega))
  have hval : ∀ i ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      (Nat.gcd (Nat.gcd i j) k).factorization p =
        ∑ t ∈ Finset.Icc 1 N, (if p ^ t ∣ i then 1 else 0) * (if p ^ t ∣ j then 1 else 0) *
          (if p ^ t ∣ k then 1 else 0) := by
    intro i hi j hj k hk
    have hg := hpos i hi j hj k hk
    have hle : Nat.gcd (Nat.gcd i j) k ≤ N :=
      (Nat.le_of_dvd (by simp only [Finset.mem_Icc] at hk; omega) (Nat.gcd_dvd_right _ _)).trans
        (Finset.mem_Icc.1 hk).2
    have hlt : Nat.gcd (Nat.gcd i j) k < p ^ (N + 1) :=
      lt_of_le_of_lt hle (lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hp.two_le _)
        |>.trans_le' (by omega))
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hg hlt, Finset.card_filter]
    rw [show Finset.Ico 1 (N + 1) = Finset.Icc 1 N by ext; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Nat.dvd_gcd_iff]
    by_cases h1 : p ^ t ∣ i <;> by_cases h2 : p ^ t ∣ j <;> by_cases h3 : p ^ t ∣ k <;> simp [*]
  have hcount : ∀ t, ∑ i ∈ Finset.Icc 1 N, (if p ^ t ∣ i then 1 else 0) = N / p ^ t := by
    intro t
    rw [← Finset.card_filter, show Finset.Icc 1 N = Finset.Ioc 0 N by ext; simp; omega]
    exact Nat.Ioc_filter_dvd_card_eq_div N (p ^ t)
  have hsum : (A129454 (N + 1)).factorization p =
      ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (Nat.gcd (Nat.gcd i j) k).factorization p := by
    simp only [A129454, Nat.add_sub_cancel]
    rw [Nat.factorization_prod (fun i hi => (Finset.prod_pos fun j hj =>
        Finset.prod_pos fun k hk => hpos i hi j hj k hk).ne')]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.factorization_prod (fun j hj => (Finset.prod_pos fun k hk => hpos i hi j hj k hk).ne')]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Nat.factorization_prod (fun k hk => (hpos i hi j hj k hk).ne')]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [hsum, Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun k hk => hval i hi j hj k hk]
  /- swap: Σ_i Σ_j Σ_k Σ_t = Σ_t (Σ_i)^3 -/
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hcount t]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem A129454_main :
    (∀ p n : ℕ, p.Prime → 1 ≤ n →
      padicValNat p (A129454 n) = ∑ t ∈ Finset.Icc 1 n, ((n - 1) / p ^ t) ^ 3) ∧
    padicValNat 3 (A129454 3) = 0 ∧ ∑ t ∈ Finset.Icc 1 3, (3 / 3 ^ t) ^ 3 = 1 := by
  refine ⟨fun p n hp hn => ?_, ?_, by decide⟩
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    have := Fact.mk hp
    rw [← Nat.factorization_def _ hp, A129454_val p N hp, Nat.add_sub_cancel]
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : N / p ^ (N + 1) = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_left hp.two_le _) |>.trans_le' (by omega))
    rw [this]; simp
  · have : A129454 3 = 2 := by decide
    rw [this]
    simp
