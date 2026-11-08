/-
OEIS A109381: a(n) = maximum digit of n^2 in the factorial base.
Conjecture: a(n) → ∞.  Not settled here.

Checked here (partial result): for every bound B the exceptions are sparse.
* `fact_base_count` : at most (B+1)^m numbers N < m! have every factorial-base digit ≤ B
                      (the digits of N < m! determine N).
* `A109381_sparse`  : for all B and k ≥ 1 there is K with
                      #{n < X : a(n) ≤ B}^k ≤ K·X² for every X, i.e. the count is O(X^(2/k)).
* `A109381_density_zero` : for all B and ε > 0, #{n < X : a(n) ≤ B} ≤ ε X for all large X.
* `conjecture_implies_brocard_finite` : if a(n) → ∞ (every {n | a n ≤ B} finite), then
                      Brocard's equation n² = k! + 1 has finitely many solutions
                      (`a_brocard`: such n have a(n) ≤ 1).
Definitions: digit i of N is N / i! mod (i+1) (i ≥ 1; the i = 0 digit is always 0);
a n is the maximum over i ≤ n² (larger i give digit 0, `fdig_eq_zero`).
Not checked in Lean: the data terms (e.g. a(1183893) = 1).
-/
import Mathlib

namespace A109381

def fdig (N i : ℕ) : ℕ := N / i.factorial % (i + 1)

def a (n : ℕ) : ℕ := (Finset.range (n ^ 2 + 1)).sup (fun i => fdig (n ^ 2) i)

lemma fdig_eq_zero (N i : ℕ) (h : N < i) : fdig N i = 0 := by
  unfold fdig
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le h (Nat.self_le_factorial i))]
  simp

lemma a_le_iff (n B : ℕ) : a n ≤ B ↔ ∀ i, fdig (n ^ 2) i ≤ B := by
  unfold a
  rw [Finset.sup_le_iff]
  constructor
  · intro h i
    by_cases hi : i < n ^ 2 + 1
    · exact h i (Finset.mem_range.mpr hi)
    · rw [fdig_eq_zero _ _ (by omega)]; omega
  · intro h i _; exact h i

/-- Digits below k determine N mod k!. -/
lemma mod_fact_eq (N M : ℕ) : ∀ k, (∀ i < k, fdig N i = fdig M i) →
    N % k.factorial = M % k.factorial
  | 0, _ => by simp [Nat.factorial_zero, Nat.mod_one]
  | k + 1, h => by
    have ih := mod_fact_eq N M k (fun i hi => h i (by omega))
    rw [Nat.factorial_succ, mul_comm, Nat.mod_mul, Nat.mod_mul, ih]
    have := h k (by omega)
    unfold fdig at this
    rw [this]

theorem fact_base_count (B m : ℕ) :
    ((Finset.range m.factorial).filter (fun N => ∀ i < m, fdig N i ≤ B)).card ≤ (B + 1) ^ m := by
  classical
  let f : ℕ → (Fin m → Fin (B + 1)) := fun N i =>
    ⟨min (fdig N i) B, by omega⟩
  have hinj : Set.InjOn f ((Finset.range m.factorial).filter (fun N => ∀ i < m, fdig N i ≤ B) : Set ℕ) := by
    intro N hN M hM hNM
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hN hM
    have hd : ∀ i < m, fdig N i = fdig M i := by
      intro i hi
      have := congrArg (fun g => (g ⟨i, hi⟩ : ℕ)) hNM
      simp only [f] at this
      rw [min_eq_left (hN.2 i hi), min_eq_left (hM.2 i hi)] at this
      exact this
    have := mod_fact_eq N M m hd
    rwa [Nat.mod_eq_of_lt hN.1, Nat.mod_eq_of_lt hM.1] at this
  have := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using this

lemma pow_le_fact (c : ℕ) : ∀ j, c ^ j ≤ c ^ c * j.factorial
  | 0 => by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc; simp
    · simpa using Nat.one_le_pow c c hc
  | j + 1 => by
    have ih := pow_le_fact c j
    by_cases hc : c ≤ j + 1
    · calc c ^ (j + 1) = c * c ^ j := by ring
        _ ≤ (j + 1) * (c ^ c * j.factorial) := Nat.mul_le_mul hc ih
        _ = c ^ c * (j + 1).factorial := by rw [Nat.factorial_succ]; ring
    · have h1 : c ^ (j + 1) ≤ c ^ c := Nat.pow_le_pow_right (by omega) (by omega)
      exact h1.trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _))

def count (B X : ℕ) : ℕ := ((Finset.range X).filter (fun n => a n ≤ B)).card

lemma count_le (B X m : ℕ) (hm : X ^ 2 ≤ m.factorial) : count B X ≤ (B + 1) ^ m := by
  classical
  refine le_trans ?_ (fact_base_count B m)
  unfold count
  apply Finset.card_le_card_of_injOn (fun n => n ^ 2)
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn ⊢
    refine ⟨lt_of_lt_of_le (Nat.pow_lt_pow_left hn.1 (by norm_num)) hm, fun i _ => (a_le_iff n B).mp hn.2 i⟩
  · intro x _ y _ hxy
    exact Nat.pow_left_injective (by norm_num) hxy

theorem A109381_sparse (B k : ℕ) (hk : 0 < k) :
    ∃ K, ∀ X, count B X ^ k ≤ K * X ^ 2 := by
  set c := (B + 1) ^ k
  refine ⟨c * c ^ c + 1, fun X => ?_⟩
  -- least m with X^2 ≤ m!
  have hex : ∃ m : ℕ, X ^ 2 ≤ m.factorial := ⟨X ^ 2, Nat.self_le_factorial _⟩
  classical
  set m := Nat.find hex
  have hm : X ^ 2 ≤ m.factorial := Nat.find_spec hex
  have hcnt := count_le B X m hm
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0] at hcnt; simp only [pow_zero] at hcnt
    rcases Nat.eq_zero_or_pos X with hX | hX
    · subst hX
      have : count B 0 = 0 := by simp [count]
      rw [this, zero_pow (by omega)]; exact Nat.zero_le _
    · have h1 : count B X ^ k ≤ 1 := by simpa using Nat.pow_le_pow_left hcnt k
      have h2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX
      calc count B X ^ k ≤ 1 := h1
        _ = 1 * 1 := by ring
        _ ≤ (c * c ^ c + 1) * X ^ 2 := Nat.mul_le_mul (by omega) h2
  · have hlt : (m - 1).factorial < X ^ 2 := by
      have := Nat.find_min hex (show m - 1 < m by omega)
      omega
    calc count B X ^ k ≤ ((B + 1) ^ m) ^ k := Nat.pow_le_pow_left hcnt k
      _ = c * c ^ (m - 1) := by
          rw [← pow_mul, show m * k = k + k * (m - 1) by
            rcases m with _ | m
            · omega
            · simp; ring, pow_add, pow_mul]
      _ ≤ c * (c ^ c * (m - 1).factorial) := Nat.mul_le_mul_left _ (pow_le_fact c _)
      _ ≤ c * (c ^ c * X ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlt.le)
      _ ≤ (c * c ^ c + 1) * X ^ 2 := by nlinarith

theorem A109381_density_zero (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X0 : ℕ, ∀ X, X0 ≤ X → (count B X : ℝ) ≤ ε * X := by
  obtain ⟨K, hK⟩ := A109381_sparse B 3 (by norm_num)
  obtain ⟨X0, hX0⟩ := exists_nat_gt ((K : ℝ) / ε ^ 3)
  refine ⟨X0, fun X hX => ?_⟩
  have hXr : (K : ℝ) / ε ^ 3 < X := lt_of_lt_of_le hX0 (by exact_mod_cast hX)
  have hXpos : (0 : ℝ) < X := lt_of_le_of_lt (by positivity) hXr
  have h1 : ((count B X : ℝ)) ^ 3 ≤ K * (X : ℝ) ^ 2 := by exact_mod_cast hK X
  have h2 : (K : ℝ) ≤ ε ^ 3 * X := by
    rw [div_lt_iff₀ (by positivity)] at hXr; linarith
  have h3 : ((count B X : ℝ)) ^ 3 ≤ (ε * X) ^ 3 := by
    calc ((count B X : ℝ)) ^ 3 ≤ K * (X : ℝ) ^ 2 := h1
      _ ≤ (ε ^ 3 * X) * X ^ 2 := by nlinarith [sq_nonneg (X : ℝ)]
      _ = (ε * X) ^ 3 := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h3

/-- Brocard's equation n² = k! + 1 (k ≥ 2) gives a(n) ≤ 1: the digits are 1 at
positions 1 and k and 0 elsewhere. -/
lemma fdig_brocard (k i : ℕ) (hk : 2 ≤ k) : fdig (k.factorial + 1) i ≤ 1 := by
  unfold fdig
  rcases Nat.lt_or_ge k i with hki | hki
  · have : (k + 1).factorial ≤ i.factorial := Nat.factorial_le hki
    have h2 : k.factorial + 1 < (k + 1).factorial := by
      rw [Nat.factorial_succ]
      have := Nat.factorial_pos k
      nlinarith
    rw [Nat.div_eq_of_lt (by omega)]; simp
  · rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i <;> simp <;> omega
    · have h1 : 1 < i.factorial := by
        calc 1 < 2 := by norm_num
          _ = (2 : ℕ).factorial := rfl
          _ ≤ i.factorial := Nat.factorial_le hi
      have hd : i.factorial ∣ k.factorial := Nat.factorial_dvd_factorial hki
      have hdiv : (k.factorial + 1) / i.factorial = k.factorial / i.factorial := by
        rw [Nat.add_div_of_dvd_right hd, Nat.div_eq_of_lt h1, add_zero]
      rw [hdiv]
      rcases hki.lt_or_eq with hlt | heq
      · have hd2 : (i + 1) ∣ k.factorial / i.factorial := by
          have : (i + 1).factorial ∣ k.factorial := Nat.factorial_dvd_factorial hlt
          rw [Nat.factorial_succ] at this
          obtain ⟨q, hq⟩ := this
          refine ⟨q, ?_⟩
          rw [hq, show (i + 1) * i.factorial * q = i.factorial * ((i + 1) * q) by ring,
            Nat.mul_div_cancel_left _ (Nat.factorial_pos i)]
        rw [Nat.mod_eq_zero_of_dvd hd2]; omega
      · rw [heq, Nat.div_self (Nat.factorial_pos k)]
        exact (Nat.mod_le _ _).trans le_rfl

theorem a_brocard (n k : ℕ) (hk : 2 ≤ k) (h : n ^ 2 = k.factorial + 1) : a n ≤ 1 := by
  rw [a_le_iff]; intro i; rw [h]; exact fdig_brocard k i hk

/-- The conjecture implies that Brocard's equation n² = k! + 1 has finitely many solutions. -/
theorem conjecture_implies_brocard_finite
    (hconj : ∀ B, Set.Finite (Set.ofPred fun n => a n ≤ B)) :
    Set.Finite (Set.ofPred fun n => ∃ k : ℕ, n ^ 2 = k.factorial + 1) := by
  apply ((hconj 1).union (Set.finite_le_nat 2)).subset
  intro n hn
  obtain ⟨k, hk⟩ := hn
  rcases Nat.lt_or_ge k 2 with h | h
  · right
    interval_cases k <;> simp at hk <;>
      (have : n ≤ 2 := by nlinarith) <;> exact this
  · left; exact a_brocard n k h hk

end A109381

open A109381
