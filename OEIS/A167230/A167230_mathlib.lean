/-
OEIS A167230 (matrix exponential of Sierpiński's triangle, divided by e),
conjecture: all nonzero entries are Bell numbers.

Formalisation.  S(n,k) = C(n,k) mod 2 (A047999), an infinite lower-triangular
matrix; its powers are `Spow m n k` (S^0 = I, S^(m+1)(n,k) = Σ_{j ≤ n} S(n,j)
S^m(j,k)), and exp(S)(n,k) = Σ_m S^m(n,k)/m! (`expS`, a real tsum).  Bell
numbers by the recurrence B(0) = 1, B(n+1) = Σ_i C(n,i) B(i).  Bits: `bsub n k`
says every binary digit of k is ≤ the digit of n (k ⊆ n bitwise,
`bsub_iff_testBit`), `bd n k` counts the binary digits set in n but not in k (the README's
j = popcount(n) − popcount(k) when k ⊆ n).

Main theorem `A167230_conjecture`: for all n, k,
expS n k / e = if bsub n k then B(bd n k) else 0; `A167230_nonzero` restates
it as: every nonzero entry of exp(S)/e is a Bell number.  This is the README
result.

Proof.  Lucas's theorem in Mathlib (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`,
p = 2) gives S(n,k) = [bsub n k]; splitting j = 2b + s in the matrix product
gives S^m(n,k) = [bsub n k]·m^(bd n k) by induction on n; Dobinski's formula
Σ_m m^j/m! = e·B(j) is proved by induction on j from the exponential series.

Not checked: nothing outside Lean.
-/
import Mathlib

open Finset

/-- k ⊆ n bitwise (each binary digit of k at most that of n). -/
def bsub (n k : ℕ) : Bool :=
  if h : n = 0 then k == 0 else (decide (k % 2 ≤ n % 2) && bsub (n / 2) (k / 2))
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

/-- Number of binary digits of n not in k. -/
def bd (n k : ℕ) : ℕ :=
  if h : n = 0 then 0 else (n % 2 - k % 2) + bd (n / 2) (k / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

lemma bsub_zero (k : ℕ) : bsub 0 k = (k == 0) := by rw [bsub]; simp

lemma bd_zero (k : ℕ) : bd 0 k = 0 := by rw [bd]; simp

lemma bsub_unfold (n k : ℕ) : bsub n k = (decide (k % 2 ≤ n % 2) && bsub (n / 2) (k / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bsub_zero, Nat.zero_mod, Nat.zero_div, bsub_zero, Bool.eq_iff_iff]
    simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [bsub]; simp [show n ≠ 0 by omega]

lemma bd_unfold (n k : ℕ) : bd n k = (n % 2 - k % 2) + bd (n / 2) (k / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bd_zero]
  · rw [bd]; simp [show n ≠ 0 by omega]

lemma bsub_le {n k : ℕ} (h : bsub n k = true) : k ≤ n := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [bsub] at h; simp at h; omega
    · rw [bsub_unfold] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have := ih (n / 2) (Nat.div_lt_self hn (by norm_num)) h.2
      omega

lemma bsub_iff_testBit (n k : ℕ) : bsub n k = true ↔ ∀ i, k.testBit i → n.testBit i := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [bsub]
      simp only [dite_true, beq_iff_eq, Nat.zero_testBit]
      constructor
      · rintro rfl i; simp
      · intro h; by_contra hk
        obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hk
        exact absurd (h i hi) (by simp)
    · rw [bsub_unfold]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [ih (n / 2) (Nat.div_lt_self hn (by norm_num))]
      constructor
      · rintro ⟨h0, h1⟩ i hi
        cases i with
        | zero =>
          rw [Nat.testBit_zero] at hi ⊢
          simp only [decide_eq_true_eq] at hi ⊢
          omega
        | succ i =>
          rw [Nat.testBit_succ] at hi ⊢
          exact h1 i hi
      · intro h
        refine ⟨?_, fun i hi => ?_⟩
        · have h0 := h 0
          simp only [Nat.testBit_zero, decide_eq_true_eq] at h0
          omega
        · have := h (i + 1); rw [Nat.testBit_succ, Nat.testBit_succ] at this; exact this hi

/-- Sierpiński's triangle: C(n,k) mod 2. -/
def Sm (n k : ℕ) : ℕ := n.choose k % 2

/-- Powers of the infinite lower-triangular matrix S. -/
def Spow : ℕ → ℕ → ℕ → ℕ
  | 0, n, k => if n = k then 1 else 0
  | m + 1, n, k => ∑ j ∈ range (n + 1), Sm n j * Spow m j k

/-- exp(S)(n,k) = Σ_m S^m(n,k)/m!. -/
noncomputable def expS (n k : ℕ) : ℝ := ∑' m, (Spow m n k : ℝ) / (m.factorial : ℝ)

/-- Bell numbers: B(0) = 1, B(n+1) = Σ_{i ≤ n} C(n,i) B(i). -/
def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), n.choose i * bell i

lemma bell_succ (n : ℕ) : bell (n + 1) = ∑ i ∈ range (n + 1), n.choose i * bell i := by
  rw [bell, Fin.sum_univ_eq_sum_range (fun i => n.choose i * bell i)]

lemma Sm_eq (n k : ℕ) : Sm n k = if bsub n k then 1 else 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [bsub_zero]; simp only [Sm, beq_iff_eq]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [Nat.choose_eq_zero_of_lt hk]; simp; omega
    · have hl : n.choose k % 2 = (Nat.choose (n % 2) (k % 2) * (n / 2).choose (k / 2)) % 2 :=
        Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
      have ih' := ih (n / 2) (Nat.div_lt_self hn (by norm_num)) (k / 2)
      have hu := bsub_unfold n k
      simp only [Sm] at ih' ⊢
      rw [hl, Nat.mul_mod, ih', hu]
      rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h1 | h1 <;>
        rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with h2 | h2 <;>
        rw [h1, h2] <;> cases bsub (n / 2) (k / 2) <;> simp

lemma sum_range_two_mul (N : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ range (2 * N), g j = ∑ b ∈ range N, (g (2 * b) + g (2 * b + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- The matrix-product sum Σ_j [j ⊆ n][k ⊆ j] m^(bd j k) = [k ⊆ n](m+1)^(bd n k). -/
lemma chain_sum (m n k : ℕ) :
    ∑ j ∈ range (n + 1), (if bsub n j then 1 else 0) * (if bsub j k then m ^ bd j k else 0) =
      if bsub n k then (m + 1) ^ bd n k else 0 := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [zero_add, range_one, sum_singleton, bsub_zero, bd_zero]
      simp
    · set a := n / 2
      set r := n % 2
      set c := k / 2
      set t := k % 2
      have ha : a < n := Nat.div_lt_self hn (by norm_num)
      have hna : n = 2 * a + r := (Nat.div_add_mod n 2).symm
      have hr : r < 2 := Nat.mod_lt _ (by norm_num)
      have ht : t < 2 := Nat.mod_lt _ (by norm_num)
      set g : ℕ → ℕ := fun j => (if bsub n j then 1 else 0) * (if bsub j k then m ^ bd j k else 0)
      -- Extend the range to 2(a+1); the extra term (if any) vanishes.
      have hext : ∑ j ∈ range (n + 1), g j = ∑ j ∈ range (2 * (a + 1)), g j := by
        rcases (show r = 0 ∨ r = 1 by omega) with h | h
        · rw [show 2 * (a + 1) = n + 1 + 1 by omega, sum_range_succ g (n + 1)]
          have : bsub n (n + 1) = false := by
            by_contra hc; simp only [Bool.not_eq_false] at hc
            have := bsub_le hc; omega
          have hg : g (n + 1) = 0 := by simp [g, this]
          rw [hg, add_zero]
        · rw [show 2 * (a + 1) = n + 1 by omega]
      have hterm : ∀ b s, s < 2 → g (2 * b + s) =
          ((if decide (s ≤ r) && decide (t ≤ s) then 1 else 0) * m ^ (s - t)) *
          ((if bsub a b then 1 else 0) * (if bsub b c then m ^ bd b c else 0)) := by
        intro b s hs
        simp only [g]
        have e1 : bsub n (2 * b + s) = (decide (s ≤ r) && bsub a b) := by
          have hm1 : (2 * b + s) % 2 = s := by omega
          have hm2 : (2 * b + s) / 2 = b := by omega
          rw [bsub_unfold n (2 * b + s), hm1, hm2]
        have e2 : bsub (2 * b + s) k = (decide (t ≤ s) && bsub b c) := by
          have hm1 : (2 * b + s) % 2 = s := by omega
          have hm2 : (2 * b + s) / 2 = b := by omega
          rw [bsub_unfold (2 * b + s) k, hm1, hm2]
        have e3 : bd (2 * b + s) k = (s - t) + bd b c := by
          have hm1 : (2 * b + s) % 2 = s := by omega
          have hm2 : (2 * b + s) / 2 = b := by omega
          rw [bd_unfold (2 * b + s) k, hm1, hm2]
        rw [e1, e2, e3, pow_add]
        cases decide (s ≤ r) <;> cases decide (t ≤ s) <;> cases bsub a b <;> cases bsub b c <;>
          simp
      have hsplit : ∑ j ∈ range (2 * (a + 1)), g j =
          (((if decide (0 ≤ r) && decide (t ≤ 0) then 1 else 0) * m ^ (0 - t)) +
            ((if decide (1 ≤ r) && decide (t ≤ 1) then 1 else 0) * m ^ (1 - t))) *
          ∑ b ∈ range (a + 1), (if bsub a b then 1 else 0) * (if bsub b c then m ^ bd b c else 0) := by
        rw [sum_range_two_mul, Finset.mul_sum]
        apply sum_congr rfl
        intro b _
        have h0 := hterm b 0 (by norm_num)
        have h1 := hterm b 1 (by norm_num)
        rw [show 2 * b = 2 * b + 0 by ring] at h0 ⊢
        rw [h0, h1]; ring
      rw [hext, hsplit, ih a ha c, bsub_unfold n k, bd_unfold n k]
      change ((if decide (0 ≤ r) && decide (t ≤ 0) then 1 else 0) * m ^ (0 - t) +
          (if decide (1 ≤ r) && decide (t ≤ 1) then 1 else 0) * m ^ (1 - t)) *
          (if bsub a c then (m + 1) ^ bd a c else 0) =
        if (decide (t ≤ r) && bsub a c) then (m + 1) ^ ((r - t) + bd a c) else 0
      interval_cases r <;> interval_cases t <;> cases bsub a c <;> first | (simp [pow_add]; done) | (simp [pow_add]; ring)

lemma bsub_bd_zero (n k : ℕ) : (bsub n k = true ∧ bd n k = 0) ↔ n = k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [bsub_zero, bd_zero]
      simp only [beq_iff_eq, and_true]
      exact eq_comm
    · rw [bsub_unfold, bd_unfold]
      have ih' := ih (n / 2) (Nat.div_lt_self hn (by norm_num)) (k / 2)
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have := ih'.1 ⟨h2, by omega⟩
        omega
      · intro h; subst h
        have := ih'.2 rfl
        exact ⟨⟨le_rfl, this.1⟩, by omega⟩

lemma Spow_eq (m n k : ℕ) : Spow m n k = if bsub n k then m ^ bd n k else 0 := by
  induction m generalizing n k with
  | zero =>
    simp only [Spow]
    by_cases hb : bsub n k = true
    · by_cases hz : bd n k = 0
      · have := (bsub_bd_zero n k).1 ⟨hb, hz⟩
        subst this
        simp [hb, hz]
      · have hne : n ≠ k := fun h => hz ((bsub_bd_zero n k).2 h).2
        simp [hne, hb, zero_pow hz]
    · have hne : n ≠ k := fun h => hb ((bsub_bd_zero n k).2 h).1
      simp [hne, hb]
  | succ m ih =>
    simp only [Spow]
    rw [← chain_sum m n k]
    apply sum_congr rfl
    intro j _
    rw [Sm_eq, ih]

/-- Dobinski's formula: Σ_m m^j/m! = e·B(j). -/
lemma dobinski (j : ℕ) :
    HasSum (fun m : ℕ => (m : ℝ) ^ j / (m.factorial : ℝ)) (Real.exp 1 * bell j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) 1
      rw [← Real.exp_eq_exp_ℝ] at this
      simp only [one_pow] at this
      simp only [pow_zero, bell, Nat.cast_one, mul_one]
      exact this
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      -- shift: m^(i+1)/m! at m+1 is (m+1)^i/m!
      rw [← hasSum_nat_add_iff' 1]
      simp only [range_one, sum_singleton, Nat.cast_zero, zero_pow (Nat.succ_ne_zero i),
        zero_div, sub_zero]
      have hshift : (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (i + 1) / ((m + 1).factorial : ℝ)) =
          fun m : ℕ => ∑ l ∈ range (i + 1), ((i.choose l : ℝ) * ((m : ℝ) ^ l / (m.factorial : ℝ))) := by
        funext m
        rw [Nat.factorial_succ]
        push_cast
        rw [pow_succ, add_pow]
        have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
        have hm : (m : ℝ) + 1 ≠ 0 := by positivity
        rw [mul_comm ((m : ℝ) + 1) (m.factorial : ℝ), mul_div_mul_right _ _ hm, Finset.sum_div]
        apply sum_congr rfl
        intro l _
        rw [one_pow, mul_one]
        ring
      rw [hshift]
      have hb : (Real.exp 1 * (bell (i + 1) : ℝ)) =
          ∑ l ∈ range (i + 1), (i.choose l : ℝ) * (Real.exp 1 * bell l) := by
        rw [bell_succ]; push_cast; rw [Finset.mul_sum]; apply sum_congr rfl; intro l _; ring
      rw [hb]
      apply hasSum_sum
      intro l hl
      exact (ih l (by simp at hl; omega)).mul_left _

theorem A167230_conjecture (n k : ℕ) :
    expS n k / Real.exp 1 = if bsub n k then (bell (bd n k) : ℝ) else 0 := by
  unfold expS
  have hS : ∀ m, (Spow m n k : ℝ) = if bsub n k then (m : ℝ) ^ bd n k else 0 := by
    intro m; rw [Spow_eq]; split_ifs <;> simp
  simp only [hS]
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  split_ifs with h
  · rw [(dobinski (bd n k)).tsum_eq]; field_simp
  · simp

theorem A167230_nonzero (n k : ℕ) (h : expS n k / Real.exp 1 ≠ 0) :
    ∃ j, expS n k / Real.exp 1 = bell j := by
  rw [A167230_conjecture] at h ⊢
  split_ifs at h ⊢ with hb
  · exact ⟨_, rfl⟩
  · exact absurd rfl h
