import Mathlib
import PNTPlus.Wiener

/-
OEIS A083762: a(1) = 1 and a(n) is the least unused positive integer m such that the decimal
concatenation of a(1), ..., a(n-1), m and the digit 1 is prime. Partial result: the greedy never
gets stuck, so a(n) is defined for every n.

Checked here (Lean + Mathlib + the vendored PNT+ file `PNTPlus.Wiener`):
* `prime_one_mod_ten_window`: for naturals 1 <= A, A + 2 <= B and any real K there are d with 10^d > K and a
  prime p = 1 (mod 10) with A 10^d < p < B 10^d. Inputs: the prime number theorem for primes
  = 1 (mod 10) in the form psi(N; 10, 1)/N -> 1/4 (`WeakPNT_AP`, PNT+), and psi - theta = O(sqrt x)
  (`Chebyshev.psi_sub_theta_le_mul_sqrt`, Mathlib).
* `exists_next`: for every C and every finite set U there is m > 0, m not in U, with
  `concat1 C m = (C 10^len(m) + m) 10 + 1` prime (len = number of decimal digits).
* `a`, `state`: the sequence defined by the greedy rule (least such m), total by `exists_next`;
  `a_spec`: a(n) > 0, a(n) is unused, and the concatenation is prime; `a_min`: a(n) is least.
* `a_injective`: no value repeats; `a_zero`, `a_one`: a(1) = 1, a(2) = 3 as in the OEIS data.
NOT checked here: whether every positive integer appears (the OEIS conjecture, open).
Indexing: `a 0` is the OEIS a(1).
-/

open Real Filter Finset ArithmeticFunction

/-- Decimal concatenation of C, m and the digit 1. -/
def concat1 (C m : ℕ) : ℕ := (C * 10 ^ (Nat.digits 10 m).length + m) * 10 + 1

/-- Primes `p ≡ 1 (mod 10)` in `(A 10^d, B 10^d)` for arbitrarily large `d` (PNT in progressions). -/
theorem prime_one_mod_ten_window (A B : ℕ) (hA : 1 ≤ A) (hAB : A + 2 ≤ B) (K : ℝ) :
    ∃ d : ℕ, K < (10 : ℝ) ^ d ∧
      ∃ p : ℕ, p.Prime ∧ p % 10 = 1 ∧ A * 10 ^ d < p ∧ p < B * 10 ^ d := by
  have hT := WeakPNT_AP (q := 10) (a := 1) (by norm_num) (by norm_num) (by norm_num)
  have h10 : Nat.totient 10 = 4 := by decide
  rw [h10] at hT
  set f : ℕ → ℝ := fun n => if n % 10 = 1 then Λ n else 0 with hf
  set S : ℕ → ℝ := fun N => cumsum f N with hS
  have hAR : (0 : ℝ) ≤ A := by positivity
  have hABR : (A : ℝ) + 2 ≤ B := by exact_mod_cast hAB
  set δ : ℝ := 1 / (4 * (A + B + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδA : (A + B + 1 : ℝ) * δ = 1 / 4 := by rw [hδ]; field_simp
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hT) δ hδpos
  have hlow : ∀ N : ℕ, N0 ≤ N → 0 < N → (N : ℝ) * (1 / 4 - δ) ≤ S N := by
    intro N hN hpos
    have h := hN0 N hN
    rw [Real.dist_eq, abs_lt] at h
    have hNR : (0 : ℝ) < N := by exact_mod_cast hpos
    have : S N / N > 1 / 4 - δ := by simp only [hS]; linarith [h.1]
    rw [gt_iff_lt, lt_div_iff₀ hNR] at this
    linarith
  have hup : ∀ N : ℕ, N0 ≤ N → 0 < N → S N ≤ (N : ℝ) * (1 / 4 + δ) := by
    intro N hN hpos
    have h := hN0 N hN
    rw [Real.dist_eq, abs_lt] at h
    have hNR : (0 : ℝ) < N := by exact_mod_cast hpos
    have : S N / N < 1 / 4 + δ := by simp only [hS]; linarith [h.2]
    rw [div_lt_iff₀ hNR] at this
    linarith
  obtain ⟨C0, hC0⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (|K| + 64 * C0 ^ 2 * B + N0 + 10) (by norm_num : (1 : ℝ) < 10)
  have hB0 : (0 : ℝ) ≤ 64 * C0 ^ 2 * B := by positivity
  have hN00 : (0 : ℝ) ≤ N0 := by positivity
  have hK0 : (0 : ℝ) ≤ |K| := abs_nonneg K
  refine ⟨d, by linarith [le_abs_self K], ?_⟩
  by_contra hno
  push Not at hno
  set t : ℝ := (10 : ℝ) ^ d with ht
  set x : ℕ := A * 10 ^ d + 1 with hx
  set y : ℕ := B * 10 ^ d with hy
  have htR : ((10 ^ d : ℕ) : ℝ) = t := by push_cast; rfl
  have hxR : (x : ℝ) = A * t + 1 := by rw [hx]; push_cast; rfl
  have hyR : (y : ℝ) = B * t := by rw [hy]; push_cast; rfl
  have ht10 : 10 ≤ t := by linarith
  have hxy : x ≤ y := by
    have h1 : (x : ℝ) ≤ y := by rw [hxR, hyR]; nlinarith
    exact_mod_cast h1
  have hxN0 : N0 ≤ x := by
    have h1 : (N0 : ℝ) ≤ x := by
      rw [hxR]
      have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
      nlinarith
    exact_mod_cast h1
  -- Lower bound from the PNT in progressions.
  have hdiff : t / 8 ≤ S y - S x := by
    have h1 := hlow y (hxN0.trans hxy) (by omega)
    have h2 := hup x hxN0 (by omega)
    rw [hyR] at h1
    rw [hxR] at h2
    have e : B * t * (1 / 4 - δ) - (A * t + 1) * (1 / 4 + δ)
        = t * ((B - A) / 4 - (A + B) * δ) - 1 / 4 - δ := by ring
    have h3 : (A + B : ℝ) * δ ≤ 1 / 4 := by nlinarith
    have h4 : δ ≤ 1 / 4 := by nlinarith
    have h5 : t * (1 / 4) ≤ t * ((B - A) / 4 - (A + B) * δ) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    linarith
  -- Upper bound: without such a prime, only proper prime powers contribute.
  have hsub : S y - S x ≤ Chebyshev.psi y - Chebyshev.theta y := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    have e : S y - S x = ∑ n ∈ Ico x y, f n := by
      simp only [hS, cumsum]; rw [Finset.sum_Ico_eq_sub _ hxy]
    rw [e]
    have e2 : ∑ n ∈ Ico x y, f n = ∑ n ∈ (Ico x y).filter (fun n => ¬ n.Prime), f n := by
      rw [Finset.sum_filter_of_ne]
      intro n hn hfn hp
      apply hfn
      simp only [hf]
      split_ifs with h1
      · exfalso
        rw [Finset.mem_Ico] at hn
        have hlt := hno n hp h1 (by omega)
        omega
      · rfl
    rw [e2]
    calc ∑ n ∈ (Ico x y).filter (fun n => ¬ n.Prime), f n
        ≤ ∑ n ∈ (Ico x y).filter (fun n => ¬ n.Prime), Λ n := by
          apply Finset.sum_le_sum
          intro n _
          simp only [hf]
          split_ifs
          · exact le_refl _
          · exact vonMangoldt_nonneg
      _ ≤ ∑ n ∈ (Ioc 0 y).filter (fun n => ¬ n.Prime), Λ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            have hx1 : 1 ≤ x := by rw [hx]; omega
            simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hn ⊢
            exact ⟨⟨by omega, by omega⟩, hn.2⟩
          · intro _ _ _; exact vonMangoldt_nonneg
  have hC := hC0 y
  rw [hyR] at hC
  have hkey : t / 8 ≤ C0 * √(B * t) := by
    have := hsub
    rw [hyR] at this
    linarith
  have hsq : 0 ≤ √(B * t) := Real.sqrt_nonneg _
  have hC0pos : 0 < C0 := by
    by_contra hneg
    push Not at hneg
    have : C0 * √(B * t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hsq
    linarith
  have hsq2 : √(B * t) ^ 2 = B * t := Real.sq_sqrt (by positivity)
  have h64 : t ^ 2 ≤ 64 * C0 ^ 2 * (B * t) := by
    have h0 : 0 ≤ t / 8 := by linarith
    have := mul_le_mul hkey hkey h0 (by positivity)
    nlinarith
  have : t ≤ 64 * C0 ^ 2 * B := by
    have htp : 0 < t := by linarith
    nlinarith
  have : (0 : ℝ) ≤ |K| := abs_nonneg K
  have : (0 : ℝ) ≤ N0 := by positivity
  linarith

/-- The greedy step always succeeds: some unused `m > 0` makes `C m 1` prime. -/
theorem exists_next (C : ℕ) (U : Finset ℕ) :
    ∃ m : ℕ, 0 < m ∧ m ∉ U ∧ (concat1 C m).Prime := by
  obtain ⟨d, hd, p, hp, hp10, hlo, hhi⟩ :=
    prime_one_mod_ten_window (10 * C + 1) (10 * C + 10) (by omega) (by omega) (10 * (U.sup id + 1) : ℕ)
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      have : (10 : ℝ) ≤ (10 * (U.sup id + 1) : ℕ) := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (U.sup id)]
      simp at hd; linarith
    · exact h
  obtain ⟨e', rfl⟩ : ∃ e', d = e' + 1 := ⟨d - 1, by omega⟩
  set e := 10 ^ e' with he
  have hpow : 10 ^ (e' + 1) = 10 * e := by rw [pow_succ]; ring
  have hdR : (10 * (U.sup id + 1) : ℕ) < 10 * e := by
    have : ((10 * (U.sup id + 1) : ℕ) : ℝ) < ((10 * e : ℕ) : ℝ) := by
      rw [← hpow]; exact_mod_cast hd
    exact_mod_cast this
  rw [hpow] at hlo hhi
  set W := C * e with hW
  have hlo' : 100 * W + 10 * e < p := by
    have : (10 * C + 1) * (10 * e) = 100 * W + 10 * e := by rw [hW]; ring
    omega
  have hhi' : p < 100 * W + 100 * e := by
    have : (10 * C + 10) * (10 * e) = 100 * W + 100 * e := by rw [hW]; ring
    omega
  set n := p / 10 with hn
  have hpn : p = 10 * n + 1 := by omega
  set m := n - 10 * W with hm
  have hm1 : e ≤ m := by omega
  have hm2 : m < 10 * e := by omega
  have he0 : 0 < e := by positivity
  have hlen : (Nat.digits 10 m).length = e' + 1 := by
    apply le_antisymm
    · rw [Nat.digits_length_le_iff (by norm_num), hpow]; exact hm2
    · by_contra hlt
      push Not at hlt
      have : (Nat.digits 10 m).length ≤ e' := by omega
      rw [Nat.digits_length_le_iff (by norm_num)] at this
      omega
  refine ⟨m, by omega, ?_, ?_⟩
  · intro hmU
    have : m ≤ U.sup id := Finset.le_sup (f := id) hmU
    omega
  · have : concat1 C m = p := by
      unfold concat1
      rw [hlen, hpow]
      have : C * (10 * e) = 10 * W := by rw [hW]; ring
      rw [this]; omega
    rw [this]; exact hp

/-- State after `n` greedy steps: (concatenation so far, used values). -/
noncomputable def state : ℕ → ℕ × Finset ℕ
  | 0 => (0, ∅)
  | n + 1 =>
    let s := state n
    let m := Nat.find (exists_next s.1 s.2)
    (s.1 * 10 ^ (Nat.digits 10 m).length + m, insert m s.2)

/-- The sequence: `a n` is the OEIS term a(n + 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.find (exists_next (state n).1 (state n).2)

theorem a_spec (n : ℕ) :
    0 < a n ∧ a n ∉ (state n).2 ∧ (concat1 (state n).1 (a n)).Prime :=
  Nat.find_spec (exists_next (state n).1 (state n).2)

theorem a_min (n m : ℕ) (hm : m < a n) :
    ¬ (0 < m ∧ m ∉ (state n).2 ∧ (concat1 (state n).1 m).Prime) :=
  Nat.find_min (exists_next (state n).1 (state n).2) hm

lemma state_used (n : ℕ) : (state (n + 1)).2 = insert (a n) (state n).2 := rfl

lemma mem_state_of_lt {i n : ℕ} (h : i < n) : a i ∈ (state n).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [state_used]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact Finset.mem_insert_of_mem (ih h')
    · subst h'; exact Finset.mem_insert_self _ _

/-- The terms are pairwise distinct. -/
theorem a_injective : Function.Injective a := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := mem_state_of_lt h
    rw [hij] at this
    exact (a_spec j).2.1 this
  · have := mem_state_of_lt h
    rw [← hij] at this
    exact (a_spec i).2.1 this

/-- Sanity check against the OEIS data: a(1) = 1 and a(2) = 3 (11 and 131 are prime, 121 is not). -/
theorem a_zero : a 0 = 1 := by
  rw [a, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by simp [state], ?_⟩, ?_⟩
  · simp [state, concat1]; norm_num
  · intro n hn h; omega

lemma state_one : state 1 = (1, {1}) := by
  show ((state 0).1 * 10 ^ (Nat.digits 10 (a 0)).length + a 0, insert (a 0) (state 0).2) = (1, {1})
  rw [a_zero]; simp [state]

theorem a_one : a 1 = 3 := by
  rw [a, Nat.find_eq_iff, state_one]
  refine ⟨⟨by norm_num, by simp, ?_⟩, ?_⟩
  · simp [concat1]; norm_num
  · intro n hn h
    interval_cases n
    · omega
    · simp at h
    · simp [concat1] at h; norm_num at h
