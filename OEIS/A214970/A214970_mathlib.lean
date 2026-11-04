/-
OEIS A214970, Mathlib proof.

A standard base-φ representation of a real x is a finite set A ⊆ ℤ of
exponents with no two consecutive (`A214970_std`) and x = Σ_(i ∈ A) φ^i.
The change of base f of A214969 (b = φ, c = φ^2) sends n to Σ_(i ∈ A) φ^(2i).

Main theorems:
- `A214970_unique`: standard representations are unique (Bergman), so f is
  well defined on numbers that have one.
- `A214970_main`: for every k ≥ 1,
  * L(2k-1) has the standard representation {2j : |j| ≤ k - 1} and
    f(L(2k-1)) = L(2k-1) · F(2k-1), so L(2k-1) divides f(L(2k-1));
  * L(2k) + 1 has the standard representation {-2k, 0, 2k} and
    f(L(2k) + 1) = (L(2k) + 1)(L(2k) - 1).
  (L = Lucas numbers `A214970_L`, F = `Nat.fib`.) This is Kimberling's
  conjecture: L(2k-1) and L(2k) + 1 are terms of A214970.

- `A214970_greedy_main` (the OEIS definition): with the greedy base-φ
  algorithm formalised (`A214970_top x` = largest i with φ^i ≤ x, one step
  x ↦ x - φ^(top x), stop at remainder 0; `A214970_f x` = Σ φ^(2i) over the
  exponents taken), f(L(2k-1)) = L(2k-1)·F(2k-1) and
  f(L(2k)+1) = (L(2k)+1)(L(2k)-1) for every k ≥ 1. The step "greedy on a
  standard representation terminates and takes exactly its exponents" is
  `A214970_greedy_std` (it needs only the bound `A214970_bound`).
Nothing is outside Lean. (Termination of the greedy algorithm on every
positive integer, Bergman's theorem, is not needed and not proved here.)
-/
import Mathlib

open Finset Real

/-- No two consecutive exponents. -/
def A214970_std (A : Finset ℤ) : Prop := ∀ i ∈ A, i + 1 ∉ A

/-- Lucas numbers. -/
def A214970_L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => A214970_L (n + 1) + A214970_L n

theorem A214970_L_eq (n : ℕ) : (A214970_L n : ℝ) = goldenRatio ^ n + goldenConj ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => norm_num [A214970_L]
    | 1, _ => simp [A214970_L]
    | m + 2, ih =>
      simp only [A214970_L]
      push_cast
      rw [ih (m + 1) (by omega), ih m (by omega)]
      have h1 : goldenRatio ^ (m + 2) = goldenRatio ^ (m + 1) + goldenRatio ^ m := by
        rw [pow_add, goldenRatio_sq]; ring_nf
      have h2 : goldenConj ^ (m + 2) = goldenConj ^ (m + 1) + goldenConj ^ m := by
        rw [pow_add, goldenConj_sq]; ring_nf
      rw [h1, h2]
      ring_nf

/-- The sum of a standard representation with all exponents ≤ M is < φ^(M+1). -/
theorem A214970_bound (A : Finset ℤ) :
    A214970_std A → ∀ M : ℤ, (∀ x ∈ A, x ≤ M) →
      ∑ i ∈ A, goldenRatio ^ i < goldenRatio ^ (M + 1) := by
  induction A using Finset.induction_on_max with
  | empty => intro _ M _; simp; positivity
  | insert a s hlt ih =>
    intro hstd M hM
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hstd' : A214970_std s := fun i hi hi1 => hstd i (mem_insert_of_mem hi)
      (mem_insert_of_mem hi1)
    have hs2 : ∀ x ∈ s, x ≤ a - 2 := by
      intro x hx
      have h1 := hlt x hx
      have h2 : x + 1 ≠ a := fun h => hstd x (mem_insert_of_mem hx) (by rw [h]; exact mem_insert_self a s)
      omega
    have hrest := ih hstd' (a - 2) hs2
    rw [sum_insert has]
    have hφ := goldenRatio_pos
    have hrec : goldenRatio ^ (a + 1) = goldenRatio ^ a + goldenRatio ^ (a - 2 + 1) := by
      have : goldenRatio ^ (a + 1) = goldenRatio ^ (a - 1) * goldenRatio ^ (2 : ℤ) := by
        rw [← zpow_add₀ goldenRatio_ne_zero]; ring_nf
      rw [this, zpow_two, ← sq, goldenRatio_sq, show a - 2 + 1 = a - 1 by ring,
        show a = (a - 1) + 1 by ring, zpow_add_one₀ goldenRatio_ne_zero]
      ring_nf
    have hmono : goldenRatio ^ (a + 1) ≤ goldenRatio ^ (M + 1) :=
      zpow_le_zpow_right₀ one_lt_goldenRatio.le (by have := hM a (mem_insert_self a s); omega)
    linarith

/-- Bergman: standard representations are unique. -/
theorem A214970_unique (A B : Finset ℤ) (hA : A214970_std A) (hB : A214970_std B)
    (h : ∑ i ∈ A, goldenRatio ^ i = ∑ i ∈ B, goldenRatio ^ i) : A = B := by
  classical
  have hsplitA := sum_sdiff (f := fun i => goldenRatio ^ i) (inter_subset_left (s₁ := A) (s₂ := B))
  have hsplitB := sum_sdiff (f := fun i => goldenRatio ^ i) (inter_subset_right (s₁ := A) (s₂ := B))
  rw [sdiff_inter_self_left] at hsplitA
  rw [sdiff_inter_self_right] at hsplitB
  have heq : ∑ i ∈ A \ B, goldenRatio ^ i = ∑ i ∈ B \ A, goldenRatio ^ i := by linarith
  have hstdA : A214970_std (A \ B) := fun i hi hi1 =>
    hA i (mem_sdiff.mp hi).1 (mem_sdiff.mp hi1).1
  have hstdB : A214970_std (B \ A) := fun i hi hi1 =>
    hB i (mem_sdiff.mp hi).1 (mem_sdiff.mp hi1).1
  -- The largest exponent of (A \ B) ∪ (B \ A) gives a contradiction.
  --
  have key : ∀ X Y : Finset ℤ, A214970_std Y → Disjoint X Y →
      ∑ i ∈ X, goldenRatio ^ i = ∑ i ∈ Y, goldenRatio ^ i →
      ∀ m ∈ X, (∀ y ∈ Y, y ≤ m) → False := by
    intro X Y hY hXY hsum m hm hYm
    have hY' : ∀ y ∈ Y, y ≤ m - 1 := by
      intro y hy
      have := hYm y hy
      have hne : y ≠ m := fun h => disjoint_left.mp hXY hm (h ▸ hy)
      omega
    have h1 := A214970_bound Y hY (m - 1) hY'
    rw [show m - 1 + 1 = m by ring] at h1
    have h2 : goldenRatio ^ m ≤ ∑ i ∈ X, goldenRatio ^ i :=
      single_le_sum (f := fun i => goldenRatio ^ i) (fun i _ => by positivity) hm
    linarith
  by_contra hne
  have hne' : (A \ B ∪ B \ A).Nonempty := by
    by_contra h0
    rw [not_nonempty_iff_eq_empty, union_eq_empty, sdiff_eq_empty_iff_subset,
      sdiff_eq_empty_iff_subset] at h0
    exact hne (Subset.antisymm h0.1 h0.2)
  set m := (A \ B ∪ B \ A).max' hne' with hm
  have hmem := max'_mem _ hne'
  rw [← hm] at hmem
  rcases mem_union.mp hmem with h1 | h1
  · exact key (A \ B) (B \ A) hstdB disjoint_sdiff_sdiff heq m h1
      (fun y hy => le_max' _ y (mem_union_right _ hy))
  · exact key (B \ A) (A \ B) hstdA disjoint_sdiff_sdiff.symm heq.symm m h1
      (fun y hy => le_max' _ y (mem_union_left _ hy))

theorem A214970_geom (x : ℝ) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; ring_nf

theorem A214970_main (k : ℕ) (hk : 1 ≤ k) :
    (∃ A : Finset ℤ, A214970_std A ∧
      ∑ i ∈ A, goldenRatio ^ i = (A214970_L (2 * k - 1) : ℝ) ∧
      ∑ i ∈ A, goldenRatio ^ (2 * i) =
        ((A214970_L (2 * k - 1) * (Nat.fib (2 * k - 1) : ℤ) : ℤ) : ℝ)) ∧
    (∃ B : Finset ℤ, A214970_std B ∧
      ∑ i ∈ B, goldenRatio ^ i = ((A214970_L (2 * k) + 1 : ℤ) : ℝ) ∧
      ∑ i ∈ B, goldenRatio ^ (2 * i) =
        (((A214970_L (2 * k) + 1) * (A214970_L (2 * k) - 1) : ℤ) : ℝ)) := by
  set u := goldenRatio with hu
  have hu0 : u ≠ 0 := goldenRatio_ne_zero
  have hupos : 0 < u := goldenRatio_pos
  have hψ : goldenConj = -u⁻¹ := by rw [hu, inv_goldenRatio, neg_neg]
  have hu2 : u ^ 2 = u + 1 := goldenRatio_sq
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5 : u - goldenConj = Real.sqrt 5 := goldenRatio_sub_goldenConj
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hm : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [hm]
  constructor
  · -- {2i - 2j : i < 2j + 1}
    --
    set A := (range (2 * j + 1)).image (fun i : ℕ => 2 * (i : ℤ) - 2 * j) with hA
    have hinj : Set.InjOn (fun i : ℕ => 2 * (i : ℤ) - 2 * j) (range (2 * j + 1) : Set ℕ) :=
      fun a _ b _ h => by simp only at h; omega
    refine ⟨A, ?_, ?_, ?_⟩
    · intro i hi hi1
      simp only [hA, mem_image] at hi hi1
      obtain ⟨a, _, rfl⟩ := hi
      obtain ⟨b, _, hb⟩ := hi1
      omega
    · rw [sum_image hinj]
      have hterm : ∀ i : ℕ, u ^ (2 * (i : ℤ) - 2 * j) = (u ^ 2) ^ i / u ^ (2 * j) := by
        intro i
        rw [zpow_sub₀ hu0, ← pow_mul]
        norm_cast
      simp only [hterm, ← sum_div]
      have hg := A214970_geom (u ^ 2) (2 * j + 1)
      rw [A214970_L_eq, hψ, Odd.neg_pow ⟨j, rfl⟩, inv_pow, ← hu]
      rw [show u ^ 2 - 1 = u by linarith] at hg
      have hS : ∑ i ∈ range (2 * j + 1), (u ^ 2) ^ i = ((u ^ 2) ^ (2 * j + 1) - 1) / u := by
        rw [← hg]; field_simp
      rw [hS]
      field_simp
      ring_nf
    · rw [sum_image hinj]
      have hterm : ∀ i : ℕ, u ^ (2 * (2 * (i : ℤ) - 2 * j)) = (u ^ 4) ^ i / u ^ (4 * j) := by
        intro i
        rw [show 2 * (2 * (i : ℤ) - 2 * j) = 4 * (i : ℤ) - 4 * j by ring, zpow_sub₀ hu0,
          ← pow_mul]
        norm_cast
      simp only [hterm, ← sum_div]
      have hg := A214970_geom (u ^ 4) (2 * j + 1)
      have hu4 : u ^ 4 - 1 = Real.sqrt 5 * u ^ 2 := by
        rw [← hs5, hψ]
        field_simp
        nlinarith [hu2]
      rw [hu4] at hg
      have hS : ∑ i ∈ range (2 * j + 1), (u ^ 4) ^ i =
          ((u ^ 4) ^ (2 * j + 1) - 1) / (Real.sqrt 5 * u ^ 2) := by
        rw [← hg]; field_simp
      rw [hS]
      push_cast
      rw [A214970_L_eq, Real.coe_fib_eq, hψ, ← hu]
      rw [Odd.neg_pow ⟨j, rfl⟩, inv_pow]
      have hs0 : Real.sqrt 5 ≠ 0 := by positivity
      field_simp
      ring_nf
  · -- {-2(j+1), 0, 2(j+1)}
    --
    set n : ℤ := 2 * ((j : ℤ) + 1) with hn
    have hn2 : 2 ≤ n := by omega
    refine ⟨{-n, 0, n}, ?_, ?_, ?_⟩
    · intro i hi hi1
      simp only [mem_insert, mem_singleton] at hi hi1
      omega
    · have hne1 : -n ≠ 0 := by omega
      have hne2 : -n ≠ n := by omega
      have hne3 : (0 : ℤ) ≠ n := by omega
      rw [sum_insert (by simp [hne1, hne2]), sum_insert (by simp [hne3]), sum_singleton]
      push_cast
      rw [A214970_L_eq, hψ, Even.neg_pow ⟨j + 1, by ring⟩, inv_pow, ← hu]
      rw [show (2 * (j + 1) : ℕ) = n.toNat by omega]
      rw [zpow_neg, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_zero]
      ring_nf
    · have hne1 : -n ≠ 0 := by omega
      have hne2 : -n ≠ n := by omega
      have hne3 : (0 : ℤ) ≠ n := by omega
      rw [sum_insert (by simp [hne1, hne2]), sum_insert (by simp [hne3]), sum_singleton]
      have hN : n = ((2 * (j + 1) : ℕ) : ℤ) := by rw [hn]; push_cast; rfl
      have hB1 : u ^ (2 * -n) = ((u ^ (2 * (j + 1))) ^ 2)⁻¹ := by
        rw [hN, mul_neg, zpow_neg, ← zpow_natCast, ← zpow_natCast, ← zpow_mul]
        push_cast
        ring_nf
      have hB2 : u ^ (2 * n) = (u ^ (2 * (j + 1))) ^ 2 := by
        rw [hN, ← zpow_natCast, ← zpow_natCast, ← zpow_mul]
        push_cast
        ring_nf
      rw [hB1, hB2, mul_zero, zpow_zero]
      push_cast
      rw [A214970_L_eq, hψ, Even.neg_pow ⟨j + 1, by ring⟩, inv_pow, ← hu]
      field_simp
      ring_nf

/-! ## The greedy base-φ expansion (OEIS definition of A214969)

`A214970_top x` = the largest integer i with φ^i ≤ x (x > 0). One greedy
step replaces x by x - φ^(top x); `A214970_greedyRem T x` is the remainder
after T steps and `A214970_greedyDigits T x` the list of exponents taken
(a step on x ≤ 0 does nothing). The expansion terminates when the remainder
is 0; `A214970_f x` = Σ φ^(2i) over the exponents of the terminated greedy
expansion (0 if it never terminates). -/

noncomputable def A214970_top (x : ℝ) : ℤ := ⌊Real.logb goldenRatio x⌋

theorem A214970_top_spec (x : ℝ) (hx : 0 < x) :
    goldenRatio ^ (A214970_top x) ≤ x ∧ x < goldenRatio ^ (A214970_top x + 1) := by
  have h1 := one_lt_goldenRatio
  have hx' : goldenRatio ^ (Real.logb goldenRatio x) = x :=
    Real.rpow_logb goldenRatio_pos h1.ne' hx
  have hf := Int.floor_le (Real.logb goldenRatio x)
  have hf' := Int.lt_floor_add_one (Real.logb goldenRatio x)
  constructor
  · rw [A214970_top, ← Real.rpow_intCast]
    conv_rhs => rw [← hx']
    exact Real.rpow_le_rpow_of_exponent_le h1.le hf
  · rw [A214970_top, ← Real.rpow_intCast]
    conv_lhs => rw [← hx']
    push_cast
    exact Real.rpow_lt_rpow_of_exponent_lt h1 hf'

theorem A214970_top_eq (x : ℝ) (hx : 0 < x) (i : ℤ) (h1 : goldenRatio ^ i ≤ x)
    (h2 : x < goldenRatio ^ (i + 1)) : A214970_top x = i := by
  obtain ⟨t1, t2⟩ := A214970_top_spec x hx
  have hφ := one_lt_goldenRatio
  have a : A214970_top x < i + 1 := (zpow_lt_zpow_iff_right₀ hφ).1 (lt_of_le_of_lt t1 h2)
  have b : i < A214970_top x + 1 := (zpow_lt_zpow_iff_right₀ hφ).1 (lt_of_le_of_lt h1 t2)
  omega

noncomputable def A214970_greedyRem : ℕ → ℝ → ℝ
  | 0, x => x
  | T + 1, x => if x ≤ 0 then x else A214970_greedyRem T (x - goldenRatio ^ (A214970_top x))

noncomputable def A214970_greedyDigits : ℕ → ℝ → List ℤ
  | 0, _ => []
  | T + 1, x => if x ≤ 0 then [] else
      A214970_top x :: A214970_greedyDigits T (x - goldenRatio ^ (A214970_top x))

/-- Once the remainder is 0, further steps change nothing. -/
theorem A214970_greedy_stable : ∀ (T : ℕ) (x : ℝ), A214970_greedyRem T x = 0 →
    ∀ s, A214970_greedyRem (T + s) x = 0 ∧
      A214970_greedyDigits (T + s) x = A214970_greedyDigits T x := by
  have h0 : ∀ s, A214970_greedyRem s 0 = 0 ∧ A214970_greedyDigits s 0 = [] := by
    intro s; cases s <;> simp [A214970_greedyRem, A214970_greedyDigits]
  intro T
  induction T with
  | zero =>
    intro x hx s
    simp only [A214970_greedyRem] at hx
    subst hx
    simpa [A214970_greedyDigits] using h0 s
  | succ T ih =>
    intro x hx s
    rw [show T + 1 + s = (T + s) + 1 by ring]
    by_cases hx0 : x ≤ 0
    · simp only [A214970_greedyRem, hx0, ↓reduceIte] at hx ⊢
      simp only [A214970_greedyDigits, hx0, ↓reduceIte]
      exact ⟨hx, trivial⟩
    · simp only [A214970_greedyRem, hx0, ↓reduceIte] at hx ⊢
      simp only [A214970_greedyDigits, hx0, ↓reduceIte, List.cons.injEq, true_and]
      exact ih _ hx s

/-- f of A214969 (b = φ, c = φ²) through the greedy expansion. -/
noncomputable def A214970_f (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ T, A214970_greedyRem T x = 0 then
    ((A214970_greedyDigits (Nat.find h) x).map (fun i => goldenRatio ^ (2 * i))).sum
  else 0

/-- On a standard representation the greedy algorithm takes exactly its exponents. -/
theorem A214970_greedy_std (A : Finset ℤ) (hA : A214970_std A) (g : ℤ → ℝ) :
    A214970_greedyRem A.card (∑ i ∈ A, goldenRatio ^ i) = 0 ∧
    ((A214970_greedyDigits A.card (∑ i ∈ A, goldenRatio ^ i)).map g).sum = ∑ i ∈ A, g i := by
  induction A using Finset.induction_on_max with
  | empty => simp [A214970_greedyRem, A214970_greedyDigits]
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hstd' : A214970_std s := fun i hi hi1 => hA i (mem_insert_of_mem hi)
      (mem_insert_of_mem hi1)
    obtain ⟨ih1, ih2⟩ := ih hstd'
    have hpos : 0 ≤ ∑ i ∈ s, goldenRatio ^ i := sum_nonneg fun i _ => by positivity
    have hx : 0 < ∑ i ∈ insert a s, goldenRatio ^ i := by
      rw [sum_insert has]; have : 0 < goldenRatio ^ a := by positivity
      linarith
    have htop : A214970_top (∑ i ∈ insert a s, goldenRatio ^ i) = a := by
      apply A214970_top_eq _ hx
      · rw [sum_insert has]; linarith
      · exact A214970_bound _ hA a (fun x hx => by
          rcases mem_insert.1 hx with rfl | hx
          · exact le_rfl
          · exact (hlt x hx).le)
    have hstep : ∑ i ∈ insert a s, goldenRatio ^ i - goldenRatio ^ a = ∑ i ∈ s, goldenRatio ^ i := by
      rw [sum_insert has]; ring
    rw [card_insert_of_notMem has]
    simp only [A214970_greedyRem, A214970_greedyDigits, not_le.2 hx, ↓reduceIte, htop, hstep,
      List.map_cons, List.sum_cons]
    refine ⟨ih1, ?_⟩
    rw [ih2, sum_insert has]

theorem A214970_f_std (A : Finset ℤ) (hA : A214970_std A) :
    A214970_f (∑ i ∈ A, goldenRatio ^ i) = ∑ i ∈ A, goldenRatio ^ (2 * i) := by
  classical
  have h := A214970_greedy_std A hA (fun i => goldenRatio ^ (2 * i))
  have hex : ∃ T, A214970_greedyRem T (∑ i ∈ A, goldenRatio ^ i) = 0 := ⟨_, h.1⟩
  unfold A214970_f
  simp only [hex, ↓reduceDIte]
  have hle : Nat.find hex ≤ A.card := Nat.find_min' hex h.1
  have hst := A214970_greedy_stable _ _ (Nat.find_spec hex) (A.card - Nat.find hex)
  rw [Nat.add_sub_cancel' hle] at hst
  rw [← hst.2, h.2]

/-- Kimberling's conjecture from the greedy definition: f(L(2k-1)) = L(2k-1)·F(2k-1) and
f(L(2k)+1) = (L(2k)+1)(L(2k)-1), so both numbers divide their images. -/
theorem A214970_greedy_main (k : ℕ) (hk : 1 ≤ k) :
    A214970_f (A214970_L (2 * k - 1) : ℝ) =
      ((A214970_L (2 * k - 1) * (Nat.fib (2 * k - 1) : ℤ) : ℤ) : ℝ) ∧
    A214970_f ((A214970_L (2 * k) + 1 : ℤ) : ℝ) =
      (((A214970_L (2 * k) + 1) * (A214970_L (2 * k) - 1) : ℤ) : ℝ) := by
  obtain ⟨⟨A, hA, hA1, hA2⟩, ⟨B, hB, hB1, hB2⟩⟩ := A214970_main k hk
  refine ⟨?_, ?_⟩
  · rw [← hA1, A214970_f_std A hA, hA2]
  · rw [← hB1, A214970_f_std B hB, hB2]
