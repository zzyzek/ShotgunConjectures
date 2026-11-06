/-
OEIS A216971: T(n,k) is the number of functions f : {1..n} -> {1..n} that have
exactly k nonrecurrent elements mapped to some recurrent element.
Conjecture (Jon Perry, entry text): every entry in row n is divisible by n.

Definitions (as in the entry).
* `Rec f x`: x is recurrent, f^[m] x = x for some m >= 1.
* `stat f`: number of x with x nonrecurrent and f x recurrent.
* `T n k`: number of f : Fin n -> Fin n with stat f = k.

Main theorem.
* `A216971_main`: for n >= 1 and every k, n divides T n k.

Route.
* `S n k r`: the f counted by T n k whose recurrent set has r elements.
  `T_eq_sum`: T n k is the sum of #S n k r over r; `S_zero`: S n k 0 is empty.
* `double_count`: r * #S = n * M, where M counts the f in S with 0 recurrent
  (relabelling by the transposition (x 0), `conj`, moves "x recurrent" to
  "0 recurrent" and keeps stat and the number of recurrent points).
* `fact_dvd_A`: for a fixed set R, the f with recurrent set R and stat k
  number (#R)! times the number of those that fix R pointwise: such f is a
  permutation of R glued to its values off R (`replace`, `permOf`, `glue`).
  Hence r! divides M, and r * #S = n * M gives n | #S for r >= 1.

Not checked in this file: agreement of `T` with the OEIS data terms
(certificate/check.py brute-forces n <= 6 and checks the b-file rows).
-/
import Mathlib

open Finset Function

namespace A216971

open scoped Classical

variable {n : ℕ}

/-- `x` is recurrent for `f`: `f^[m] x = x` for some `m ≥ 1`. -/
def Rec (f : Fin n → Fin n) (x : Fin n) : Prop := ∃ m, 0 < m ∧ f^[m] x = x

/-- The set of recurrent elements. -/
noncomputable def recSet (f : Fin n → Fin n) : Finset (Fin n) := univ.filter (Rec f)

/-- Number of nonrecurrent elements mapped to a recurrent element. -/
noncomputable def stat (f : Fin n → Fin n) : ℕ :=
  #(univ.filter fun x => ¬ Rec f x ∧ Rec f (f x))

/-- A216971: T(n,k). -/
noncomputable def T (n k : ℕ) : ℕ := #(univ.filter fun f : Fin n → Fin n => stat f = k)

lemma mem_recSet {f : Fin n → Fin n} {x : Fin n} : x ∈ recSet f ↔ Rec f x := by
  simp [recSet]

lemma rec_iff {f : Fin n → Fin n} {x : Fin n} : Rec f x ↔ x ∈ periodicPts f := by
  rw [mem_periodicPts]
  rfl

lemma rec_apply {f : Fin n → Fin n} {x : Fin n} (h : Rec f x) : Rec f (f x) := by
  obtain ⟨m, hm, hx⟩ := h
  exact ⟨m, hm, by rw [← iterate_succ_apply, iterate_succ_apply', hx]⟩

lemma maps_of {f : Fin n → Fin n} {R : Finset (Fin n)} (hR : recSet f = R) {x : Fin n}
    (hx : x ∈ R) : f x ∈ R := by
  subst hR
  exact mem_recSet.2 (rec_apply (mem_recSet.1 hx))

lemma injOn_of {f : Fin n → Fin n} {R : Finset (Fin n)} (hR : recSet f = R) :
    Set.InjOn f (R : Set (Fin n)) := by
  subst hR
  have he : ((recSet f : Finset (Fin n)) : Set (Fin n)) = periodicPts f := by
    ext x
    rw [mem_coe, mem_recSet, rec_iff]
  rw [he]
  exact (bijOn_periodicPts (f := f)).injOn

/-- Every function on a nonempty finite set has a recurrent point. -/
lemma exists_rec (hn : 0 < n) (f : Fin n → Fin n) : ∃ x, Rec f x := by
  obtain ⟨i, j, hij, h⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => f^[m] (⟨0, hn⟩ : Fin n))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨f^[i] ⟨0, hn⟩, j - i, by omega, ?_⟩
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact h.symm
  · refine ⟨f^[j] ⟨0, hn⟩, i - j, by omega, ?_⟩
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact h

/-! ### Replacing a function on its recurrent set -/

/-- If `h` agrees with `f` off the recurrent set of `f`, maps that set into itself, and
every point of it is recurrent for `h`, then `h` has the same recurrent set and the
same statistic as `f`. -/
lemma replace {f h : Fin n → Fin n} (hagree : ∀ x, x ∉ recSet f → h x = f x)
    (hmaps : ∀ x, x ∈ recSet f → h x ∈ recSet f) (hrec : ∀ x, x ∈ recSet f → Rec h x) :
    recSet h = recSet f ∧ stat h = stat f := by
  have key : ∀ x, Rec h x ↔ x ∈ recSet f := by
    intro x
    refine ⟨fun hx => ?_, hrec x⟩
    by_contra hxR
    obtain ⟨m, hm, hx⟩ := hx
    have hstay : ∀ j, h^[j] x ∈ recSet f → ∀ i, h^[i + j] x ∈ recSet f := by
      intro j hj i
      induction i with
      | zero => simpa using hj
      | succ i ih =>
        rw [Nat.succ_add, iterate_succ_apply']
        exact hmaps _ ih
    have hout : ∀ j, h^[j] x ∉ recSet f := by
      intro j hj
      have hle : j ≤ m * (j + 1) := by nlinarith
      have hp : h^[m * (j + 1)] x = x :=
        (show IsPeriodicPt h m x from hx).mul_const (j + 1)
      have h1 := hstay j hj (m * (j + 1) - j)
      rw [Nat.sub_add_cancel hle, hp] at h1
      exact hxR h1
    have hit : ∀ j, h^[j] x = f^[j] x := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [iterate_succ_apply', iterate_succ_apply', ← ih]
        exact hagree _ (hout j)
    exact hxR (mem_recSet.2 ⟨m, hm, by rw [← hit]; exact hx⟩)
  have hset : recSet h = recSet f := by
    ext x
    rw [mem_recSet, key]
  refine ⟨hset, ?_⟩
  unfold stat
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [key, key, ← mem_recSet (f := f), ← mem_recSet (f := f)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← hagree x h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [hagree x h1]; exact h2⟩

/-! ### Relabelling -/

/-- Relabel `f` by the permutation `τ`. -/
def conj (τ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) : Fin n → Fin n :=
  fun x => τ (f (τ.symm x))

lemma conj_iterate (τ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) (m : ℕ) (x : Fin n) :
    (conj τ f)^[m] x = τ (f^[m] (τ.symm x)) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply']
    simp [conj]

lemma rec_conj (τ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) (x : Fin n) :
    Rec (conj τ f) x ↔ Rec f (τ.symm x) := by
  simp only [Rec, conj_iterate]
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    have := congrArg τ.symm h
    simpa using this
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [h]
    simp

lemma recSet_conj (τ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    recSet (conj τ f) = (recSet f).map τ.toEmbedding := by
  ext x
  rw [mem_map_equiv, mem_recSet, mem_recSet, rec_conj]

lemma stat_conj (τ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    stat (conj τ f) = stat f := by
  unfold stat
  apply Finset.card_nbij' (fun x => τ.symm x) (fun x => τ x)
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, rec_conj] at hx ⊢
    simpa [conj] using hx
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, rec_conj] at hx ⊢
    simpa [conj] using hx
  · intro x _
    simp
  · intro x _
    simp

lemma conj_symm_conj (τ : Equiv.Perm (Fin n)) (f : Fin n → Fin n) :
    conj τ.symm (conj τ f) = f := by
  funext x
  simp [conj]

/-! ### Splitting off the permutation of the recurrent set -/

/-- Functions with statistic `k` and recurrent set `R`. -/
noncomputable def A (R : Finset (Fin n)) (k : ℕ) : Finset (Fin n → Fin n) :=
  univ.filter fun f => stat f = k ∧ recSet f = R

/-- The permutation of `R` induced by a function whose recurrent set is `R`. -/
noncomputable def permOf (f : Fin n → Fin n) {R : Finset (Fin n)} (hR : recSet f = R) :
    Equiv.Perm R :=
  Equiv.ofBijective (fun x : R => ⟨f x, maps_of hR x.2⟩) (by
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    apply Subtype.ext
    exact injOn_of hR (mem_coe.2 a.2) (mem_coe.2 b.2) (congrArg Subtype.val hab))

/-- `f` with its values on `R` replaced by the identity. -/
def normal (R : Finset (Fin n)) (f : Fin n → Fin n) : Fin n → Fin n :=
  fun x => if x ∈ R then x else f x

/-- The permutation `π` on `R`, glued to `g` off `R`. -/
def glue {R : Finset (Fin n)} (π : Equiv.Perm R) (g : Fin n → Fin n) : Fin n → Fin n :=
  fun x => if hx : x ∈ R then (π ⟨x, hx⟩ : Fin n) else g x

lemma glue_iterate {R : Finset (Fin n)} (π : Equiv.Perm R) (g : Fin n → Fin n) (x : Fin n)
    (hx : x ∈ R) (j : ℕ) : (glue π g)^[j] x = ((π ^ j) ⟨x, hx⟩ : Fin n) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply]
    simp [glue]

lemma fact_dvd_A (R : Finset (Fin n)) (k : ℕ) : (#R).factorial ∣ #(A R k) := by
  let D := (A R k).filter fun g => ∀ x ∈ R, g x = x
  have hcard : #(A R k) = #(univ : Finset (Equiv.Perm R)) * #D := by
    rw [← card_product]
    refine card_bij'
      (fun f hf => (permOf f (mem_filter.1 hf).2.2, normal R f))
      (fun p _ => glue p.1 p.2) ?_ ?_ ?_ ?_
    · intro f hf
      have hfR := (mem_filter.1 hf).2.2
      have hfk := (mem_filter.1 hf).2.1
      have hr := replace (f := f) (h := normal R f)
        (fun x hx => by rw [hfR] at hx; simp [normal, hx])
        (fun x hx => by rw [hfR] at hx ⊢; simp [normal, hx])
        (fun x hx => by rw [hfR] at hx; exact ⟨1, one_pos, by simp [normal, hx]⟩)
      simp only [mem_product, mem_univ, true_and, D, A, mem_filter]
      refine ⟨⟨hr.2.trans hfk, hr.1.trans hfR⟩, fun x hx => by simp [normal, hx]⟩
    · rintro ⟨π, g⟩ hp
      simp only [mem_product, mem_univ, true_and, D, A, mem_filter] at hp
      obtain ⟨⟨hgk, hgR⟩, hgid⟩ := hp
      have hr := replace (f := g) (h := glue π g)
        (fun x hx => by rw [hgR] at hx; simp [glue, hx])
        (fun x hx => by rw [hgR] at hx ⊢; simp [glue, hx])
        (fun x hx => by
          rw [hgR] at hx
          refine ⟨orderOf π, orderOf_pos π, ?_⟩
          rw [glue_iterate π g x hx, pow_orderOf_eq_one]
          rfl)
      simp only [A, mem_filter, mem_univ, true_and]
      exact ⟨hr.2.trans hgk, hr.1.trans hgR⟩
    · intro f hf
      funext x
      by_cases hx : x ∈ R
      · simp [glue, hx, permOf]
      · simp [glue, hx, normal]
    · rintro ⟨π, g⟩ hp
      simp only [mem_product, mem_univ, true_and, D, A, mem_filter] at hp
      obtain ⟨⟨_, _⟩, hgid⟩ := hp
      refine Prod.ext ?_ ?_
      · ext a
        simp [permOf, glue]
      · funext x
        by_cases hx : x ∈ R
        · simp [normal, hx, hgid x hx]
        · simp [normal, glue, hx]
  rw [hcard, card_univ, Fintype.card_perm, Fintype.card_coe]
  exact Dvd.intro _ rfl

/-! ### Counting -/

/-- The functions counted by `T n k` with exactly `r` recurrent points. -/
noncomputable def S (n k r : ℕ) : Finset (Fin n → Fin n) :=
  univ.filter fun f => stat f = k ∧ #(recSet f) = r

lemma T_eq_sum (n k : ℕ) : T n k = ∑ r ∈ range (n + 1), #(S n k r) := by
  unfold T S
  rw [card_eq_sum_card_fiberwise (f := fun f => #(recSet f)) (t := range (n + 1))]
  · refine sum_congr rfl fun r _ => ?_
    rw [filter_filter]
  · intro f _
    simp only [coe_range, Set.mem_Iio]
    have := card_le_univ (recSet f)
    rw [Fintype.card_fin] at this
    omega

lemma S_zero (hn : 0 < n) (k : ℕ) : S n k 0 = ∅ := by
  ext f
  simp only [S, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
  intro _ h0
  obtain ⟨x, hx⟩ := exists_rec hn f
  rw [card_eq_zero] at h0
  have : x ∈ recSet f := mem_recSet.2 hx
  rw [h0] at this
  exact notMem_empty x this

lemma fiber_eq (hn : 0 < n) (k r x : ℕ) (hx : x < n) :
    #((S n k r).filter fun f => (⟨x, hx⟩ : Fin n) ∈ recSet f) =
      #((S n k r).filter fun f => (⟨0, hn⟩ : Fin n) ∈ recSet f) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap ⟨x, hx⟩ ⟨0, hn⟩
  apply Finset.card_nbij' (conj τ) (conj τ.symm)
  · intro f hf
    simp only [S, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
    refine ⟨⟨by rw [stat_conj]; exact hf.1.1, by rw [recSet_conj, card_map]; exact hf.1.2⟩, ?_⟩
    rw [recSet_conj, mem_map_equiv]
    simpa [τ] using hf.2
  · intro f hf
    simp only [S, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
    refine ⟨⟨by rw [stat_conj]; exact hf.1.1, by rw [recSet_conj, card_map]; exact hf.1.2⟩, ?_⟩
    rw [recSet_conj, mem_map_equiv]
    simpa [τ] using hf.2
  · intro f _
    exact conj_symm_conj τ f
  · intro f _
    have := conj_symm_conj τ.symm f
    rwa [Equiv.symm_symm] at this

lemma double_count (hn : 0 < n) (k r : ℕ) :
    #(S n k r) * r = n * #((S n k r).filter fun f => (⟨0, hn⟩ : Fin n) ∈ recSet f) := by
  have h1 : ∑ f ∈ S n k r, #(recSet f) = #(S n k r) * r := by
    rw [sum_const_nat]
    intro f hf
    exact (mem_filter.1 hf).2.2
  have h2 : ∑ f ∈ S n k r, #(recSet f) =
      ∑ x : Fin n, #((S n k r).filter fun f => x ∈ recSet f) := by
    rw [sum_congr rfl fun x _ => card_filter _ _, sum_comm]
    refine sum_congr rfl fun f _ => ?_
    rw [recSet, card_filter]
    simp only [mem_filter, mem_univ, true_and]
  have h3 : ∀ x : Fin n, #((S n k r).filter fun f => x ∈ recSet f) =
      #((S n k r).filter fun f => (⟨0, hn⟩ : Fin n) ∈ recSet f) := by
    intro x
    exact fiber_eq hn k r x.1 x.2
  rw [← h1, h2, sum_congr rfl fun x _ => h3 x, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]

lemma fact_dvd_M (hn : 0 < n) (k r : ℕ) :
    r.factorial ∣ #((S n k r).filter fun f => (⟨0, hn⟩ : Fin n) ∈ recSet f) := by
  rw [card_eq_sum_card_fiberwise (f := recSet) (t := (univ : Finset (Finset (Fin n))))
    (fun _ _ => mem_coe.2 (mem_univ _))]
  refine dvd_sum fun R _ => ?_
  by_cases hR : #R = r ∧ (⟨0, hn⟩ : Fin n) ∈ R
  · have : ((S n k r).filter fun f => (⟨0, hn⟩ : Fin n) ∈ recSet f).filter
        (fun f => recSet f = R) = A R k := by
      ext f
      simp only [S, A, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, _⟩, h4⟩
        exact ⟨h1, h4⟩
      · rintro ⟨h1, h4⟩
        exact ⟨⟨⟨h1, by rw [h4]; exact hR.1⟩, by rw [h4]; exact hR.2⟩, h4⟩
    rw [this, ← hR.1]
    exact fact_dvd_A R k
  · have : ((S n k r).filter fun f => (⟨0, hn⟩ : Fin n) ∈ recSet f).filter
        (fun f => recSet f = R) = ∅ := by
      ext f
      simp only [S, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨⟨⟨_, h2⟩, h3⟩, h4⟩
      rw [h4] at h2 h3
      exact hR ⟨h2, h3⟩
    rw [this, card_empty]
    exact dvd_zero _

lemma S_dvd (hn : 0 < n) (k r : ℕ) (hr : 0 < r) : n ∣ #(S n k r) := by
  obtain ⟨q, hq⟩ := fact_dvd_M hn k r
  have hdc := double_count hn k r
  rw [hq, ← Nat.mul_factorial_pred hr.ne'] at hdc
  refine ⟨(r - 1).factorial * q, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right hr
  rw [hdc]
  ring

/-- **A216971 (Perry's conjecture).** For `n ≥ 1`, every entry of row `n` is divisible
by `n`. -/
theorem A216971_main (n k : ℕ) (hn : 0 < n) : n ∣ T n k := by
  rw [T_eq_sum]
  refine dvd_sum fun r _ => ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [S_zero hn, card_empty]
    exact dvd_zero _
  · exact S_dvd hn k r hr

