import Mathlib

/-!
# Collinear k-subsets of the grid {0, ..., k-1}^n

For k ≥ 2, a set of k points of the grid `Fin n → Fin k` is collinear (Mathlib `Collinear ℝ`,
after embedding the grid in `Fin n → ℝ`) iff it is a combinatorial line: every coordinate is
constant, runs 0..k-1, or runs k-1..0 along it, not all constant. Each line has exactly two
descriptions (one per direction), so the number of collinear k-subsets is ((k+2)^n - k^n)/2.

Main result `OpenProblemsLib.D_CombLine.card_collinear`.
-/

namespace OpenProblemsLib.D_CombLine

open Finset

variable {n k : ℕ}

/-- A line description: per coordinate a constant `inl c`, increasing `inr true`, or decreasing
`inr false`. -/
abbrev Desc (n k : ℕ) := Fin n → (Fin k ⊕ Bool)

/-- The profile of one coordinate along the line. -/
def val : Fin k ⊕ Bool → Fin k → Fin k
  | Sum.inl c => fun _ => c
  | Sum.inr true => id
  | Sum.inr false => Fin.rev

def flipE : Fin k ⊕ Bool → Fin k ⊕ Bool
  | Sum.inl c => Sum.inl c
  | Sum.inr b => Sum.inr (!b)

def flip (f : Desc n k) : Desc n k := fun j => flipE (f j)

/-- Not every coordinate is constant. -/
def NonConst (f : Desc n k) : Prop := ∃ j b, f j = Sum.inr b

instance (f : Desc n k) : Decidable (NonConst f) := by unfold NonConst; infer_instance

/-- The t-th point of the line. -/
def pt (f : Desc n k) (t : Fin k) : Fin n → Fin k := fun j => val (f j) t

def lineSet (f : Desc n k) : Finset (Fin n → Fin k) := univ.image (pt f)

/-- The grid embedded in ℝ^n. -/
def emb (x : Fin n → Fin k) : Fin n → ℝ := fun j => ((x j : ℕ) : ℝ)

theorem emb_injective : Function.Injective (emb : (Fin n → Fin k) → Fin n → ℝ) := by
  intro x y h
  funext j
  have := congrFun h j
  simp only [emb, Nat.cast_inj] at this
  exact Fin.ext this

theorem val_flipE (e : Fin k ⊕ Bool) (t : Fin k) : val (flipE e) t = val e t.rev := by
  rcases e with c | b
  · rfl
  · cases b <;> simp [flipE, val]

theorem pt_flip (f : Desc n k) (t : Fin k) : pt (flip f) t = pt f t.rev := by
  funext j; exact val_flipE _ _

theorem lineSet_flip (f : Desc n k) : lineSet (flip f) = lineSet f := by
  ext x
  simp only [lineSet, mem_image, mem_univ, true_and, pt_flip]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t.rev, rfl⟩
  · rintro ⟨t, rfl⟩; exact ⟨t.rev, by rw [Fin.rev_rev]⟩

theorem flipE_flipE (e : Fin k ⊕ Bool) : flipE (flipE e) = e := by
  rcases e with c | b
  · rfl
  · simp [flipE]

/-- The profiles are pairwise distinct for k ≥ 2. -/
theorem val_injective (hk : 2 ≤ k) : Function.Injective (val : Fin k ⊕ Bool → Fin k → Fin k) := by
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  intro e e' h
  have a0 := congrFun h ⟨0, h0⟩
  have a1 := congrFun h ⟨1, h1⟩
  rcases e with c | b <;> rcases e' with c' | b'
  · simp only [val] at a0; rw [a0]
  · exfalso
    cases b' <;> simp only [val, id, Fin.ext_iff, Fin.val_rev] at a0 a1 <;> omega
  · exfalso
    cases b <;> simp only [val, id, Fin.ext_iff, Fin.val_rev] at a0 a1 <;> omega
  · cases b <;> cases b' <;> simp only [val, id, Fin.ext_iff, Fin.val_rev] at a0 a1 <;>
      first | rfl | omega

theorem pt_injective (f : Desc n k) (hf : NonConst f) : Function.Injective (pt f) := by
  obtain ⟨j, b, hj⟩ := hf
  intro t s h
  have := congrFun h j
  simp only [pt, hj, val] at this
  cases b
  · exact Fin.rev_injective this
  · exact this

theorem card_lineSet (f : Desc n k) (hf : NonConst f) : (lineSet f).card = k := by
  rw [lineSet, card_image_of_injective _ (pt_injective f hf), card_univ, Fintype.card_fin]

/-- Every line is collinear. -/
theorem collinear_lineSet (f : Desc n k) :
    Collinear ℝ (emb '' (lineSet f : Set (Fin n → Fin k))) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  let p₀ : Fin n → ℝ := fun j => match f j with
    | Sum.inl c => ((c : ℕ) : ℝ)
    | Sum.inr true => 0
    | Sum.inr false => ((k : ℝ) - 1)
  let v : Fin n → ℝ := fun j => match f j with
    | Sum.inl _ => 0
    | Sum.inr true => 1
    | Sum.inr false => -1
  refine ⟨p₀, v, ?_⟩
  rintro p ⟨x, hx, rfl⟩
  simp only [lineSet, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx
  obtain ⟨t, rfl⟩ := hx
  refine ⟨((t : ℕ) : ℝ), ?_⟩
  funext j
  simp only [emb, pt, vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, p₀, v]
  rcases hfj : f j with c | b
  · simp [val]
  · cases b
    · simp only [val, Fin.val_rev]
      have : (t : ℕ) + 1 ≤ k := t.isLt
      rw [Nat.cast_sub this]; push_cast; ring
    · simp [val]

/-- Every collinear k-subset of the grid (k ≥ 2) is a line. -/
theorem exists_desc (hk : 2 ≤ k) (S : Finset (Fin n → Fin k)) (hS : S.card = k)
    (hcol : Collinear ℝ (emb '' (S : Set (Fin n → Fin k)))) :
    ∃ f : Desc n k, NonConst f ∧ lineSet f = S := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_image_of_mem emb hx)).1 hcol
  have hr : ∀ p ∈ S, ∃ r : ℝ, emb p = r • v + emb x := fun p hp =>
    hv _ (Set.mem_image_of_mem emb hp)
  /- a coordinate i with v i ≠ 0 -/
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr'⟩ := hr y hy
    apply hxy
    apply emb_injective
    rw [hr']; funext j; simp [hcon j]
  /- the i-th coordinate is injective on S -/
  have hinj : ∀ p ∈ S, ∀ q ∈ S, p i = q i → p = q := by
    intro p hp q hq he
    obtain ⟨r, hrp⟩ := hr p hp
    obtain ⟨s, hsq⟩ := hr q hq
    have e1 := congrFun hrp i
    have e2 := congrFun hsq i
    have hpi : emb p i = emb q i := by simp [emb, he]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have hrs : r = s := by
      have : r * v i = s * v i := by linarith
      exact mul_right_cancel₀ hi this
    apply emb_injective
    rw [hrp, hsq, hrs]
  /- hence it is onto Fin k -/
  have honto : ∀ t : Fin k, ∃ p ∈ S, p i = t := by
    have hc : (S.image (fun p => p i)).card = k := by
      rw [card_image_of_injOn (fun p hp q hq he => hinj p hp q hq he), hS]
    have : S.image (fun p => p i) = univ :=
      eq_univ_of_card _ (by rw [hc, Fintype.card_fin])
    intro t
    have ht : t ∈ S.image (fun p => p i) := by rw [this]; exact mem_univ t
    simpa using ht
  choose q hqS hqi using honto
  /- affine structure: q t = q 0 + t (q 1 - q 0) coordinatewise -/
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  set t0 : Fin k := ⟨0, h0⟩
  set t1 : Fin k := ⟨1, h1⟩
  have haff : ∀ t : Fin k, ∀ j, emb (q t) j = emb (q t0) j + ((t : ℕ) : ℝ) * (emb (q t1) j - emb (q t0) j) := by
    intro t j
    obtain ⟨rt, hrt⟩ := hr _ (hqS t)
    obtain ⟨r0, hr0⟩ := hr _ (hqS t0)
    obtain ⟨r1, hr1⟩ := hr _ (hqS t1)
    have it := congrFun hrt i
    have i0 := congrFun hr0 i
    have i1 := congrFun hr1 i
    have jt := congrFun hrt j
    have j0 := congrFun hr0 j
    have j1 := congrFun hr1 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at it i0 i1 jt j0 j1
    simp only [emb, hqi] at it i0 i1
    have hrt' : rt - r0 = ((t : ℕ) : ℝ) * (r1 - r0) := by
      have e1 : (rt - r0) * v i = ((t : ℕ) : ℝ) := by simp [t0] at i0; linarith
      have e2 : (r1 - r0) * v i = 1 := by simp [t0, t1] at i0 i1; linarith
      have : (rt - r0) * v i = ((t : ℕ) : ℝ) * (r1 - r0) * v i := by rw [e1, mul_assoc, e2, mul_one]
      exact mul_right_cancel₀ hi this
    rw [jt, j0, j1]
    linear_combination v j * hrt'
  /- the step d j = q 1 j - q 0 j is -1, 0 or 1 -/
  have hstep : ∀ j, (q t1 j : ℕ) = (q t0 j : ℕ) ∨
      ((q t0 j : ℕ) = 0 ∧ ∀ t : Fin k, q t j = t) ∨
      ((q t0 j : ℕ) = k - 1 ∧ ∀ t : Fin k, q t j = t.rev) := by
    intro j
    have hlast := haff ⟨k - 1, by omega⟩ j
    simp only [emb] at hlast
    have b0 : (q t0 j : ℕ) < k := (q t0 j).isLt
    have b1 : (q t1 j : ℕ) < k := (q t1 j).isLt
    have bl : (q ⟨k - 1, by omega⟩ j : ℕ) < k := (q ⟨k - 1, by omega⟩ j).isLt
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [hk1] at hlast
    set a := (q t0 j : ℕ)
    set b := (q t1 j : ℕ)
    set c := (q ⟨k - 1, by omega⟩ j : ℕ)
    have hkq : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hcq : (c : ℝ) < k := by exact_mod_cast bl
    have haq : (a : ℝ) < k := by exact_mod_cast b0
    have hbq : (b : ℝ) < k := by exact_mod_cast b1
    have haq1 : (a : ℝ) + 1 ≤ k := by exact_mod_cast b0
    have hcq1 : (c : ℝ) + 1 ≤ k := by exact_mod_cast bl
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    rcases lt_trichotomy b a with hba | hba | hba
    · /- step -1 -/
      have hba' : (b : ℝ) + 1 ≤ a := by exact_mod_cast hba
      have hstep : (b : ℝ) = a - 1 := by
        by_contra hne
        have : (b : ℝ) + 2 ≤ a := by
          have : b + 2 ≤ a := by
            by_contra h'
            have : b + 1 = a := by omega
            apply hne; rw [← this]; push_cast; ring
          exact_mod_cast this
        nlinarith
      have ha : (a : ℝ) = k - 1 := by
        rw [hstep] at hlast
        have : (c : ℝ) = a - (k - 1) := by rw [hlast]; ring
        linarith
      refine Or.inr (Or.inr ⟨by exact_mod_cast (show (a : ℝ) = ((k - 1 : ℕ) : ℝ) by rw [hk1]; exact ha), fun t => ?_⟩)
      have := haff t j
      simp only [emb] at this
      change ((q t j : ℕ) : ℝ) = (a : ℝ) + ((t : ℕ) : ℝ) * ((b : ℝ) - a) at this
      rw [hstep, ha] at this
      apply Fin.ext
      rw [Fin.val_rev]
      have ht : (t : ℕ) + 1 ≤ k := t.isLt
      have : ((q t j : ℕ) : ℝ) = ((k - (t + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_sub ht]; push_cast; linarith
      exact_mod_cast this
    · exact Or.inl hba
    · /- step +1 -/
      have hstep : (b : ℝ) = a + 1 := by
        by_contra hne
        have : (a : ℝ) + 2 ≤ b := by
          have : a + 2 ≤ b := by
            by_contra h'
            have : a + 1 = b := by omega
            apply hne; rw [← this]; push_cast; ring
          exact_mod_cast this
        nlinarith
      have ha : (a : ℝ) = 0 := by
        rw [hstep] at hlast
        have : (c : ℝ) = a + (k - 1) := by rw [hlast]; ring
        linarith
      refine Or.inr (Or.inl ⟨by exact_mod_cast ha, fun t => ?_⟩)
      have := haff t j
      simp only [emb] at this
      change ((q t j : ℕ) : ℝ) = (a : ℝ) + ((t : ℕ) : ℝ) * ((b : ℝ) - a) at this
      rw [hstep, ha] at this
      apply Fin.ext
      exact_mod_cast (show ((q t j : ℕ) : ℝ) = ((t : ℕ) : ℝ) by linarith)
  /- build the description -/
  have hcases : ∀ j, ∃ e : Fin k ⊕ Bool, ∀ t, q t j = val e t := by
    intro j
    rcases hstep j with h | ⟨_, h⟩ | ⟨_, h⟩
    · refine ⟨Sum.inl (q t0 j), fun t => ?_⟩
      have := haff t j
      simp only [emb] at this
      have hc : ((q t1 j : ℕ) : ℝ) = ((q t0 j : ℕ) : ℝ) := by exact_mod_cast h
      rw [hc, sub_self, mul_zero, add_zero] at this
      exact Fin.ext (by exact_mod_cast this)
    · exact ⟨Sum.inr true, fun t => h t⟩
    · exact ⟨Sum.inr false, fun t => h t⟩
  choose f hf using hcases
  have hpt : ∀ t, pt f t = q t := fun t => by funext j; exact (hf j t).symm
  refine ⟨f, ?_, ?_⟩
  · /- coordinate i runs through all values, so it is not constant -/
    rcases hfi : f i with c | b
    · exfalso
      have e0 := hf i t0
      have e1 := hf i t1
      rw [hfi, hqi] at e0 e1
      simp only [val] at e0 e1
      have := e0.trans e1.symm
      simp [t0, t1, Fin.ext_iff] at this
    · exact ⟨i, b, hfi⟩
  · ext p
    simp only [lineSet, mem_image, mem_univ, true_and, hpt]
    constructor
    · rintro ⟨t, rfl⟩; exact hqS t
    · intro hp
      exact ⟨p i, hinj _ (hqS _) _ hp (hqi _)⟩

/-- Two descriptions of the same line agree or are flips of each other. -/
theorem eq_or_flip (hk : 2 ≤ k) (f g : Desc n k) (hf : NonConst f)
    (h : lineSet g = lineSet f) : g = f ∨ g = flip f := by
  obtain ⟨i, b, hfi⟩ := hf
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  /- each point of g's line is a point of f's line -/
  have hmem : ∀ s, ∃ t, pt g s = pt f t := by
    intro s
    have : pt g s ∈ lineSet f := by rw [← h]; exact mem_image_of_mem _ (mem_univ s)
    simpa [lineSet, eq_comm] using this
  choose ψ hψ using hmem
  /- g i is not constant: f's line takes two values at i -/
  obtain ⟨b', hgi⟩ : ∃ b', g i = Sum.inr b' := by
    rcases hgi : g i with c | b'
    · exfalso
      have m0 : pt f ⟨0, h0⟩ ∈ lineSet g := by rw [h]; exact mem_image_of_mem _ (mem_univ _)
      have m1 : pt f ⟨1, h1⟩ ∈ lineSet g := by rw [h]; exact mem_image_of_mem _ (mem_univ _)
      simp only [lineSet, mem_image, mem_univ, true_and] at m0 m1
      obtain ⟨s0, hs0⟩ := m0
      obtain ⟨s1, hs1⟩ := m1
      have a0 := congrFun hs0 i
      have a1 := congrFun hs1 i
      simp only [pt, hgi, hfi, val] at a0 a1
      cases b <;> simp only [id, Fin.ext_iff, Fin.val_rev] at a0 a1 <;> omega
    · exact ⟨b', rfl⟩
  /- ψ is id or rev, according to b = b' -/
  have hψ' : ∀ s, ψ s = if b = b' then s else s.rev := by
    intro s
    have := congrFun (hψ s) i
    simp only [pt, hgi, hfi] at this
    cases b <;> cases b'
    · simp only [val] at this
      simp only [ite_true]; exact Fin.rev_injective this.symm
    · simp only [val, id] at this
      simp only [Bool.false_eq_true, ite_false]; conv_rhs => rw [this, Fin.rev_rev]
    · simp only [val, id] at this
      simp only [Bool.true_eq_false, ite_false]; exact this.symm
    · simp only [val, id] at this
      simp only [ite_true]; exact this.symm
  by_cases hbb : b = b'
  · left
    funext j
    apply val_injective hk
    funext s
    have := congrFun (hψ s) j
    simp only [pt, hψ', hbb, ite_true] at this
    exact this
  · right
    funext j
    apply val_injective hk
    funext s
    have := congrFun (hψ s) j
    simp only [pt, hψ', hbb, ite_false] at this
    rw [flip, val_flipE, this]

theorem flip_ne (f : Desc n k) (hf : NonConst f) : flip f ≠ f := by
  obtain ⟨j, b, hj⟩ := hf
  intro h
  have := congrFun h j
  simp only [flip, hj, flipE, Sum.inr.injEq] at this
  cases b <;> simp at this

theorem nonConst_flip (f : Desc n k) (hf : NonConst f) : NonConst (flip f) := by
  obtain ⟨j, b, hj⟩ := hf
  exact ⟨j, !b, by simp [flip, hj, flipE]⟩

/-- The number of descriptions that are not all constant. -/
theorem card_nonConst :
    (univ.filter (fun f : Desc n k => NonConst f)).card = (k + 2) ^ n - k ^ n := by
  classical
  have hc : (univ.filter (fun f : Desc n k => ¬ NonConst f)) =
      Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin k)).map Function.Embedding.inl) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_map,
      Function.Embedding.inl_apply, NonConst, not_exists]
    refine forall_congr' fun j => ?_
    rcases f j with c | b
    · simp
    · simp
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Desc n k)))
    (fun f => NonConst f)
  rw [hc, Fintype.card_piFinset, card_univ] at htot
  simp only [card_map, card_univ, Fintype.card_fin, prod_const, Fintype.card_fun,
    Fintype.card_sum, Fintype.card_bool] at htot
  omega

open scoped Classical in
/-- The collinear k-subsets of the grid {0, ..., k-1}^n (k ≥ 2). -/
noncomputable def collinearSets (n k : ℕ) : Finset (Finset (Fin n → Fin k)) :=
  (univ.powersetCard k).filter (fun S => Collinear ℝ (emb '' (S : Set (Fin n → Fin k))))

/-- Twice the number of collinear k-subsets is (k+2)^n - k^n. -/
theorem two_mul_card_collinear (hk : 2 ≤ k) :
    2 * (collinearSets n k).card = (k + 2) ^ n - k ^ n := by
  classical
  rw [← card_nonConst]
  have hmaps : ∀ f ∈ univ.filter (fun f : Desc n k => NonConst f),
      lineSet f ∈ collinearSets n k := by
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    simp only [collinearSets, mem_filter, mem_powersetCard]
    exact ⟨⟨subset_univ _, card_lineSet f hf⟩, collinear_lineSet f⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ S ∈ collinearSets n k,
      ((univ.filter (fun f : Desc n k => NonConst f)).filter (fun f => lineSet f = S)).card = 2 := by
    intro S hS
    simp only [collinearSets, mem_filter, mem_powersetCard] at hS
    obtain ⟨f0, hf0, rfl⟩ := exists_desc hk S hS.1.2 hS.2
    have : (univ.filter (fun f : Desc n k => NonConst f)).filter (fun f => lineSet f = lineSet f0) =
        {f0, flip f0} := by
      ext g
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hg, he⟩; exact eq_or_flip hk f0 g hf0 he
      · rintro (rfl | rfl)
        · exact ⟨hf0, rfl⟩
        · exact ⟨nonConst_flip _ hf0, lineSet_flip _⟩
    rw [this, card_pair (flip_ne f0 hf0).symm]
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul, mul_comm]

/-- The m-th binomial transform of 0, 1, 0, 1, ...: Σ_j C(n, j) m^(n-j) [j odd]. -/
def binomTransform (m n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), n.choose j * m ^ (n - j) * (j % 2)

theorem two_mul_binomTransform (m n : ℕ) (hm : 1 ≤ m) :
    2 * binomTransform m n = (m + 1) ^ n - (m - 1) ^ n := by
  have h1 : ((m + 1 : ℕ) : ℤ) ^ n = ∑ j ∈ range (n + 1), (m : ℤ) ^ j * 1 ^ (n - j) * n.choose j := by
    rw [Nat.cast_add, Nat.cast_one, add_pow]
  have h2 : ((m - 1 : ℕ) : ℤ) ^ n =
      ∑ j ∈ range (n + 1), (m : ℤ) ^ (n - j) * (-1) ^ j * n.choose j := by
    rw [Nat.cast_sub hm, Nat.cast_one, sub_eq_add_neg, add_comm, add_pow]
    refine sum_congr rfl fun j hj => ?_
    ring
  have h1' : ((m + 1 : ℕ) : ℤ) ^ n = ∑ j ∈ range (n + 1), (m : ℤ) ^ (n - j) * n.choose j := by
    rw [h1, ← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj)
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hj', Nat.choose_symm hj']
    ring
  have hle : (m - 1) ^ n ≤ (m + 1) ^ n := Nat.pow_le_pow_left (by omega) n
  have key : ((2 * binomTransform m n : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) ^ n - ((m - 1 : ℕ) : ℤ) ^ n := by
    rw [h1', h2, ← sum_sub_distrib, binomTransform]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rcases Nat.even_or_odd j with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · have : ((r + r : ℕ) : ℤ) % 2 = 0 := by push_cast; omega
      rw [this, show r + r = 2 * r by ring, pow_mul]; simp
    · have : ((2 * r + 1 : ℕ) : ℤ) % 2 = 1 := by push_cast; omega
      rw [this, pow_succ, pow_mul]; simp; ring
  have : ((2 * binomTransform m n : ℕ) : ℤ) = (((m + 1) ^ n - (m - 1) ^ n : ℕ) : ℤ) := by
    rw [key, Nat.cast_sub hle]; push_cast; ring
  exact_mod_cast this

/-- Main result: for k ≥ 2 the number of collinear k-subsets of {0..k-1}^n equals the
(k+1)-th binomial transform of 0, 1, 0, 1, ..., and ((k+2)^n - k^n)/2. -/
theorem card_collinear (hk : 2 ≤ k) :
    (collinearSets n k).card = binomTransform (k + 1) n ∧
    (collinearSets n k).card = ((k + 2) ^ n - k ^ n) / 2 := by
  have h1 := two_mul_card_collinear (n := n) hk
  have h2 := two_mul_binomTransform (k + 1) n (by omega)
  simp only [Nat.add_sub_cancel, show k + 1 + 1 = k + 2 by ring] at h2
  omega

end OpenProblemsLib.D_CombLine
