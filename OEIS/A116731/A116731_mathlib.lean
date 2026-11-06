import Mathlib

open Finset

namespace A116731

/-- One left-to-right bubble pass: returns the new list and the number of swaps. -/
def pass : List ℕ → List ℕ × ℕ
  | x :: y :: t =>
    if y < x then (y :: (pass (x :: t)).1, (pass (x :: t)).2 + 1)
    else (x :: (pass (y :: t)).1, (pass (y :: t)).2)
  | l => (l, 0)

/-- Bubble sort with a pass budget: repeat passes until a pass makes no swap.
Returns (flips, iterations): total swaps and number of passes that swapped. -/
def bubbleAux : ℕ → List ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | fuel + 1, l =>
    if (pass l).2 = 0 then (0, 0)
    else ((bubbleAux fuel (pass l).1).1 + (pass l).2, (bubbleAux fuel (pass l).1).2 + 1)

def bubble (l : List ℕ) : ℕ × ℕ := bubbleAux l.length l

/-- Number of elements greater than `v` before (the first) `v` in the list. -/
def cgb (v : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: t => if x = v then 0 else (if v < x then 1 else 0) + cgb v t

lemma pass_perm (l : List ℕ) : (pass l).1.Perm l := by
  induction l using pass.induct with
  | case1 x y t h ih =>
    simp only [pass, h, ↓reduceIte]
    exact ((ih.cons y).trans (List.Perm.swap x y t))
  | case2 x y t h ih =>
    simp only [pass, h, ↓reduceIte]
    exact ih.cons x
  | case3 l hl =>
    rw [pass.eq_def]; split
    · exact absurd rfl (hl _ _ _)
    · rfl

lemma pass_short (l : List ℕ) (hl : ∀ x y t, l ≠ x :: y :: t) : pass l = (l, 0) := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp [pass]
  · simp [pass]
  · exact absurd rfl (hl a b t)

lemma pass_cgb (l : List ℕ) (hnd : l.Nodup) (v : ℕ) (hv : v ∈ l) :
    cgb v (pass l).1 = cgb v l - 1 := by
  induction l using pass.induct with
  | case1 x y t h ih =>
    simp only [pass, h, ↓reduceIte]
    have hnd' : (x :: t).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnd ⊢
      exact ⟨hnd.1.2, hnd.2.2⟩
    by_cases hvy : y = v
    · subst hvy
      have hxy : x ≠ y := by omega
      simp [cgb, hxy, h]
    · have hv' : v ∈ x :: t := by
        simp only [List.mem_cons] at hv ⊢
        rcases hv with hv | hv | hv
        · exact Or.inl hv
        · exact absurd hv.symm hvy
        · exact Or.inr hv
      simp only [cgb, hvy, ↓reduceIte]
      rw [ih hnd' hv']
      simp only [cgb]
      split_ifs <;> omega
  | case2 x y t h ih =>
    simp only [pass, h, ↓reduceIte]
    have hxy : x ≠ y := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
      exact hnd.1.1
    have hnd' : (y :: t).Nodup := (List.nodup_cons.1 hnd).2
    by_cases hvx : x = v
    · subst hvx
      simp [cgb]
    · have hv' : v ∈ y :: t := by
        simp only [List.mem_cons] at hv ⊢
        rcases hv with hv | hv
        · exact absurd hv.symm hvx
        · exact hv
      simp only [cgb, hvx, ↓reduceIte]
      rw [ih hnd' hv']
      simp only [cgb]
      split_ifs <;> omega
  | case3 l hl =>
    rw [pass_short l hl]
    rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hv
    · simp only [List.mem_singleton] at hv
      subst hv
      simp [cgb]
    · exact absurd rfl (hl a b t)

lemma pass_swaps (l : List ℕ) (hnd : l.Nodup) :
    (pass l).2 = l.countP (fun v => 0 < cgb v l) := by
  induction l using pass.induct with
  | case1 x y t h ih =>
    simp only [pass, h, ↓reduceIte]
    have hnd2 := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd2
    have hnd' : (x :: t).Nodup := List.nodup_cons.2 ⟨hnd2.1.2, hnd2.2.2⟩
    rw [ih hnd']
    have hxy : x ≠ y := hnd2.1.1
    have key : t.countP (fun v => 0 < cgb v (x :: t)) =
        t.countP (fun v => 0 < cgb v (x :: y :: t)) := by
      apply List.countP_congr
      intro v hv
      have hvx : x ≠ v := fun e => hnd2.1.2 (e ▸ hv)
      have hvy : y ≠ v := fun e => hnd2.2.1 (e ▸ hv)
      simp only [cgb, hvx, hvy, ↓reduceIte, decide_eq_true_eq]
      split_ifs <;> omega
    simp only [List.countP_cons]
    rw [key]
    simp [cgb, hxy, h]
  | case2 x y t h ih =>
    simp only [pass, h, ↓reduceIte]
    have hnd2 := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd2
    have hnd' : (y :: t).Nodup := List.nodup_cons.2 ⟨hnd2.2.1, hnd2.2.2⟩
    rw [ih hnd']
    have hxy : x ≠ y := hnd2.1.1
    have key : t.countP (fun v => 0 < cgb v (y :: t)) =
        t.countP (fun v => 0 < cgb v (x :: y :: t)) := by
      apply List.countP_congr
      intro v hv
      have hvx : x ≠ v := fun e => hnd2.1.2 (e ▸ hv)
      have hvy : y ≠ v := fun e => hnd2.2.1 (e ▸ hv)
      simp only [cgb, hvx, hvy, ↓reduceIte, decide_eq_true_eq]
      split_ifs <;> omega
    simp only [List.countP_cons]
    rw [key]
    simp [cgb, hxy, h]
  | case3 l hl =>
    rw [pass_short l hl]
    rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp
    · simp [cgb]
    · exact absurd rfl (hl a b t)

/-- Maximum of a list of naturals (0 for the empty list). -/
def mx (xs : List ℕ) : ℕ := xs.foldr max 0

lemma le_mx {xs : List ℕ} {x : ℕ} (h : x ∈ xs) : x ≤ mx xs := by
  induction xs with
  | nil => simp at h
  | cons a t ih =>
    simp only [mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma mx_le {xs : List ℕ} {m : ℕ} (h : ∀ x ∈ xs, x ≤ m) : mx xs ≤ m := by
  induction xs with
  | nil => simp [mx]
  | cons a t ih =>
    simp only [mx, List.foldr_cons] at ih ⊢
    exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

lemma mx_mem (xs : List ℕ) : mx xs = 0 ∨ mx xs ∈ xs := by
  induction xs with
  | nil => simp [mx]
  | cons a t ih =>
    simp only [mx, List.foldr_cons] at ih ⊢
    rcases le_total a (t.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with ih | ih
      · exact Or.inl ih
      · exact Or.inr (List.mem_cons_of_mem _ ih)
    · rw [max_eq_left h]; exact Or.inr (by simp)

lemma sum_sub_one (xs : List ℕ) :
    xs.sum = (xs.map (· - 1)).sum + xs.countP (fun x => 0 < x) := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons, List.countP_cons, ih, decide_eq_true_eq]
    split_ifs <;> omega

/-- Total and maximum of the left-greater counts. -/
def S (l : List ℕ) : ℕ := (l.map (fun v => cgb v l)).sum
def B (l : List ℕ) : ℕ := mx (l.map (fun v => cgb v l))

theorem bubbleAux_eq (fuel : ℕ) : ∀ l : List ℕ, l.Nodup → B l < fuel →
    bubbleAux fuel l = (S l, B l) := by
  induction fuel with
  | zero => intro l _ h; omega
  | succ fuel ih =>
    intro l hnd hB
    have hsw := pass_swaps l hnd
    have hp := pass_perm l
    have hc : ∀ v ∈ (pass l).1, cgb v (pass l).1 = cgb v l - 1 :=
      fun v hv => pass_cgb l hnd v (hp.subset hv)
    have hS : S (pass l).1 = (l.map (fun v => cgb v l - 1)).sum := by
      unfold S
      rw [List.map_congr_left hc]
      exact (hp.map _).sum_eq
    have hSl : S l = (l.map (fun v => cgb v l - 1)).sum + l.countP (fun v => 0 < cgb v l) := by
      unfold S
      rw [sum_sub_one, List.map_map, List.countP_map]
      rfl
    simp only [bubbleAux]
    split_ifs with h0
    · rw [hsw, List.countP_eq_zero] at h0
      have hz : ∀ v ∈ l, cgb v l = 0 := fun v hv => by
        have := h0 v hv; simp at this; omega
      have h1 : S l = 0 := by
        unfold S; apply List.sum_eq_zero
        intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx; exact hz v hv
      have h2 : B l = 0 := by
        apply Nat.eq_zero_of_le_zero; apply mx_le
        intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx; exact (hz v hv).le
      rw [h1, h2]
    · have hpos : 1 ≤ B l := by
        rw [hsw] at h0
        obtain ⟨v, hv, hv0⟩ := List.countP_pos_iff.1 (Nat.pos_of_ne_zero h0)
        simp at hv0
        exact le_trans hv0 (le_mx (List.mem_map_of_mem hv))
      have hBr : B (pass l).1 = B l - 1 := by
        apply le_antisymm
        · apply mx_le
          intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
          rw [hc v hv]
          have := le_mx (List.mem_map_of_mem (f := fun v => cgb v l) (hp.subset hv))
          unfold B; omega
        · rcases mx_mem (l.map (fun v => cgb v l)) with h | h
          · change B l = 0 at h; omega
          · obtain ⟨v, hv, hvB⟩ := List.mem_map.1 h
            have hv' : v ∈ (pass l).1 := hp.symm.subset hv
            have := le_mx (List.mem_map_of_mem (f := fun v => cgb v (pass l).1) hv')
            rw [hc v hv'] at this
            change cgb v l = B l at hvB
            unfold B at *; omega
      rw [ih (pass l).1 (hp.nodup_iff.2 hnd) (by omega), hS, hSl, hBr, ← hsw]
      ext
      · simp
      · simp; omega

theorem bubble_eq (l : List ℕ) (hnd : l.Nodup) (hB : B l < l.length) :
    bubble l = (S l, B l) := bubbleAux_eq _ l hnd hB

/-! ## The set of pairs over all permutations of 1..n -/

/-- Largest possible total of left-greater counts when all counts are ≤ b. -/
def M (n b : ℕ) : ℕ := ((List.range' 1 n).map (fun v => min b (n - v))).sum

/-- The pairs (flips, iterations). -/
def P (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).biUnion (fun b => (Finset.Icc b (M n b)).image (fun i => (i, b)))

lemma countP_range' (n v : ℕ) : (List.range' 1 n).countP (fun x => v < x) = n - v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_concat, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
    split_ifs <;> omega

lemma cgb_le_countP (v : ℕ) (l : List ℕ) : cgb v l ≤ l.countP (fun x => v < x) := by
  induction l with
  | nil => simp [cgb]
  | cons x t ih =>
    simp only [cgb, List.countP_cons, decide_eq_true_eq]
    split_ifs <;> omega

lemma cgb_le (n : ℕ) (l : List ℕ) (hl : l.Perm (List.range' 1 n)) (v : ℕ) :
    cgb v l ≤ n - v := by
  have := cgb_le_countP v l
  rw [hl.countP_eq, countP_range'] at this
  exact this

theorem bubble_mem_P (n : ℕ) (l : List ℕ) (hl : l.Perm (List.range' 1 n)) (hn : 1 ≤ n) :
    bubble l ∈ P n := by
  have hnd : l.Nodup := hl.nodup_iff.2 (List.nodup_range')
  have hlen : l.length = n := by rw [hl.length_eq, List.length_range']
  have hmem : ∀ v ∈ l, 1 ≤ v := fun v hv => by
    have := hl.subset hv; rw [List.mem_range'_1] at this; omega
  have hBn : B l ≤ n - 1 := by
    apply mx_le; intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    have := cgb_le n l hl v; have := hmem v hv; omega
  rw [bubble_eq l hnd (by omega)]
  simp only [P, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Icc,
    Prod.mk.injEq]
  refine ⟨B l, by omega, S l, ⟨?_, ?_⟩, rfl, rfl⟩
  · rcases mx_mem (l.map (fun v => cgb v l)) with h | h
    · change B l = 0 at h; omega
    · exact List.le_sum_of_mem h
  · unfold S M
    rw [← (hl.map (fun v => min (B l) (n - v))).sum_eq]
    apply List.sum_le_sum
    intro v hv
    exact le_min (le_mx (List.mem_map_of_mem hv)) (cgb_le n l hl v)

/-- Insert `v` after the first `k` entries. -/
def ins : ℕ → ℕ → List ℕ → List ℕ
  | 0, v, L => v :: L
  | _ + 1, v, [] => [v]
  | k + 1, v, x :: L => x :: ins k v L

lemma ins_perm (k v : ℕ) (L : List ℕ) : (ins k v L).Perm (v :: L) := by
  induction k generalizing L with
  | zero => simp [ins]
  | succ k ih =>
    cases L with
    | nil => simp [ins]
    | cons x L => exact ((ih L).cons x).trans (List.Perm.swap v x L)

lemma cgb_ins_self (k v : ℕ) (L : List ℕ) (h : ∀ x ∈ L, v < x) :
    cgb v (ins k v L) = min k L.length := by
  induction k generalizing L with
  | zero => simp [ins, cgb]
  | succ k ih =>
    cases L with
    | nil => simp [ins, cgb]
    | cons x L =>
      have hx : v < x := h x (by simp)
      simp only [ins, cgb, List.length_cons]
      rw [ih L (fun y hy => h y (by simp [hy]))]
      have : x ≠ v := by omega
      simp only [this, ↓reduceIte, hx]
      omega

lemma cgb_ins_other (k v w : ℕ) (L : List ℕ) (h : v < w) :
    cgb w (ins k v L) = cgb w L := by
  induction k generalizing L with
  | zero =>
    have : v ≠ w := by omega
    have : ¬ w < v := by omega
    simp [ins, cgb, *]
  | succ k ih =>
    cases L with
    | nil =>
      have : v ≠ w := by omega
      have : ¬ w < v := by omega
      simp [ins, cgb, *]
    | cons x L => simp only [ins, cgb, ih L]

/-- Insert n-m at position e(n-m) into the list of the values n-m+1..n. -/
def build (n : ℕ) (e : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 => ins (e (n - m)) (n - m) (build n e m)

lemma build_perm (n : ℕ) (e : ℕ → ℕ) (m : ℕ) (hm : m ≤ n) :
    (build n e m).Perm (List.range' (n - m + 1) m) := by
  induction m with
  | zero => simp [build]
  | succ m ih =>
    simp only [build]
    refine (ins_perm _ _ _).trans ?_
    rw [List.range'_succ, show n - (m + 1) + 1 = n - m by omega]
    exact (ih (by omega)).cons _

lemma cgb_build (n : ℕ) (e : ℕ → ℕ) (he : ∀ v, e v ≤ n - v) (m : ℕ) (hm : m ≤ n) :
    ∀ v ∈ build n e m, cgb v (build n e m) = e v := by
  induction m with
  | zero => simp [build]
  | succ m ih =>
    intro v hv
    have hp := build_perm n e m (by omega)
    have hgt : ∀ x ∈ build n e m, n - m < x := fun x hx => by
      have := hp.subset hx; rw [List.mem_range'_1] at this; omega
    simp only [build] at hv ⊢
    rcases List.mem_cons.1 ((ins_perm _ _ _).subset hv) with h | h
    · subst h
      rw [cgb_ins_self _ _ _ hgt, hp.length_eq, List.length_range']
      have := he (n - m); omega
    · rw [cgb_ins_other _ _ _ _ (hgt v h)]
      exact ih (by omega) v h

/-- Prefix sums of the caps min b (n - v). -/
def C (n b : ℕ) : ℕ → ℕ
  | 0 => 0
  | v + 1 => C n b v + min b (n - (v + 1))

/-- The greedy table with total i. -/
def tab (n b i v : ℕ) : ℕ := min i (C n b v) - min i (C n b (v - 1))

lemma tab_le (n b i v : ℕ) : tab n b i v ≤ min b (n - v) := by
  unfold tab
  cases v with
  | zero => simp [C]
  | succ v => simp only [C, Nat.add_sub_cancel]; omega

lemma sum_tab (n b i m : ℕ) :
    ((List.range' 1 m).map (tab n b i)).sum = min i (C n b m) := by
  induction m with
  | zero => simp [C]
  | succ m ih =>
    rw [List.range'_concat, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tab,
      show 1 + 1 * m = m + 1 by omega, Nat.add_sub_cancel, C]
    omega

lemma C_eq (n b m : ℕ) : C n b m = ((List.range' 1 m).map (fun v => min b (n - v))).sum := by
  induction m with
  | zero => simp [C]
  | succ m ih =>
    rw [List.range'_concat, List.map_append, List.sum_append, ← ih]
    simp [C, show 1 + m = m + 1 by omega]

theorem P_sub (n : ℕ) (hn : 1 ≤ n) (p : ℕ × ℕ) (hp : p ∈ P n) :
    ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ bubble l = p := by
  obtain ⟨i, b⟩ := p
  simp only [P, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Icc,
    Prod.mk.injEq] at hp
  obtain ⟨b', hb, i', ⟨hbi, hiM⟩, rfl, rfl⟩ := hp
  set e := tab n b' i' with he_def
  have he : ∀ v, e v ≤ n - v := fun v => le_trans (tab_le n b' i' v) (min_le_right _ _)
  set l := build n e n with hl_def
  have hperm : l.Perm (List.range' 1 n) := by
    have := build_perm n e n le_rfl; rwa [Nat.sub_self, zero_add] at this
  have hnd : l.Nodup := hperm.nodup_iff.2 List.nodup_range'
  have hc : ∀ v ∈ l, cgb v l = e v := cgb_build n e he n le_rfl
  have hmem : ∀ v ∈ l, 1 ≤ v := fun v hv => by
    have := hperm.subset hv; rw [List.mem_range'_1] at this; omega
  have he1 : e 1 = b' := by
    rw [he_def]; simp [tab, C]; omega
  have h1 : 1 ∈ l := hperm.symm.subset (by rw [List.mem_range'_1]; omega)
  have hB : B l = b' := by
    apply le_antisymm
    · apply mx_le; intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      rw [hc v hv]; exact le_trans (tab_le n b' i' v) (min_le_left _ _)
    · have := le_mx (List.mem_map_of_mem (f := fun v => cgb v l) h1)
      rw [hc 1 h1, he1] at this; unfold B; exact this
  have hS : S l = i' := by
    unfold S
    rw [List.map_congr_left hc, (hperm.map e).sum_eq, he_def, sum_tab, C_eq]
    unfold M at hiM; omega
  refine ⟨l, hperm, ?_⟩
  rw [bubble_eq l hnd (by rw [hB, hperm.length_eq, List.length_range']; omega), hS, hB]

theorem pairs_eq_P (n : ℕ) (hn : 1 ≤ n) :
    ((List.range' 1 n).permutations.map bubble).toFinset = P n := by
  ext p
  simp only [List.mem_toFinset, List.mem_map, List.mem_permutations]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact bubble_mem_P n l hl hn
  · intro hp; exact P_sub n hn p hp

/-! ## Counting the pairs -/

lemma list_sum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma M_eq (n b : ℕ) : M n b = ∑ j ∈ Finset.range n, min b j := by
  unfold M
  rw [List.range'_eq_map_range, List.map_map, list_sum_range]
  rw [← Finset.sum_range_reflect (fun j => min b j) n]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.comp, Finset.mem_range] at hj ⊢
  congr 1; omega

lemma M_closed (n b : ℕ) (h : b ≤ n) : 2 * M n b + b * (b + 1) = 2 * b * n := by
  rw [M_eq]
  induction n, h using Nat.le_induction with
  | base =>
    have hs : ∑ j ∈ Finset.range b, min b j = ∑ j ∈ Finset.range b, j :=
      Finset.sum_congr rfl (fun j hj => min_eq_right (Finset.mem_range.1 hj).le)
    rw [hs]
    have := Finset.sum_range_id_mul_two b
    rcases b with _ | c
    · simp
    · simp only [Nat.add_sub_cancel] at this
      nlinarith [this]
  | succ n hbn ih =>
    rw [Finset.sum_range_succ, min_eq_left hbn]
    nlinarith [ih]

lemma card_P (n : ℕ) : (P n).card = ∑ b ∈ Finset.range n, (M n b + 1 - b) := by
  unfold P
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro b _
    rw [Finset.card_image_of_injective _ (fun a c h => by simpa using congrArg Prod.fst h),
      Nat.card_Icc]
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_image] at hp hq
    obtain ⟨_, _, rfl⟩ := hp
    obtain ⟨_, _, h⟩ := hq
    exact hxy (congrArg Prod.snd h).symm

lemma sum_poly (N m : ℕ) :
    6 * ∑ b ∈ Finset.range m, ((2 * b * N - b ^ 2 - 3 * b + 2 : ℤ)) =
      6 * N * m * (m - 1) - m * (m - 1) * (2 * m - 1) - 9 * m * (m - 1) + 12 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem card_P_closed (n : ℕ) : (P n).card = (n ^ 3 + 5 * n - 3 * n ^ 2) / 3 := by
  have key : ∀ b ∈ Finset.range n,
      (((M n b + 1 - b : ℕ)) : ℤ) * 2 = 2 * b * n - b ^ 2 - 3 * b + 2 := by
    intro b hb
    have hbn := Finset.mem_range.1 hb
    have hM := M_closed n b hbn.le
    have hle : b ≤ M n b + 1 := by nlinarith
    rw [Nat.cast_sub hle]
    push_cast
    have hMz : (2 * M n b + b * (b + 1) : ℤ) = 2 * b * n := by exact_mod_cast hM
    linarith
  have h2 : ((P n).card : ℤ) * 2 = ∑ b ∈ Finset.range n, ((2 * b * n - b ^ 2 - 3 * b + 2 : ℤ)) := by
    rw [card_P, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl key
  have h3 := sum_poly n n
  have h4 : (3 * (P n).card + 3 * n ^ 2 : ℤ) = n ^ 3 + 5 * n := by nlinarith
  have h5 : 3 * (P n).card + 3 * n ^ 2 = n ^ 3 + 5 * n := by exact_mod_cast h4
  generalize n ^ 3 = a at h5 ⊢
  generalize n ^ 2 = c at h5 ⊢
  omega

/-- Main theorem: over all permutations of 1..n, bubble sort produces exactly
(n^3 - 3n^2 + 5n)/3 distinct pairs (flips, iterations). -/
theorem A116731_conjecture (n : ℕ) (hn : 1 ≤ n) :
    ((List.range' 1 n).permutations.map bubble).toFinset.card = (n ^ 3 + 5 * n - 3 * n ^ 2) / 3 := by
  rw [pairs_eq_P n hn, card_P_closed n]
