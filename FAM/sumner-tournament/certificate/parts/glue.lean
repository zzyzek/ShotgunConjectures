/-! ## Soundness of the checkers -/

theorem allLT_iff (n : Nat) (p : Nat → Bool) : allLT n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    show (allLT n p && p n) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · exact h ▸ h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem allLT_mul (C len : Nat) (p : Nat → Bool)
    (h : ∀ c < C, allLT len (fun j => p (c * len + j)) = true) : allLT (C * len) p = true := by
  rw [allLT_iff]
  intro i hi
  have hlen : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | h0
    · subst h0
      simp at hi
    · exact h0
  have hc : i / len < C := by
    rw [Nat.div_lt_iff_lt_mul hlen]
    exact hi
  have := (allLT_iff _ _).1 (h (i / len) hc) (i % len) (Nat.mod_lt _ hlen)
  rwa [Nat.div_add_mod'] at this

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  simpa [Nat.blt_eq] using h

theorem blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · have := Nat.blt_eq.mp hb
    omega

theorem nbeq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem bit_eq_testBit (t i : Nat) : bit t i = t.testBit i := by
  unfold bit
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  by_cases h : t / 2 ^ i % 2 = 1
  · rw [nbeq_true h]
    simp [h]
  · rw [nbeq_false h]
    simp [h]

theorem tAdj_lt (t : Nat) {a b : Nat} (h : a < b) : tAdj t a b = bit t (b * (b - 1) / 2 + a) := by
  unfold tAdj
  rw [blt_true h]
  rfl

theorem tAdj_gt (t : Nat) {a b : Nat} (h : b < a) :
    tAdj t a b = !(bit t (a * (a - 1) / 2 + b)) := by
  unfold tAdj
  rw [blt_false (Nat.le_of_lt h), blt_true h]
  rfl

theorem tAdj_self (t a : Nat) : tAdj t a a = false := by
  unfold tAdj
  rw [blt_false (Nat.le_refl a)]
  rfl

theorem tAdj_swap (t : Nat) {a b : Nat} (h : a ≠ b) : tAdj t a b = !(tAdj t b a) := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · rw [tAdj_lt t h, tAdj_gt t h, Bool.not_not]
  · rw [tAdj_lt t h, tAdj_gt t h]

theorem extAdj_lt_lt (t S : Nat) {k a b : Nat} (ha : a < k) (hb : b < k) :
    extAdj t S k a b = tAdj t a b := by
  unfold extAdj
  rw [blt_true ha, blt_true hb]
  rfl

theorem extAdj_lt_eq (t S : Nat) {k a : Nat} (ha : a < k) : extAdj t S k a k = bit S a := by
  unfold extAdj
  rw [blt_true ha, blt_false (Nat.le_refl k), nbeq_true rfl]
  rfl

theorem extAdj_eq_lt (t S : Nat) {k b : Nat} (hb : b < k) : extAdj t S k k b = !(bit S b) := by
  unfold extAdj
  rw [blt_false (Nat.le_refl k), nbeq_true rfl, blt_true hb]
  rfl

theorem extAdj_eq_eq (t S k : Nat) : extAdj t S k k k = false := by
  unfold extAdj
  rw [blt_false (Nat.le_refl k), nbeq_true rfl]
  rfl

theorem extAdj_self (t S k a : Nat) (ha : a ≤ k) : extAdj t S k a a = false := by
  rcases Nat.lt_or_eq_of_le ha with h | h
  · rw [extAdj_lt_lt t S h h, tAdj_self]
  · subst h
    exact extAdj_eq_eq t S a

theorem extAdj_swap (t S : Nat) {k a b : Nat} (ha : a ≤ k) (hb : b ≤ k) (hne : a ≠ b) :
    extAdj t S k a b = !(extAdj t S k b a) := by
  rcases Nat.lt_or_eq_of_le ha with ha' | ha'
  · rcases Nat.lt_or_eq_of_le hb with hb' | hb'
    · rw [extAdj_lt_lt t S ha' hb', extAdj_lt_lt t S hb' ha', tAdj_swap t hne]
    · subst hb'
      rw [extAdj_lt_eq t S ha', extAdj_eq_lt t S ha', Bool.not_not]
  · subst ha'
    rcases Nat.lt_or_eq_of_le hb with hb' | hb'
    · rw [extAdj_eq_lt t S hb', extAdj_lt_eq t S hb']
    · exact absurd hb'.symm hne

theorem beqB_eq {x y : Bool} (h : beqB x y = true) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem injOK_sound {n m : Nat} {f : Nat → Nat} (h : injOK n m f = true) :
    (∀ a < n, f a < m) ∧ (∀ a b, a < n → b < n → f a = f b → a = b) := by
  rw [injOK, allLT_iff] at h
  have h' : ∀ a < n, f a < m ∧ ∀ b < a, f b ≠ f a := by
    intro a ha
    have := h a ha
    rw [Bool.and_eq_true, allLT_iff] at this
    refine ⟨Nat.blt_eq.mp this.1, fun b hb heq => ?_⟩
    have := this.2 b hb
    rw [nbeq_true heq] at this
    exact absurd this (by decide)
  refine ⟨fun a ha => (h' a ha).1, fun a b ha hb heq => ?_⟩
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd heq ((h' b hb).2 a hab)
  · exact hab
  · exact absurd heq.symm ((h' a ha).2 b hab)

/-- What a passing table entry says. -/
theorem entryOK_sound {k t S e t' : Nat} (h : entryOK k t S e t' = true) :
    (∀ a < k + 1, epi e a < k + 1) ∧
    (∀ a b, a < k + 1 → b < k + 1 → epi e a = epi e b → a = b) ∧
    (∀ a b, a < k + 1 → b < k + 1 → extAdj t S k (epi e a) (epi e b) = tAdj t' a b) := by
  rw [entryOK, Bool.and_eq_true] at h
  obtain ⟨hinj, hadj⟩ := h
  obtain ⟨hlt, hi⟩ := injOK_sound hinj
  rw [allLT_iff] at hadj
  have hpair : ∀ a b, a < b → b < k + 1 →
      extAdj t S k (epi e a) (epi e b) = tAdj t' a b := by
    intro a b hab hb
    have := hadj b hb
    rw [allLT_iff] at this
    rw [beqB_eq (this a hab), tAdj_lt t' hab]
  refine ⟨hlt, hi, fun a b ha hb => ?_⟩
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact hpair a b hab hb
  · subst hab
    rw [extAdj_self t S k _ (Nat.lt_succ_iff.1 (hlt a ha)), tAdj_self]
  · have hne : epi e a ≠ epi e b := fun heq => absurd (hi a b ha hb heq) (by omega)
    rw [extAdj_swap t S (Nat.lt_succ_iff.1 (hlt a ha)) (Nat.lt_succ_iff.1 (hlt b hb)) hne,
      hpair b a hab ha, tAdj_swap t' (by omega), Bool.not_not]

/-! ### Building `S` from a tournament -/

def ofBits (g : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => ofBits g k + cond (g k) (2 ^ k) 0

theorem ofBits_lt (g : Nat → Bool) (k : Nat) : ofBits g k < 2 ^ k := by
  induction k with
  | zero => simp [ofBits]
  | succ k ih =>
    simp only [ofBits]
    cases g k <;> simp [pow_succ] <;> omega

theorem ofBits_testBit (g : Nat → Bool) (k : Nat) : ∀ a < k, (ofBits g k).testBit a = g a := by
  induction k with
  | zero => intro a ha; omega
  | succ k ih =>
    intro a ha
    simp only [ofBits]
    have hlt := ofBits_lt g k
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
    · cases g k
      · simpa using ih a h
      · simp only [Bool.cond_true]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt h]
        exact ih a h
    · subst h
      cases hg : g a
      · simp only [Bool.cond_false, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
      · simp only [Bool.cond_true]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl

theorem bit_ofBits (g : Nat → Bool) {k a : Nat} (ha : a < k) : bit (ofBits g k) a = g a := by
  rw [bit_eq_testBit, ofBits_testBit g k a ha]

/-! ### Classification of tournaments on `Fin k` -/

def IsTourRel {k : Nat} (R : Fin k → Fin k → Prop) : Prop :=
  (∀ a, ¬ R a a) ∧ ∀ a b, a ≠ b → (R a b ↔ ¬ R b a)

/-- Every tournament on `Fin k` is isomorphic to one of the listed representatives. -/
def Classified (k : Nat) : Prop :=
  ∀ R : Fin k → Fin k → Prop, IsTourRel R →
    ∃ i, i < numReps k ∧ ∃ σ : Fin k → Fin k, Function.Injective σ ∧
      ∀ a b : Fin k, R (σ a) (σ b) ↔ tAdj (rep k i) a b = true

theorem classified_succ {k : Nat} (h : Classified k)
    (hs : allLT (numReps k) (stepBody k) = true) : Classified (k + 1) := by
  classical
  intro R hR
  let R' : Fin k → Fin k → Prop := fun a b => R a.castSucc b.castSucc
  have hR' : IsTourRel R' := by
    refine ⟨fun a => hR.1 _, fun a b hab => hR.2 _ _ ?_⟩
    exact fun heq => hab (Fin.castSucc_injective k heq)
  obtain ⟨i, hi, σ', hσ'inj, hσ'⟩ := h R' hR'
  let g : Nat → Bool := fun a =>
    if ha : a < k then decide (R (σ' ⟨a, ha⟩).castSucc (Fin.last k)) else false
  let S := ofBits g k
  have hS : S < 2 ^ k := ofBits_lt g k
  have hbody := (allLT_iff _ _).1 hs i hi
  unfold stepBody at hbody
  have hentry := (allLT_iff _ _).1 hbody S hS
  rw [Bool.and_eq_true] at hentry
  obtain ⟨hj, hok⟩ := hentry
  set e := entry k i S
  obtain ⟨hlt, hinj, hadj⟩ := entryOK_sound hok
  -- τ relabels the extension (vertices 0..k) into `R`
  let τ : Fin (k + 1) → Fin (k + 1) := fun x =>
    if hx : (x : Nat) < k then (σ' ⟨x, hx⟩).castSucc else Fin.last k
  have hτinj : Function.Injective τ := by
    intro x y hxy
    simp only [τ] at hxy
    by_cases hx : (x : Nat) < k <;> by_cases hy : (y : Nat) < k <;>
      simp only [hx, hy, dite_true, dite_false] at hxy
    · have := hσ'inj (Fin.castSucc_injective k hxy)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · exact absurd hxy (Fin.castSucc_ne_last _)
    · exact absurd hxy.symm (Fin.castSucc_ne_last _)
    · exact Fin.ext (by omega)
  have hkey : ∀ x y : Fin (k + 1), R (τ x) (τ y) ↔ extAdj (rep k i) S k x y = true := by
    intro x y
    by_cases hx : (x : Nat) < k <;> by_cases hy : (y : Nat) < k
    · simp only [τ, hx, hy, dite_true]
      rw [extAdj_lt_lt _ _ hx hy]
      exact hσ' ⟨x, hx⟩ ⟨y, hy⟩
    · have hyk : (y : Nat) = k := by omega
      simp only [τ, hx, hy, dite_true, dite_false]
      rw [hyk, extAdj_lt_eq _ _ hx, bit_ofBits g hx]
      simp [g, hx]
    · have hxk : (x : Nat) = k := by omega
      simp only [τ, hx, hy, dite_true, dite_false]
      rw [hxk, extAdj_eq_lt _ _ hy, bit_ofBits g hy]
      have hne : Fin.last k ≠ (σ' ⟨y, hy⟩).castSucc := (Fin.castSucc_ne_last _).symm
      rw [hR.2 _ _ hne]
      simp [g, hy]
    · have hxk : (x : Nat) = k := by omega
      have hyk : (y : Nat) = k := by omega
      simp only [τ, hx, hy, dite_false]
      rw [hxk, hyk, extAdj_eq_eq]
      simp [hR.1]
  refine ⟨e % 2 ^ 13, Nat.blt_eq.mp hj, fun a => τ ⟨epi e a, hlt a a.2⟩, ?_, fun a b => ?_⟩
  · intro a b hab
    have := hτinj hab
    exact Fin.ext (hinj a b a.2 b.2 (congrArg Fin.val this))
  · rw [hkey]
    simp only
    rw [hadj a b a.2 b.2]

theorem classified_one : Classified 1 := by
  intro R hR
  refine ⟨0, Nat.zero_lt_one, id, Function.injective_id, fun a b => ?_⟩
  have ha : a = 0 := Fin.ext (by omega)
  have hb : b = 0 := Fin.ext (by omega)
  subst ha hb
  simp only [id]
  rw [show ((0 : Fin 1) : Nat) = 0 from rfl, tAdj_self]
  simp [hR.1]

/-! ### Embeddings of tree representatives -/

theorem embBody_sound {n m i : Nat} (h : embBody n m i = true) :
    ∀ r < numTrees n, (∀ a < n, embF n i r a < m) ∧
      (∀ a b, a < n → b < n → embF n i r a = embF n i r b → a = b) ∧
      ∀ q ∈ treeArcs n r, tAdj (rep m i) (embF n i r q.1) (embF n i r q.2) = true := by
  intro r hr
  have := (allLT_iff _ _).1 h r hr
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨(injOK_sound this.1).1, (injOK_sound this.1).2, this.2⟩

/-! ### Parent codes -/

theorem allPar_sound : ∀ (l : Nat) (p : List Nat → Nat → Bool), allPar l p = true →
    ∀ ps : List Nat, ps.length = l → (∀ i < l, ps.getD i 0 < max i 1) → ∃ idx, p ps idx = true
  | 0, p, h, ps, hl, _ => by
    rw [List.length_eq_zero_iff] at hl
    subst hl
    exact ⟨0, h⟩
  | l + 1, p, h, ps, hl, hb => by
    rcases List.eq_nil_or_concat ps with h0 | ⟨L, x, rfl⟩
    · subst h0
      simp at hl
    · rw [List.concat_eq_append] at hl hb ⊢
      have hL : L.length = l := by simpa using hl
      have hbL : ∀ i < l, L.getD i 0 < max i 1 := by
        intro i hi
        have := hb i (by omega)
        rwa [List.getD_append _ _ _ _ (by omega)] at this
      have hx : x < max l 1 := by
        have := hb l (by omega)
        rwa [List.getD_append_right _ _ _ _ (by omega), hL, Nat.sub_self] at this
      obtain ⟨idx, hidx⟩ := allPar_sound l _ h L hL hbL
      exact ⟨_, (allLT_iff _ _).1 hidx x hx⟩

theorem arcIn_sound {L : List (Nat × Nat)} {a b : Nat} (h : arcIn L a b = true) : (a, b) ∈ L := by
  rw [arcIn, List.any_eq_true] at h
  obtain ⟨q, hq, hab⟩ := h
  rw [Bool.and_eq_true] at hab
  have h1 := Nat.eq_of_beq_eq_true hab.1
  have h2 := Nat.eq_of_beq_eq_true hab.2
  rw [← h1, ← h2]
  exact hq

theorem codesOK_sound {n : Nat} (h : codesOK n = true) (ps : List Nat) (hl : ps.length = n)
    (hb : ∀ i < n, ps.getD i 0 < max i 1) (d : Nat) (hd : d < 2 ^ (n - 1)) :
    ∃ r < numTrees n, ∃ ρ : Nat → Nat, (∀ a < n, ρ a < n) ∧
      (∀ a b, a < n → b < n → ρ a = ρ b → a = b) ∧
      ∀ i, 0 < i → i < n → (ρ (codeArc ps d i).1, ρ (codeArc ps d i).2) ∈ treeArcs n r := by
  obtain ⟨idx, hidx⟩ := allPar_sound n _ h ps hl hb
  have hc := (allLT_iff _ _).1 hidx d hd
  unfold codeOK at hc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hr, hinj⟩, harcs⟩ := hc
  refine ⟨_, Nat.blt_eq.mp hr, _, (injOK_sound hinj).1, (injOK_sound hinj).2, ?_⟩
  intro i hi0 hi
  have := (allLT_iff _ _).1 harcs i hi
  rw [Bool.or_eq_true, nbeq_false (by omega : i ≠ 0)] at this
  simp only [Bool.false_eq_true, false_or] at this
  exact arcIn_sound this

/-! ## Statement (definitions copied from formal-conjectures) -/

def IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

def IsOrientation {V : Type*} (D : Digraph V) (H : SimpleGraph V) : Prop :=
  (∀ u v, D.Adj u v → H.Adj u v) ∧ (∀ u v, H.Adj u v → (D.Adj u v ↔ ¬ D.Adj v u))

def IsOrientedTree {W : Type*} (D : Digraph W) : Prop :=
  ∃ T : SimpleGraph W, T.IsTree ∧ IsOrientation D T

structure Hom {V W : Type*} (D : Digraph V) (D' : Digraph W) where
  toFun : V → W
  map_adj' : ∀ {u v : V}, D.Adj u v → D'.Adj (toFun u) (toFun v)

def Embeds {W V : Type*} (D : Digraph W) (D' : Digraph V) : Prop :=
  ∃ f : Hom D D', Function.Injective f.toFun

/-! ## Trees as parent codes -/

theorem walk_step {W : Type*} {T : SimpleGraph W} {v r : W} (q : T.Walk v r) (h : v ≠ r) :
    ∃ w, T.Adj v w ∧ ∃ q' : T.Walk w r, q'.length + 1 = q.length := by
  cases q with
  | nil => exact absurd rfl h
  | cons hadj q' => exact ⟨_, hadj, q', by simp⟩

/-- Every finite tree, listed in order of distance from a root, has each non-root vertex
joined to an earlier one, and these parent edges are all the edges. -/
theorem tree_parent_code {W : Type*} [Fintype W] {T : SimpleGraph W} (hT : T.IsTree)
    {n : Nat} (hn : Fintype.card W = n) (hpos : 0 < n) :
    ∃ e : Fin n ≃ W, ∃ par : Fin n → Fin n, (∀ i : Fin n, 0 < (i : Nat) → par i < i) ∧
      ∀ u v : Fin n, T.Adj (e u) (e v) →
        ((0 < (v : Nat) ∧ par v = u) ∨ (0 < (u : Nat) ∧ par u = v)) := by
  classical
  have hne : Nonempty W := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨r⟩ := hne
  have hstep : ∀ v, v ≠ r → ∃ w, T.Adj w v ∧ T.dist r w < T.dist r v := by
    intro v hv
    obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist r v
    obtain ⟨w, hvw, q', hq'⟩ := walk_step p.reverse hv
    refine ⟨w, hvw.symm, ?_⟩
    have h1 := SimpleGraph.dist_le q'.reverse
    rw [SimpleGraph.Walk.length_reverse] at h1
    rw [SimpleGraph.Walk.length_reverse] at hq'
    omega
  let par : W → W := fun v => if hv : v = r then r else Classical.choose (hstep v hv)
  have hpar : ∀ v, v ≠ r → T.Adj (par v) v ∧ T.dist r (par v) < T.dist r v := by
    intro v hv
    simp only [par, hv, dite_false]
    exact Classical.choose_spec (hstep v hv)
  -- every edge is a parent edge
  have hedge : ∀ a b, T.Adj a b →
      (b ≠ r ∧ par b = a) ∨ (a ≠ r ∧ par a = b) := by
    intro a b hab
    let P : Finset (Sym2 W) := (Finset.univ.erase r).image (fun v => s(par v, v))
    have hPsub : P ⊆ T.edgeFinset := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hz
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (hpar v (Finset.ne_of_mem_erase hv)).1
    have hPcard : P.card = n - 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ r),
        Finset.card_univ, hn]
      intro v hv v' hv' heq
      have hv0 := Finset.ne_of_mem_erase hv
      have hv0' := Finset.ne_of_mem_erase hv'
      rcases Sym2.eq_iff.1 heq with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h
      · have := (hpar v hv0).2
        have := (hpar v' hv0').2
        rw [h1] at *
        rw [← h2] at *
        omega
    have hE := hT.card_edgeFinset
    have hPeq : P = T.edgeFinset :=
      Finset.eq_of_subset_of_card_le hPsub (by rw [hPcard]; omega)
    have hmem : s(a, b) ∈ P := by
      rw [hPeq, SimpleGraph.mem_edgeFinset]
      exact hab
    obtain ⟨v, hv, hveq⟩ := Finset.mem_image.1 hmem
    have hv0 := Finset.ne_of_mem_erase hv
    rcases Sym2.eq_iff.1 hveq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      subst h2
      exact ⟨hv0, h1⟩
    · right
      subst h2
      exact ⟨hv0, h1⟩
  -- order the vertices by distance from `r`
  let e0 : Fin n ≃ W := (Fintype.equivFinOfCardEq hn).symm
  let f : Fin n → Nat := fun i => T.dist r (e0 i)
  let e : Fin n ≃ W := (Tuple.sort f).trans e0
  have hmono : Monotone (fun i => T.dist r (e i)) := Tuple.monotone_sort f
  have hord : ∀ i j : Fin n, T.dist r (e i) < T.dist r (e j) → i < j := by
    intro i j h
    by_contra hij
    have := hmono (not_lt.1 hij)
    simp only at this
    omega
  have hdpos : ∀ v, v ≠ r → 0 < T.dist r v := by
    intro v hv
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [hT.connected.dist_eq_zero_iff] at h0
    exact hv h0.symm
  have hroot : ∀ i : Fin n, 0 < (i : Nat) → e i ≠ r := by
    intro i hi hei
    have h0 : e ⟨0, hpos⟩ ≠ r := by
      intro h0
      have : i = ⟨0, hpos⟩ := e.injective (hei.trans h0.symm)
      rw [this] at hi
      exact absurd hi (lt_irrefl 0)
    have := hord i ⟨0, hpos⟩ (by rw [hei, SimpleGraph.dist_self]; exact hdpos _ h0)
    exact absurd this (by simp [Fin.lt_def])
  refine ⟨e, fun i => e.symm (par (e i)), ?_, ?_⟩
  · intro i hi
    apply hord
    rw [Equiv.apply_symm_apply]
    exact (hpar (e i) (hroot i hi)).2
  · intro u v huv
    rcases hedge _ _ huv with ⟨hvr, hp⟩ | ⟨hur, hp⟩
    · left
      have hlt := hord u v (hp ▸ (hpar (e v) hvr).2)
      rw [Fin.lt_def] at hlt
      refine ⟨by omega, ?_⟩
      show e.symm (par (e v)) = u
      rw [hp, Equiv.symm_apply_apply]
    · right
      have hlt := hord v u (hp ▸ (hpar (e u) hur).2)
      rw [Fin.lt_def] at hlt
      refine ⟨by omega, ?_⟩
      show e.symm (par (e u)) = v
      rw [hp, Equiv.symm_apply_apply]

/-! ## Assembly -/

theorem sumner_of_checks (n m : Nat) (hn : 2 ≤ n) (hm : m = 2 * n - 2) (hcl : Classified m)
    (hemb : allLT (numReps m) (embBody n m) = true) (hcodes : codesOK n = true)
    {W : Type} [Fintype W] (D : Digraph W) (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    {V : Type} [Fintype V] (G : Digraph V) (hV : Fintype.card V = 2 * n - 2)
    (hG : IsTournament G) : Embeds D G := by
  classical
  obtain ⟨T, hT, hor⟩ := hD
  obtain ⟨e, par, hpar, hadj⟩ := tree_parent_code hT hW (by omega)
  -- the parent list and the direction bits
  let ps : List Nat := List.ofFn (fun i : Fin n => if (i : Nat) = 0 then 0 else (par i : Nat))
  have hps : ∀ i : Fin n, 0 < (i : Nat) → ps.getD i 0 = par i := by
    intro i hi
    simp only [ps, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.2, Nat.pos_iff_ne_zero.1 hi]
  have hpsl : ps.length = n := List.length_ofFn
  have hpsb : ∀ i < n, ps.getD i 0 < max i 1 := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp [ps, List.getD_eq_getElem?_getD, hi]
    · rw [hps ⟨i, hi⟩ (Nat.pos_of_ne_zero h0)]
      have := hpar ⟨i, hi⟩ (Nat.pos_of_ne_zero h0)
      rw [Fin.lt_def] at this
      simp only at this
      omega
  let g : Nat → Bool := fun j =>
    if hj : j + 1 < n then decide (D.Adj (e (par ⟨j + 1, hj⟩)) (e ⟨j + 1, hj⟩)) else false
  let d := ofBits g (n - 1)
  have hd : d < 2 ^ (n - 1) := ofBits_lt g (n - 1)
  obtain ⟨r, hr, ρ, hρlt, hρinj, hρarc⟩ := codesOK_sound hcodes ps hpsl hpsb d hd
  -- every arc of `D` is a code arc
  have harc : ∀ u v : Fin n, D.Adj (e u) (e v) →
      ∃ i, 0 < i ∧ i < n ∧ codeArc ps d i = ((u : Nat), (v : Nat)) := by
    intro u v huv
    have hT' := hor.1 _ _ huv
    rcases hadj u v hT' with ⟨hv, hp⟩ | ⟨hu, hp⟩
    · refine ⟨v, hv, v.2, ?_⟩
      have hbit : bit d ((v : Nat) - 1) = true := by
        rw [bit_ofBits g (by omega)]
        have hv' : (v : Nat) - 1 + 1 < n := by omega
        simp only [g, hv', dite_true, decide_eq_true_eq]
        have : (⟨(v : Nat) - 1 + 1, hv'⟩ : Fin n) = v := Fin.ext (by simp; omega)
        rw [this, hp]
        exact huv
      unfold codeArc
      rw [hbit, hps v hv, hp]
      rfl
    · refine ⟨u, hu, u.2, ?_⟩
      have hbit : bit d ((u : Nat) - 1) = false := by
        rw [bit_ofBits g (by omega)]
        have hu' : (u : Nat) - 1 + 1 < n := by omega
        simp only [g, hu', dite_true, decide_eq_false_iff_not]
        have : (⟨(u : Nat) - 1 + 1, hu'⟩ : Fin n) = u := Fin.ext (by simp; omega)
        rw [this, hp]
        exact (hor.2 _ _ hT').1 huv
      unfold codeArc
      rw [hbit, hps u hu, hp]
      rfl
  -- classify `G`
  have hVm : Fintype.card V = m := by rw [hV, hm]
  let eV : Fin m ≃ V := (Fintype.equivFinOfCardEq hVm).symm
  let R : Fin m → Fin m → Prop := fun a b => G.Adj (eV a) (eV b)
  have hR : IsTourRel R := by
    refine ⟨fun a => hG.1 _, fun a b hab => hG.2 _ _ ?_⟩
    exact fun h => hab (eV.injective h)
  obtain ⟨i, hi, σ, hσinj, hσ⟩ := hcl R hR
  obtain ⟨hflt, hfinj, hfarc⟩ := embBody_sound ((allLT_iff _ _).1 hemb i hi) r hr
  let φ : W → V := fun w =>
    eV (σ ⟨embF n i r (ρ (e.symm w)), hflt _ (hρlt _ (e.symm w).2)⟩)
  refine ⟨⟨φ, fun {w w'} hww => ?_⟩, ?_⟩
  · have hww' : D.Adj (e (e.symm w)) (e (e.symm w')) := by simpa using hww
    obtain ⟨j, hj0, hjn, hj⟩ := harc _ _ hww'
    have hmem := hρarc j hj0 hjn
    rw [hj] at hmem
    have := hfarc _ hmem
    exact (hσ _ _).2 this
  · intro w w' hww
    simp only [φ] at hww
    have h1 := Fin.ext_iff.1 (hσinj (eV.injective hww))
    simp only at h1
    have h2 := hfinj _ _ (hρlt _ (e.symm w).2) (hρlt _ (e.symm w').2) h1
    have h3 := hρinj _ _ (e.symm w).2 (e.symm w').2 h2
    exact e.symm.injective (Fin.ext h3)
