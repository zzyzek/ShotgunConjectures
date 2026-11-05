import Mathlib

/-!
# Dean's conjecture: longest-path lemmas (FAM-dean-cycles)

Dean (1988): every finite simple graph with minimum degree `≥ k ≥ 3` has a cycle whose length is
divisible by `k`. Statement shape and `cycleLengths` copied from google-deepmind/formal-conjectures
(`FormalConjectures/Arxiv/2605.02731/DeanCycles.lean`,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean`, Apache 2.0).

Checked here (all known results, proved from scratch):
* `cycle_of_two_neighbours`: if `p` is a path starting at `u` and `u` is adjacent to the vertices at
  positions `1 ≤ i < j` of `p`, then `G` has a cycle of length `j - i + 2`.
* `exists_path_nbrs_mem`: a finite nonempty graph has a path `p` from some `u` such that every
  neighbour of `u` lies on `p` (a longest path).
* `exists_cycle_mod_two`: minimum degree `≥ k + 1` (`k ≥ 1`) gives a cycle of length `≡ 2 (mod k)`.
* `exists_cycle_mod_two_five`: the case `k = 5` (minimum degree `≥ 6`).
* `exists_cycle_length_ge`: minimum degree `≥ k ≥ 2` gives a cycle of length `≥ k + 1`.

Not checked here: Dean's conjecture for any `k` (in particular `k = 3` of Chen–Saito and the open
case `k = 5`).
-/

namespace DeanSmall

open SimpleGraph

/-- `G.cycleLengths` is the set of lengths of the cycles in `G` (copied from formal-conjectures). -/
def cycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m | ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

variable {V : Type} (G : SimpleGraph V)

/-- A path from `u` and two chords from `u` to positions `1 ≤ i < j` close a cycle of length
`j - i + 2`. -/
theorem cycle_of_two_neighbours {u v : V} (p : G.Walk u v) (hp : p.IsPath) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ p.length)
    (hai : G.Adj u (p.getVert i)) (haj : G.Adj u (p.getVert j)) :
    j - i + 2 ∈ cycleLengths G := by
  have hend : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  let q : G.Walk (p.getVert i) (p.getVert j) := ((p.drop i).take (j - i)).copy rfl hend
  have hq : q.IsPath := by
    simp only [q, Walk.isPath_copy]
    exact (hp.drop i).take (j - i)
  have hqlen : q.length = j - i := by
    simp only [q, Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  -- Every vertex of `q` is `p.getVert t` with `i ≤ t ≤ j`.
  --
  have hsupp : ∀ x ∈ q.support, ∃ t, i ≤ t ∧ t ≤ j ∧ p.getVert t = x := by
    intro x hx
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    refine ⟨i + min (j - i) n, by omega, by omega, ?_⟩
    rw [← hn]
    simp only [q, Walk.getVert_copy, Walk.take_getVert, Walk.drop_getVert]
  have hinj := hp.getVert_injOn
  have hu : u ∉ q.support := by
    intro hx
    obtain ⟨t, ht1, ht2, ht⟩ := hsupp u hx
    have : t = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega) (by simp)
      (ht.trans (p.getVert_zero).symm)
    omega
  refine ⟨u, Walk.cons hai (q.concat haj.symm), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hq.concat hu haj.symm, ?_⟩
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, not_or]
    constructor
    · intro he
      exact hu (q.fst_mem_support_of_mem_edges he)
    · intro he
      simp only [List.mem_singleton, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : j = 0 := hinj (by simp only [Set.mem_ofPred_eq]; omega) (by simp)
          (h1.symm.trans (p.getVert_zero).symm)
        omega
      · have : i = j := hinj (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; omega) h2
        omega
  · simp only [Walk.length_cons, Walk.length_concat, hqlen]

/-- A longest path: a path from `u` containing every neighbour of `u`. -/
theorem exists_path_nbrs_mem [Fintype V] [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ w, G.Adj u w → w ∈ p.support := by
  classical
  let P : ℕ → Prop := fun n => ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n
  let N := Nat.findGreatest P (Fintype.card V)
  have h0 : P 0 := by
    obtain ⟨x⟩ := ‹Nonempty V›
    exact ⟨x, x, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hN : P N := Nat.findGreatest_spec (Nat.zero_le _) h0
  obtain ⟨u, v, p, hp, hpl⟩ := hN
  refine ⟨u, v, p, hp, fun w hw => ?_⟩
  by_contra hns
  have hc : (Walk.cons hw.symm p).IsPath := hp.cons hns
  have hle : p.length + 1 ≤ N := by
    apply Nat.le_findGreatest
    · have := hc.length_lt
      simp only [Walk.length_cons] at this
      omega
    · exact ⟨w, v, _, hc, by simp⟩
  omega

/-- Position of a vertex on a walk (length of the initial segment up to it). -/
private theorem pos_spec {u v : V} (p : G.Walk u v) [DecidableEq V] {w : V}
    (hw : w ∈ p.support) (hne : w ≠ u) :
    1 ≤ (p.takeUntil w hw).length ∧ (p.takeUntil w hw).length ≤ p.length ∧
      p.getVert (p.takeUntil w hw).length = w := by
  refine ⟨?_, p.length_takeUntil_le_length hw, p.getVert_length_takeUntil hw⟩
  rcases Nat.eq_zero_or_pos (p.takeUntil w hw).length with h | h
  · have := p.getVert_length_takeUntil hw
    rw [h, Walk.getVert_zero] at this
    exact absurd this.symm hne
  · exact h

/-- Minimum degree `≥ k + 1` gives a cycle of length `≡ 2 (mod k)`. -/
theorem exists_cycle_mod_two [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hδ : k + 1 ≤ G.minDegree) : ∃ m ∈ cycleLengths G, m ≡ 2 [MOD k] := by
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hδ
  obtain ⟨u, v, p, hp, hmem⟩ := exists_path_nbrs_mem G
  let pos : V → ℕ := fun w => if hw : w ∈ p.support then (p.takeUntil w hw).length else 0
  have hpos : ∀ w ∈ G.neighborFinset u, 1 ≤ pos w ∧ pos w ≤ p.length ∧ p.getVert (pos w) = w := by
    intro w hw
    rw [mem_neighborFinset] at hw
    have := pos_spec G p (hmem w hw) (G.ne_of_adj hw).symm
    simpa [pos, hmem w hw] using this
  have hcard : (Finset.range k).card < (G.neighborFinset u).card := by
    rw [Finset.card_range, card_neighborFinset_eq_degree]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (hδ.trans (G.minDegree_le_degree u))
  obtain ⟨a, ha, b, hb, hab, habk⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun w => pos w % k) (fun w _ => by simp [Nat.mod_lt _ hk])
  obtain ⟨ha1, ha2, ha3⟩ := hpos a ha
  obtain ⟨hb1, hb2, hb3⟩ := hpos b hb
  have hab' : pos a ≠ pos b := fun h => hab (ha3.symm.trans (h ▸ hb3))
  have hadj : ∀ w ∈ G.neighborFinset u, G.Adj u w := fun w hw => (mem_neighborFinset _ _ _).mp hw
  rcases lt_or_gt_of_ne hab' with h | h
  · refine ⟨pos b - pos a + 2, cycle_of_two_neighbours G p hp ha1 h hb2
      (by rw [ha3]; exact hadj a ha) (by rw [hb3]; exact hadj b hb), ?_⟩
    have : pos a % k = pos b % k := habk
    have hm : (pos b - pos a) % k = 0 := Nat.sub_mod_eq_zero_of_mod_eq this.symm
    exact Nat.ModEq.add_right 2 (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero hm))
  · refine ⟨pos a - pos b + 2, cycle_of_two_neighbours G p hp hb1 h ha2
      (by rw [hb3]; exact hadj b hb) (by rw [ha3]; exact hadj a ha), ?_⟩
    have : pos a % k = pos b % k := habk
    have hm : (pos a - pos b) % k = 0 := Nat.sub_mod_eq_zero_of_mod_eq this
    exact Nat.ModEq.add_right 2 (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero hm))

/-- `k = 5`: minimum degree `≥ 6` gives a cycle of length `≡ 2 (mod 5)`. -/
theorem exists_cycle_mod_two_five {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hδ : 6 ≤ G.minDegree) : ∃ m ∈ cycleLengths G, m ≡ 2 [MOD 5] :=
  exists_cycle_mod_two G 5 (by norm_num) hδ

/-- Minimum degree `≥ k ≥ 2` gives a cycle of length at least `k + 1`. -/
theorem exists_cycle_length_ge [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (k : ℕ)
    (hk : 2 ≤ k) (hδ : k ≤ G.minDegree) : ∃ m ∈ cycleLengths G, k + 1 ≤ m := by
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hδ
    omega
  obtain ⟨u, v, p, hp, hmem⟩ := exists_path_nbrs_mem G
  let pos : V → ℕ := fun w => if hw : w ∈ p.support then (p.takeUntil w hw).length else 0
  have hpos : ∀ w ∈ G.neighborFinset u, 1 ≤ pos w ∧ pos w ≤ p.length ∧ p.getVert (pos w) = w := by
    intro w hw
    rw [mem_neighborFinset] at hw
    have := pos_spec G p (hmem w hw) (G.ne_of_adj hw).symm
    simpa [pos, hmem w hw] using this
  have hadj : ∀ w ∈ G.neighborFinset u, G.Adj u w := fun w hw => (mem_neighborFinset _ _ _).mp hw
  -- The positions of the `≥ k` neighbours are distinct numbers in `[1, length]`, so the
  -- largest is at least `k` and the smallest is `1`.
  --
  have hinj : Set.InjOn pos (G.neighborFinset u) := by
    intro a ha b hb h
    exact (hpos a ha).2.2.symm.trans (h ▸ (hpos b hb).2.2)
  have hdeg : k ≤ (G.neighborFinset u).card := by
    rw [card_neighborFinset_eq_degree]
    exact hδ.trans (G.minDegree_le_degree u)
  have himg : ((G.neighborFinset u).image pos).card = (G.neighborFinset u).card :=
    Finset.card_image_of_injOn hinj
  have hsub : (G.neighborFinset u).image pos ⊆ Finset.Icc 1 p.length := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr ⟨(hpos w hw).1, (hpos w hw).2.1⟩
  have hnonempty : ((G.neighborFinset u).image pos).Nonempty := by
    rw [← Finset.card_pos, himg]
    omega
  let M := ((G.neighborFinset u).image pos).max' hnonempty
  have hM : M ∈ (G.neighborFinset u).image pos := Finset.max'_mem _ _
  obtain ⟨b, hb, hbM⟩ := Finset.mem_image.mp hM
  have hMk : k ≤ M := by
    have hsub' : (G.neighborFinset u).image pos ⊆ Finset.Icc 1 M := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hsub hx)).1, Finset.le_max' _ _ hx⟩
    have := Finset.card_le_card hsub'
    rw [Nat.card_Icc, himg] at this
    omega
  -- The first step of the path goes to a neighbour at position 1.
  --
  have hlen : 1 ≤ p.length := (hpos b hb).1.trans (hpos b hb).2.1
  have h1 : G.Adj u (p.getVert 1) := by
    have := p.adj_getVert_succ (i := 0) (by omega)
    simpa using this
  have hM1 : 1 < M := by omega
  refine ⟨M - 1 + 2, cycle_of_two_neighbours G p hp le_rfl hM1 (hbM ▸ (hpos b hb).2.1) h1
    (hbM ▸ (hpos b hb).2.2.symm ▸ hadj b hb), by omega⟩
