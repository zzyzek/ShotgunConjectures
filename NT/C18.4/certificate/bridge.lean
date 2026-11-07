
theorem family_to_finset (n : ℕ) (Y : ℤ → ℤ) (e1 e2 : ℕ) (he : e1 ≠ e2) (he1 : e1 < n)
    (he2 : e2 < n)
    (hok : ∀ t1 t2 : ℕ, t1 < t2 → t2 < n → t1 ≠ e1 → t1 ≠ e2 → t2 ≠ e1 → t2 ≠ e2 →
      ∀ j : ℤ, (j = -1 ∨ j = 0 ∨ j = 1) → ¬ (n : ℤ) ∣ (Y t2 + j * t2) - (Y t1 + j * t1)) :
    ∃ S : Finset (ZMod n × ZMod n), S.card = n - 2 ∧ NonAttacking S := by
  classical
  set T : Finset ℕ := (Finset.range n) \ {e1, e2} with hT
  have hTc : T.card = n - 2 := by
    rw [hT, Finset.card_sdiff_of_subset (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simpa using ‹_›)]
    simp [Finset.card_pair he]
  have hmemT : ∀ t, t ∈ T ↔ t < n ∧ t ≠ e1 ∧ t ≠ e2 := by
    intro t; simp [hT]
  have cast_inj : ∀ a b : ℕ, a < n → b < n → ((a : ZMod n) = b) → a = b := by
    intro a b ha hb h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  -- an ordered key: for t1 < t2 in T, the three keys differ in ZMod n
  have key : ∀ t1 t2 : ℕ, t1 ∈ T → t2 ∈ T → t1 < t2 → ∀ j : ℤ, (j = -1 ∨ j = 0 ∨ j = 1) →
      ((Y t1 + j * t1 : ℤ) : ZMod n) ≠ ((Y t2 + j * t2 : ℤ) : ZMod n) := by
    intro t1 t2 h1 h2 hlt j hj heq
    rw [hmemT] at h1 h2
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at heq
    exact hok t1 t2 hlt h2.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 j hj heq
  refine ⟨T.image (fun t : ℕ => ((t : ZMod n), ((Y (t : ℤ) : ℤ) : ZMod n))), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hTc]
    intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    exact cast_inj a b ((hmemT a).1 ha).1 ((hmemT b).1 hb).1 hab.1
  · intro p hp q hq hpq
    simp only [Finset.mem_image] at hp hq
    obtain ⟨t1, h1, rfl⟩ := hp
    obtain ⟨t2, h2, rfl⟩ := hq
    have hne : t1 ≠ t2 := by rintro rfl; exact hpq rfl
    have k0 := fun a b (ha : a ∈ T) (hb : b ∈ T) (hab : a < b) => key a b ha hb hab 0 (by simp)
    have kp := fun a b (ha : a ∈ T) (hb : b ∈ T) (hab : a < b) => key a b ha hb hab 1 (by simp)
    have km := fun a b (ha : a ∈ T) (hb : b ∈ T) (hab : a < b) => key a b ha hb hab (-1) (by simp)
    simp only [zero_mul, add_zero, one_mul, neg_one_mul, ← sub_eq_add_neg] at k0 kp km
    push_cast at k0 kp km
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hne (cast_inj t1 t2 ((hmemT t1).1 h1).1 ((hmemT t2).1 h2).1 h)
    · intro h
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact k0 t1 t2 h1 h2 hl h
      · exact k0 t2 t1 h2 h1 hl h.symm
    · intro h
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact kp t1 t2 h1 h2 hl (by simpa [add_comm] using h)
      · exact kp t2 t1 h2 h1 hl (by simpa [add_comm] using h.symm)
    · intro h
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact km t1 t2 h1 h2 hl h
      · exact km t2 t1 h2 h1 hl h.symm
