
theorem lower_F3 (m : ℕ) :
    ∃ S : Finset (ZMod (6*m+3) × ZMod (6*m+3)), S.card = (6*m+3) - 2 ∧ NonAttacking S :=
  family_to_finset (6*m+3) (YF3 m) (3*m+1) (4*m+2) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F3_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F4 (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset (ZMod (12*m+4) × ZMod (12*m+4)), S.card = (12*m+4) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m+4) (YF4 m) (5*m) (12*m+3) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F4_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F6 (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset (ZMod (12*m+6) × ZMod (12*m+6)), S.card = (12*m+6) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m+6) (YF6 m) (6*m+3) (8*m+4) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F6_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F8 (m : ℕ) :
    ∃ S : Finset (ZMod (12*m+8) × ZMod (12*m+8)), S.card = (12*m+8) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m+8) (YF8 ((m : ℤ) + 1)) (2*m+1) (9*m+5) (by omega) (by omega) (by omega)
    (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F8_ok ((m : ℤ) + 1) t1 t2 j k (by omega) hj (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_F12 (m : ℕ) (hm : 2 ≤ m) :
    ∃ S : Finset (ZMod (12*m) × ZMod (12*m)), S.card = (12*m) - 2 ∧ NonAttacking S :=
  family_to_finset (12*m) (YF12 m) (4*m-2) (9*m-1) (by omega) (by omega) (by omega) (by
    intro t1 t2 h12 h2 a1 a2 b1 b2 j hj ⟨k, hk⟩
    exact F12_ok m t1 t2 j k (by omega) hj (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hk]; push_cast; ring))

theorem lower_4 : ∃ S : Finset (ZMod 4 × ZMod 4), S.card = 4 - 2 ∧ NonAttacking S :=
  ⟨{(0, 0), (1, 2)}, by decide, by unfold NonAttacking; decide⟩

theorem lower_6 : ∃ S : Finset (ZMod 6 × ZMod 6), S.card = 6 - 2 ∧ NonAttacking S :=
  ⟨{(0, 0), (1, 3), (2, 5), (3, 2)}, by decide, by unfold NonAttacking; decide⟩

theorem lower_12 : ∃ S : Finset (ZMod 12 × ZMod 12), S.card = 12 - 2 ∧ NonAttacking S :=
  ⟨{(0, 0), (1, 2), (2, 4), (3, 1), (4, 7), (5, 9), (6, 11), (7, 3), (8, 5), (11, 10)},
    by decide +kernel, by unfold NonAttacking; decide +kernel⟩

/-- Heden's conjectured lower bound: n - 2 non-attacking queens on the n × n torus whenever
3 ∣ n or 4 ∣ n (n ≥ 3). -/
theorem queens_lower (n : ℕ) (h3 : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n) :
    ∃ S : Finset (ZMod n × ZMod n), S.card = n - 2 ∧ NonAttacking S := by
  have hr : n % 12 = 0 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 6 ∨ n % 12 = 8 ∨ n % 12 = 9 := by
    omega
  rcases hr with h | h | h | h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m := ⟨n / 12, by omega⟩
    rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
    · exact lower_12
    · exact lower_F12 m hm
  · obtain ⟨m, rfl⟩ : ∃ m, n = 6 * m + 3 := ⟨n / 6, by omega⟩
    exact lower_F3 m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m + 4 := ⟨n / 12, by omega⟩
    rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
    · exact lower_4
    · exact lower_F4 m hm
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m + 6 := ⟨n / 12, by omega⟩
    rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
    · exact lower_6
    · exact lower_F6 m hm
  · obtain ⟨m, rfl⟩ : ∃ m, n = 12 * m + 8 := ⟨n / 12, by omega⟩
    exact lower_F8 m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 6 * m + 3 := ⟨n / 6, by omega⟩
    exact lower_F3 m
