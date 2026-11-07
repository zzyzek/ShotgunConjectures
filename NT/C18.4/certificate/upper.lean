
/-! Upper bound (Monsky): no n - 1 non-attacking queens when 3 ∣ n or 4 ∣ n. -/

theorem sum_zmod {n : ℕ} [NeZero n] {R : Type} [AddCommMonoid R] (g : ZMod n → R) :
    ∑ v, g v = ∑ i ∈ Finset.range n, g (i : ZMod n) := by
  refine (Finset.sum_nbij' (s := Finset.range n) (t := Finset.univ)
    (f := fun i => g (i : ZMod n)) (g := g) (fun i => (i : ZMod n)) (fun v => v.val)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro i _; simp
  · intro v _; simp [ZMod.val_lt]
  · intro i hi; rw [Finset.mem_range] at hi; exact ZMod.val_cast_of_lt hi
  · intro v _; simp
  · intro i _; rfl

/-- If f is injective on S and |S| = n - 1, the image misses exactly one value a. -/
theorem miss {n : ℕ} [NeZero n] {α : Type} [DecidableEq α] (S : Finset α) (f : α → ZMod n)
    (hf : Set.InjOn f S) (hc : S.card + 1 = n) :
    ∃ a : ZMod n, ∀ {R : Type} [AddCommGroup R] (g : ZMod n → R),
      ∑ p ∈ S, g (f p) = (∑ v, g v) - g a := by
  classical
  have hI : (S.image f).card = S.card := Finset.card_image_of_injOn hf
  have hcc : (S.image f)ᶜ.card = 1 := by
    rw [Finset.card_compl, hI, ZMod.card]; omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcc
  refine ⟨a, fun {R} _ g => ?_⟩
  rw [← Finset.sum_image (f := g) hf, ← Finset.sum_compl_add_sum (S.image f), ha,
    Finset.sum_singleton]
  abel

theorem six_sum_sq (N : ℕ) : 6 * ∑ i ∈ Finset.range (N + 1), i ^ 2 = N * (N + 1) * (2 * N + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

theorem sq_lift {n : ℕ} (hn : 2 ∣ n) (u w : ℤ) (h : ((u : ZMod n)) = (w : ZMod n)) :
    ((u : ZMod (2 * n))) ^ 2 = (w : ZMod (2 * n)) ^ 2 := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  obtain ⟨r, rfl⟩ := hn
  have : ((u : ZMod (2 * (2 * r)))) = (w : ZMod (2 * (2 * r))) + ((2 * r : ℕ) : ℤ) * (-k) := by
    have : u = w + ((2 * r : ℕ) : ℤ) * (-k) := by push_cast at hk ⊢; linarith
    rw [this]; push_cast; ring
  rw [this]
  have h0 : ((2 * (2 * r) : ℕ) : ZMod (2 * (2 * r))) = 0 := ZMod.natCast_self _
  have : ((w : ZMod (2 * (2 * r))) + ((2 * r : ℕ) : ℤ) * (-k)) ^ 2 =
      (w : ZMod (2 * (2 * r))) ^ 2 + ((2 * (2 * r) : ℕ) : ZMod (2 * (2 * r))) * (w * (-k) + r * k ^ 2) := by
    push_cast; ring
  rw [this, h0, zero_mul, add_zero]

theorem no_n_minus_one (n : ℕ) (hn : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n)
    (S : Finset (ZMod n × ZMod n)) (hS : NonAttacking S) (hc : S.card + 1 = n) : False := by
  classical
  have : NeZero n := ⟨by omega⟩
  have inj : ∀ (f : ZMod n × ZMod n → ZMod n), (∀ p ∈ S, ∀ q ∈ S, p ≠ q → f p ≠ f q) →
      Set.InjOn f S := by
    intro f hf p hp q hq hpq
    by_contra hne; exact hf p hp q hq hne hpq
  obtain ⟨a, ha⟩ := miss S (fun p => p.1) (inj _ fun p hp q hq h => (hS p hp q hq h).1) hc
  obtain ⟨b, hb⟩ := miss S (fun p => p.2) (inj _ fun p hp q hq h => (hS p hp q hq h).2.1) hc
  obtain ⟨c, hc'⟩ := miss S (fun p => p.1 + p.2)
    (inj _ fun p hp q hq h => (hS p hp q hq h).2.2.1) hc
  obtain ⟨d, hd'⟩ := miss S (fun p => p.2 - p.1)
    (inj _ fun p hp q hq h => (hS p hp q hq h).2.2.2) hc
  set T : ZMod n := ∑ v, v with hTdef
  have hT : T + T = 0 := by
    have : T = -T := by
      rw [hTdef, ← Finset.sum_neg_distrib]
      exact (Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun v => by simp)).symm
    calc T + T = T + -T := by rw [← this]
      _ = 0 := add_neg_cancel T
  -- linear relations between the missing values
  have l1 := ha (fun v => v); have l2 := hb (fun v => v)
  have l3 := hc' (fun v => v); have l4 := hd' (fun v => v)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at l1 l2 l3 l4
  have hcab : c = a + b - T := by rw [l1, l2] at l3; linear_combination l3
  have hdab : d = T - a + b := by rw [l1, l2] at l4; linear_combination l4
  rcases hd with h3 | h4
  · -- squares in ZMod n
    have s1 := ha (fun v => v ^ 2); have s2 := hb (fun v => v ^ 2)
    have s3 := hc' (fun v => v ^ 2); have s4 := hd' (fun v => v ^ 2)
    have par : ∑ p ∈ S, (p.1 + p.2) ^ 2 + ∑ p ∈ S, (p.2 - p.1) ^ 2 =
        2 * ∑ p ∈ S, p.1 ^ 2 + 2 * ∑ p ∈ S, p.2 ^ 2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [s1, s2, s3, s4, hcab, hdab] at par
    have hQ : 2 * ∑ v : ZMod n, v ^ 2 = 0 := by
      linear_combination -par - (T - 2 * a) * hT
    rw [sum_zmod (fun v : ZMod n => v ^ 2)] at hQ
    have hcast : (2 * ∑ i ∈ Finset.range n, (i : ZMod n) ^ 2) =
        ((2 * ∑ i ∈ Finset.range n, i ^ 2 : ℕ) : ZMod n) := by push_cast; rfl
    rw [hcast, ZMod.natCast_eq_zero_iff] at hQ
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    obtain ⟨j, hj⟩ := hQ
    have h6 := six_sum_sq N
    have : (N + 1) * (3 * j) = (N + 1) * (N * (2 * N + 1)) := by
      have : 3 * (2 * ∑ i ∈ Finset.range (N + 1), i ^ 2) = 3 * ((N + 1) * j) := by rw [hj]
      nlinarith
    have h3j := Nat.eq_of_mul_eq_mul_left (by omega) this
    have hN : N % 3 = 2 := by omega
    have : (N * (2 * N + 1)) % 3 = 1 := by
      rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod 2, hN]
    omega
  · -- squares of lifts in ZMod (2n)
    have h2 : 2 ∣ n := dvd_trans ⟨2, rfl⟩ h4
    let L : ZMod n → ZMod (2 * n) := fun v => ((v.val : ℤ) : ZMod (2 * n))
    have Lsq : ∀ (v : ZMod n) (w : ℤ), (w : ZMod n) = v → L v ^ 2 = (w : ZMod (2 * n)) ^ 2 := by
      intro v w h
      exact sq_lift h2 _ _ (by rw [h]; simp)
    have s1 := ha (fun v => L v ^ 2); have s2 := hb (fun v => L v ^ 2)
    have s3 := hc' (fun v => L v ^ 2); have s4 := hd' (fun v => L v ^ 2)
    have par : ∑ p ∈ S, L (p.1 + p.2) ^ 2 + ∑ p ∈ S, L (p.2 - p.1) ^ 2 =
        2 * ∑ p ∈ S, L p.1 ^ 2 + 2 * ∑ p ∈ S, L p.2 ^ 2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Lsq (p.1 + p.2) ((p.1.val : ℤ) + p.2.val) (by push_cast; simp),
        Lsq (p.2 - p.1) ((p.2.val : ℤ) - p.1.val) (by push_cast; simp)]
      simp only [L]; push_cast; ring
    have hc2 : L c ^ 2 = (L a + L b - L T) ^ 2 := by
      rw [Lsq c ((a.val : ℤ) + b.val - T.val) (by push_cast; simp [hcab])]
      simp only [L]; push_cast; ring
    have hd2 : L d ^ 2 = (L T - L a + L b) ^ 2 := by
      rw [Lsq d ((T.val : ℤ) - a.val + b.val) (by push_cast; simp [hdab])]
      simp only [L]; push_cast; ring
    rw [s1, s2, s3, s4, hc2, hd2] at par
    -- T.val is 0 or n/2
    obtain ⟨k, rfl⟩ := h4
    have hk0 : 1 ≤ k := by omega
    have hTv : T.val = 0 ∨ T.val = 2 * k := by
      have h0 : ((2 * T.val : ℕ) : ZMod (4 * k)) = 0 := by
        push_cast; rw [ZMod.natCast_zmod_val]; linear_combination hT
      rw [ZMod.natCast_eq_zero_iff] at h0
      obtain ⟨j, hj⟩ := h0
      have hlt : T.val < 4 * k := ZMod.val_lt T
      have hj2 : j < 2 := by nlinarith
      interval_cases j <;> omega
    have hQ : 2 * ∑ v : ZMod (4 * k), L v ^ 2 = 0 := by
      have h0 : ((2 * (4 * k) : ℕ) : ZMod (2 * (4 * k))) = 0 := ZMod.natCast_self _
      rcases hTv with ht | ht
      · have hLT : L T = 0 := by simp only [L]; rw [ht]; simp
        rw [hLT] at par; linear_combination -par
      · have hLT : L T = ((2 * k : ℕ) : ZMod (2 * (4 * k))) := by simp only [L]; rw [ht]; simp
        rw [hLT] at par
        have e : (2 : ZMod (2 * (4 * k))) * ((2 * k : ℕ) : ZMod (2 * (4 * k))) ^ 2 -
            4 * L a * ((2 * k : ℕ) : ZMod (2 * (4 * k))) =
            ((2 * (4 * k) : ℕ) : ZMod (2 * (4 * k))) * (k - L a) := by push_cast; ring
        rw [h0, zero_mul] at e
        linear_combination -par - e
    rw [sum_zmod (fun v : ZMod (4 * k) => L v ^ 2)] at hQ
    have hL : ∀ i ∈ Finset.range (4 * k), L (i : ZMod (4 * k)) ^ 2 = ((i ^ 2 : ℕ) : ZMod (2 * (4 * k))) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [L]; rw [ZMod.val_cast_of_lt hi]; push_cast; ring
    rw [Finset.sum_congr rfl hL] at hQ
    have hcast : (2 * ∑ i ∈ Finset.range (4 * k), ((i ^ 2 : ℕ) : ZMod (2 * (4 * k)))) =
        ((2 * ∑ i ∈ Finset.range (4 * k), i ^ 2 : ℕ) : ZMod (2 * (4 * k))) := by push_cast; rfl
    rw [hcast, ZMod.natCast_eq_zero_iff] at hQ
    obtain ⟨j, hj⟩ := hQ
    obtain ⟨N, hN⟩ : ∃ N, 4 * k = N + 1 := ⟨4 * k - 1, by omega⟩
    have h6 := six_sum_sq N
    rw [hN] at hj
    have : (N + 1) * (6 * j) = (N + 1) * (N * (2 * N + 1)) := by nlinarith
    have h6j := Nat.eq_of_mul_eq_mul_left (by omega) this
    have hN2 : N % 2 = 1 := by omega
    have : (N * (2 * N + 1)) % 2 = 1 := by
      rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod 2, hN2]
    omega

/-- Monsky's upper bound: at most n - 2 non-attacking queens on the n × n torus when 3 ∣ n or
4 ∣ n. -/
theorem queens_upper (n : ℕ) (hn : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n)
    (S : Finset (ZMod n × ZMod n)) (hS : NonAttacking S) : S.card ≤ n - 2 := by
  by_contra h
  obtain ⟨S', hsub, hcard⟩ := Finset.exists_subset_card_eq (show n - 1 ≤ S.card by omega)
  exact no_n_minus_one n hn hd S' (fun p hp q hq => hS p (hsub hp) q (hsub hq)) (by omega)

/-- M(n) = n - 2 when 3 ∣ n or 4 ∣ n: n - 2 non-attacking queens exist and no larger set does. -/
theorem modular_queens_eq (n : ℕ) (hn : 3 ≤ n) (hd : 3 ∣ n ∨ 4 ∣ n) :
    (∃ S : Finset (ZMod n × ZMod n), S.card = n - 2 ∧ NonAttacking S) ∧
    ∀ S : Finset (ZMod n × ZMod n), NonAttacking S → S.card ≤ n - 2 :=
  ⟨queens_lower n hn hd, fun S hS => queens_upper n hn hd S hS⟩
