import Mathlib

/-
OEIS-A182334 (Mathlib). Triangular numbers that differ from a square by 1, in increasing
order with offset 1: a(n) = `Nat.nth IsTerm (n - 1)` where `IsTerm T` says T = k(k+1)/2 for
some k and T = s^2 + 1 or T = s^2 - 1 (written T + 1 = s^2) for some s.
README result: the printed recurrence a(n) = 35a(n-3) - 35a(n-6) + a(n-9) is false at
n = 10 and n = 11 and holds for all n ≥ 12.

Main theorem `A182334_main`:
* the set of terms is infinite (so `Nat.nth` enumerates all of it, increasingly),
* a(1..11) = 0, 1, 3, 10, 15, 120, 325, 528, 4095, 11026, 17955,
* the recurrence fails at n = 10 and n = 11 (as integers),
* the recurrence holds for every n ≥ 12 (as integers).

Proof. With x = 2k+1 the term conditions are x^2 = 8s^2 + 9 and x^2 + 7 = 8s^2. Descent by
the unit 3 - √8, (x, s) ↦ (3x - 8s, 3s - x), lowers s and stays in ℕ for s ≥ 3, so every
solution is an image of a small one under step (x, s) ↦ (3x + 8s, x + 3s): the orbits W of
(3, 0) (for +9), U of (1, 1) and V of (5, 2) (for -7). T = x^2 / 8. The step map has positive
coefficients, so W m < U m < V m < W (m+1) in both coordinates for m ≥ 1 (base case by
evaluation); with U 0 < W 0 < V 0 < W 1 this gives the explicit increasing enumeration `g`
(g 0 = U 0, g 1 = W 0, then V 0, W 1, U 1, V 1, W 2, ...), which is `Nat.nth` by Mathlib's
uniqueness lemma. Along one orbit T satisfies T(j+3) = 35T(j+2) - 35T(j+1) + T(j)
(polynomial identity); n = 12 uses V 0..V 3, while n = 10, 11 would need W 0, U 0 in the
swapped first two places.

Outside Lean: nothing.
-/

/-- T is a term of A182334: triangular, and equal to s^2 + 1 or s^2 - 1 for some s. -/
def IsTerm (T : ℕ) : Prop :=
  (∃ k, T = k * (k + 1) / 2) ∧ ∃ s, T = s ^ 2 + 1 ∨ T + 1 = s ^ 2

/-- a(n), offset 1: the n-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Multiplication by the unit 3 + √8 on (x, s) ↔ x + s√8. -/
def step (p : ℕ × ℕ) : ℕ × ℕ := (3 * p.1 + 8 * p.2, p.1 + 3 * p.2)

def orb (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => p
  | j + 1 => step (orb p j)

def W : ℕ → ℕ × ℕ := orb (3, 0)
def U : ℕ → ℕ × ℕ := orb (1, 1)
def V : ℕ → ℕ × ℕ := orb (5, 2)

/-- The term belonging to a solution (x, s): T = (x^2 - 1)/8 = x^2 / 8. -/
def val (p : ℕ × ℕ) : ℕ := p.1 ^ 2 / 8

def orbSeq (r : ℕ) : ℕ → ℕ × ℕ := if r = 0 then W else if r = 1 then U else V

/-- The explicit enumeration (0-indexed). -/
def g (n : ℕ) : ℕ :=
  if n = 0 then val (U 0) else if n = 1 then val (W 0) else val (orbSeq (n % 3) (n / 3))

/-! ### Norm equations along the orbits -/

theorem step_eq9 {x y : ℕ} (h : x ^ 2 = 8 * y ^ 2 + 9) :
    (step (x, y)).1 ^ 2 = 8 * (step (x, y)).2 ^ 2 + 9 := by
  simp only [step]; ring_nf; ring_nf at h; nlinarith [h]

theorem step_eq7 {x y : ℕ} (h : x ^ 2 + 7 = 8 * y ^ 2) :
    (step (x, y)).1 ^ 2 + 7 = 8 * (step (x, y)).2 ^ 2 := by
  simp only [step]; ring_nf; ring_nf at h; nlinarith [h]

theorem W_eq (j : ℕ) : (W j).1 ^ 2 = 8 * (W j).2 ^ 2 + 9 := by
  induction j with
  | zero => decide
  | succ j ih => exact step_eq9 ih

theorem orb_eq7 (p : ℕ × ℕ) (hp : p.1 ^ 2 + 7 = 8 * p.2 ^ 2) (j : ℕ) :
    (orb p j).1 ^ 2 + 7 = 8 * (orb p j).2 ^ 2 := by
  induction j with
  | zero => exact hp
  | succ j ih => exact step_eq7 ih

theorem U_eq (j : ℕ) : (U j).1 ^ 2 + 7 = 8 * (U j).2 ^ 2 := orb_eq7 _ (by decide) j
theorem V_eq (j : ℕ) : (V j).1 ^ 2 + 7 = 8 * (V j).2 ^ 2 := orb_eq7 _ (by decide) j

/-! ### Descent: every solution lies on one of the three orbits -/

theorem desc9 : ∀ y x : ℕ, x ^ 2 = 8 * y ^ 2 + 9 → ∃ j, (x, y) = W j := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro x h
  rcases Nat.lt_or_ge y 3 with hy | hy
  · interval_cases y
    · have hx : x = 3 := by nlinarith
      exact ⟨0, by rw [hx]; rfl⟩
    · have : x < 5 := by nlinarith
      interval_cases x <;> omega
    · have : x < 7 := by nlinarith
      interval_cases x <;> omega
  · have h1 : 8 * y ≤ 3 * x := by
      by_contra hc; push Not at hc; nlinarith [Nat.mul_lt_mul'' hc hc]
    have h2 : x ≤ 3 * y := by
      by_contra hc; push Not at hc; nlinarith [Nat.mul_lt_mul'' hc hc]
    obtain ⟨x', y', hx, hy'⟩ : ∃ x' y', x = 3 * x' + 8 * y' ∧ y = x' + 3 * y' :=
      ⟨3 * x - 8 * y, 3 * y - x, by omega, by omega⟩
    subst hx hy'
    have h' : x' ^ 2 = 8 * y' ^ 2 + 9 := by ring_nf at h; nlinarith [h]
    have hlt : y' < x' + 3 * y' := by
      rcases Nat.eq_zero_or_pos x' with h0 | h0
      · subst h0; nlinarith
      · omega
    obtain ⟨j, hj⟩ := ih y' hlt x' h'
    refine ⟨j + 1, ?_⟩
    show _ = step (W j)
    rw [← hj]; rfl

theorem desc7 : ∀ y x : ℕ, x ^ 2 + 7 = 8 * y ^ 2 → ∃ j, (x, y) = U j ∨ (x, y) = V j := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro x h
  rcases Nat.lt_or_ge y 3 with hy | hy
  · interval_cases y
    · omega
    · have hx : x = 1 := by nlinarith
      exact ⟨0, Or.inl (by rw [hx]; rfl)⟩
    · have hx : x = 5 := by nlinarith
      exact ⟨0, Or.inr (by rw [hx]; rfl)⟩
  · have h1 : 8 * y ≤ 3 * x := by
      by_contra hc; push Not at hc; nlinarith [Nat.mul_lt_mul'' hc hc]
    have h2 : x ≤ 3 * y := by
      by_contra hc; push Not at hc; nlinarith [Nat.mul_lt_mul'' hc hc]
    obtain ⟨x', y', hx, hy'⟩ : ∃ x' y', x = 3 * x' + 8 * y' ∧ y = x' + 3 * y' :=
      ⟨3 * x - 8 * y, 3 * y - x, by omega, by omega⟩
    subst hx hy'
    have h' : x' ^ 2 + 7 = 8 * y' ^ 2 := by ring_nf at h; nlinarith [h]
    have hlt : y' < x' + 3 * y' := by
      rcases Nat.eq_zero_or_pos y' with h0 | h0
      · subst h0; nlinarith
      · omega
    obtain ⟨j, hj | hj⟩ := ih y' hlt x' h'
    · refine ⟨j + 1, Or.inl ?_⟩
      show _ = step (U j)
      rw [← hj]; rfl
    · refine ⟨j + 1, Or.inr ?_⟩
      show _ = step (V j)
      rw [← hj]; rfl

/-! ### Order of the orbits -/

abbrev Lt2 (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∧ p.2 < q.2

theorem step_mono {p q : ℕ × ℕ} (h : Lt2 p q) : Lt2 (step p) (step q) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by simp only [step]; omega, by simp only [step]; omega⟩

theorem chain (m : ℕ) :
    Lt2 (W (m + 1)) (U (m + 1)) ∧ Lt2 (U (m + 1)) (V (m + 1)) ∧ Lt2 (V (m + 1)) (W (m + 2)) := by
  induction m with
  | zero => decide
  | succ m ih =>
    exact ⟨step_mono ih.1, step_mono ih.2.1, step_mono ih.2.2⟩

theorem val_lt {p q : ℕ × ℕ} (hp : 8 * val p + 1 = p.1 ^ 2) (hq : 8 * val q + 1 = q.1 ^ 2)
    (h : p.1 < q.1) : val p < val q := by
  have := Nat.mul_lt_mul'' h h
  nlinarith

/-! ### Terms from solutions -/

theorem spec9 {p : ℕ × ℕ} (h : p.1 ^ 2 = 8 * p.2 ^ 2 + 9) :
    8 * val p + 1 = p.1 ^ 2 ∧ val p = p.2 ^ 2 + 1 := by
  unfold val; generalize p.1 ^ 2 = X at *; generalize p.2 ^ 2 = Y at *; omega

theorem spec7 {p : ℕ × ℕ} (h : p.1 ^ 2 + 7 = 8 * p.2 ^ 2) :
    8 * val p + 1 = p.1 ^ 2 ∧ val p + 1 = p.2 ^ 2 := by
  unfold val; generalize p.1 ^ 2 = X at *; generalize p.2 ^ 2 = Y at *; omega

theorem orb_parity (p : ℕ × ℕ) (j : ℕ) : (orb p j).1 % 2 = p.1 % 2 := by
  induction j with
  | zero => rfl
  | succ j ih => show (3 * (orb p j).1 + 8 * (orb p j).2) % 2 = _; omega

theorem isTerm_of {p : ℕ × ℕ} (hodd : p.1 % 2 = 1) (h8 : 8 * val p + 1 = p.1 ^ 2)
    (hs : ∃ s, val p = s ^ 2 + 1 ∨ val p + 1 = s ^ 2) : IsTerm (val p) := by
  refine ⟨⟨p.1 / 2, ?_⟩, hs⟩
  obtain ⟨k, hk⟩ : ∃ k, p.1 = 2 * k + 1 := ⟨p.1 / 2, by omega⟩
  have e : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [hk, e] at h8
  rw [hk, show (2 * k + 1) / 2 = k by omega]
  generalize k * (k + 1) = P at *
  omega

theorem W_term (j : ℕ) : IsTerm (val (W j)) :=
  isTerm_of (by rw [W, orb_parity]; rfl) (spec9 (W_eq j)).1 ⟨_, Or.inl (spec9 (W_eq j)).2⟩
theorem U_term (j : ℕ) : IsTerm (val (U j)) :=
  isTerm_of (by rw [U, orb_parity]; rfl) (spec7 (U_eq j)).1 ⟨_, Or.inr (spec7 (U_eq j)).2⟩
theorem V_term (j : ℕ) : IsTerm (val (V j)) :=
  isTerm_of (by rw [V, orb_parity]; rfl) (spec7 (V_eq j)).1 ⟨_, Or.inr (spec7 (V_eq j)).2⟩

/-! ### The enumeration `g` -/

theorem g_eq (m r : ℕ) (hr : r < 3) (h2 : 2 ≤ 3 * m + r) :
    g (3 * m + r) = val (orbSeq r m) := by
  unfold g
  simp only [show ¬(3 * m + r = 0) from by omega, show ¬(3 * m + r = 1) from by omega,
    ↓reduceIte]
  rw [show (3 * m + r) % 3 = r by omega,
    show (3 * m + r) / 3 = m by omega]

theorem g_mem (n : ℕ) : IsTerm (g n) := by
  unfold g
  split_ifs
  · exact U_term 0
  · exact W_term 0
  · unfold orbSeq
    split_ifs
    · exact W_term _
    · exact U_term _
    · exact V_term _

theorem g_succ (n : ℕ) : g n < g (n + 1) := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ n = 3 * m + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
  · interval_cases r <;> decide
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hc := chain m'
    interval_cases r
    · rw [g_eq (m' + 1) 0 (by norm_num) (by omega), show 3 * (m' + 1) + 0 + 1 = 3 * (m' + 1) + 1
        by ring, g_eq (m' + 1) 1 (by norm_num) (by omega)]
      exact val_lt (spec9 (W_eq _)).1 (spec7 (U_eq _)).1 hc.1.1
    · rw [g_eq (m' + 1) 1 (by norm_num) (by omega), show 3 * (m' + 1) + 1 + 1 = 3 * (m' + 1) + 2
        by ring, g_eq (m' + 1) 2 (by norm_num) (by omega)]
      exact val_lt (spec7 (U_eq _)).1 (spec7 (V_eq _)).1 hc.2.1.1
    · rw [g_eq (m' + 1) 2 (by norm_num) (by omega), show 3 * (m' + 1) + 2 + 1 = 3 * (m' + 2) + 0
        by ring, g_eq (m' + 2) 0 (by norm_num) (by omega)]
      exact val_lt (spec7 (V_eq _)).1 (spec9 (W_eq _)).1 hc.2.2.1

theorem g_strictMono : StrictMono g := strictMono_nat_of_lt_succ g_succ

theorem g_surj (T : ℕ) (h : IsTerm T) : ∃ n, g n = T := by
  obtain ⟨⟨k, hk⟩, s, hs⟩ := h
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self k
  have hx : (2 * k + 1) ^ 2 = 8 * T + 1 := by
    rw [show (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 by ring]
    generalize k * (k + 1) = P at *
    omega
  have hval : ∀ p : ℕ × ℕ, p.1 = 2 * k + 1 → val p = T := by
    intro p hp
    unfold val
    rw [hp, hx]
    omega
  have hW : ∀ j, ∃ n, g n = val (W j) := by
    intro j
    rcases j with _ | j
    · exact ⟨1, rfl⟩
    · exact ⟨3 * (j + 1) + 0, g_eq _ _ (by norm_num) (by omega)⟩
  have hU : ∀ j, ∃ n, g n = val (U j) := by
    intro j
    rcases j with _ | j
    · exact ⟨0, rfl⟩
    · exact ⟨3 * (j + 1) + 1, g_eq _ _ (by norm_num) (by omega)⟩
  have hV : ∀ j, ∃ n, g n = val (V j) :=
    fun j => ⟨3 * j + 2, g_eq _ _ (by norm_num) (by omega)⟩
  rcases hs with hs | hs
  · have e : (2 * k + 1) ^ 2 = 8 * s ^ 2 + 9 := by
      rw [hx, hs]; ring
    obtain ⟨j, hj⟩ := desc9 s _ e
    obtain ⟨n, hn⟩ := hW j
    exact ⟨n, hn.trans (hval _ (by rw [← hj]))⟩
  · have e : (2 * k + 1) ^ 2 + 7 = 8 * s ^ 2 := by
      rw [hx, ← hs]; ring
    obtain ⟨j, hj | hj⟩ := desc7 s _ e
    · obtain ⟨n, hn⟩ := hU j
      exact ⟨n, hn.trans (hval _ (by rw [← hj]))⟩
    · obtain ⟨n, hn⟩ := hV j
      exact ⟨n, hn.trans (hval _ (by rw [← hj]))⟩

theorem range_g : Set.range g = {T | IsTerm T} := by
  ext T
  constructor
  · rintro ⟨n, rfl⟩
    exact g_mem n
  · intro h
    exact g_surj T h

theorem terms_infinite : {T | IsTerm T}.Infinite := by
  rw [← range_g]
  exact Set.infinite_range_of_injective g_strictMono.injective

theorem nth_eq (n : ℕ) : Nat.nth IsTerm n = g n := by
  have hall : ∀ m : ℕ, m ∈ {m : ℕ | ∀ hf : (Set.ofPred IsTerm).Finite, m < hf.toFinset.card} :=
    fun m hf => absurd hf terms_infinite
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn g ?_ ?_
    (g_strictMono.strictMonoOn _) (hall n)).symm
  · intro T hT
    obtain ⟨m, hm⟩ := g_surj T hT
    exact ⟨m, hall m, hm⟩
  · intro m _
    exact g_mem m

/-! ### The recurrence along one orbit -/

theorem orb_rec (p : ℕ × ℕ) (hs : ∀ j, 8 * val (orb p j) + 1 = (orb p j).1 ^ 2) (j : ℕ) :
    (val (orb p (j + 3)) : ℤ) =
      35 * val (orb p (j + 2)) - 35 * val (orb p (j + 1)) + val (orb p j) := by
  have h0 := hs j
  have h1 := hs (j + 1)
  have h2 := hs (j + 2)
  have h3 := hs (j + 3)
  have e1 : (orb p (j + 1)).1 = 3 * (orb p j).1 + 8 * (orb p j).2 := rfl
  have e2 : (orb p (j + 2)).1 = 17 * (orb p j).1 + 48 * (orb p j).2 := by
    show 3 * (3 * (orb p j).1 + 8 * (orb p j).2) + 8 * ((orb p j).1 + 3 * (orb p j).2) = _
    ring
  have e3 : (orb p (j + 3)).1 = 99 * (orb p j).1 + 280 * (orb p j).2 := by
    show 3 * (3 * (3 * (orb p j).1 + 8 * (orb p j).2) + 8 * ((orb p j).1 + 3 * (orb p j).2)) +
      8 * ((3 * (orb p j).1 + 8 * (orb p j).2) + 3 * ((orb p j).1 + 3 * (orb p j).2)) = _
    ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  generalize (orb p j).1 = x at *
  generalize (orb p j).2 = y at *
  generalize val (orb p j) = v0 at *
  generalize val (orb p (j + 1)) = v1 at *
  generalize val (orb p (j + 2)) = v2 at *
  generalize val (orb p (j + 3)) = v3 at *
  have h0' : (8 * v0 + 1 : ℤ) = (x : ℤ) ^ 2 := by exact_mod_cast h0
  have h1' : (8 * v1 + 1 : ℤ) = (3 * x + 8 * y : ℤ) ^ 2 := by exact_mod_cast h1
  have h2' : (8 * v2 + 1 : ℤ) = (17 * x + 48 * y : ℤ) ^ 2 := by exact_mod_cast h2
  have h3' : (8 * v3 + 1 : ℤ) = (99 * x + 280 * y : ℤ) ^ 2 := by exact_mod_cast h3
  have : (8 : ℤ) * (v3 - (35 * v2 - 35 * v1 + v0)) = 0 := by
    linear_combination h3' - 35 * h2' + 35 * h1' - h0'
  omega

theorem orbSeq_rec (r j : ℕ) :
    (val (orbSeq r (j + 3)) : ℤ) =
      35 * val (orbSeq r (j + 2)) - 35 * val (orbSeq r (j + 1)) + val (orbSeq r j) := by
  unfold orbSeq
  split_ifs
  · exact orb_rec _ (fun j => (spec9 (W_eq j)).1) j
  · exact orb_rec _ (fun j => (spec7 (U_eq j)).1) j
  · exact orb_rec _ (fun j => (spec7 (V_eq j)).1) j

/-! ### Main theorem -/

theorem A182334_main :
    {T | IsTerm T}.Infinite ∧
    (a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 3 ∧ a 4 = 10 ∧ a 5 = 15 ∧ a 6 = 120 ∧ a 7 = 325 ∧
      a 8 = 528 ∧ a 9 = 4095 ∧ a 10 = 11026 ∧ a 11 = 17955) ∧
    (a 10 : ℤ) ≠ 35 * a 7 - 35 * a 4 + a 1 ∧
    (a 11 : ℤ) ≠ 35 * a 8 - 35 * a 5 + a 2 ∧
    ∀ n, 12 ≤ n → (a n : ℤ) = 35 * a (n - 3) - 35 * a (n - 6) + a (n - 9) := by
  have ha : ∀ n, a n = g (n - 1) := fun n => nth_eq _
  refine ⟨terms_infinite, ?_, ?_, ?_, ?_⟩
  · simp only [ha]; decide
  · simp only [ha]; decide
  · simp only [ha]; decide
  · intro n hn
    simp only [ha]
    obtain ⟨j, r, hr, hi⟩ : ∃ j r, r < 3 ∧ n - 1 = 3 * (j + 3) + r :=
      ⟨(n - 1) / 3 - 3, (n - 1) % 3, Nat.mod_lt _ (by norm_num), by omega⟩
    have hj : 2 ≤ 3 * j + r := by omega
    rw [hi, show n - 3 - 1 = 3 * (j + 2) + r by omega, show n - 6 - 1 = 3 * (j + 1) + r by omega,
      show n - 9 - 1 = 3 * j + r by omega, g_eq _ _ hr (by omega), g_eq _ _ hr (by omega),
      g_eq _ _ hr (by omega), g_eq _ _ hr hj]
    exact orbSeq_rec r j
