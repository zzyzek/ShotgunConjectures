/-
OEIS A094787 (a(n) = smallest prime p such that p + n is a perfect power
m^k, k ≥ 2), conjecture: every prime occurs in the sequence.

Main theorem `A094787_conjecture`: for every prime q there is n ≥ 1 such that
q is the least prime p with p + n a perfect power (`IsPerfPow y`:
∃ c k, 2 ≤ k ∧ y = c^k).  This is the README result.

Proof.  For m > q put n = m^2 - q.  A prime p < q gives p + n in the window
[m^2 - q + 2, m^2 - 1], strictly between (m-1)^2 and m^2, so it is not a
square; it suffices that the window holds no c^k with k ≥ 3.  Windows of
different m are disjoint, so the "blocked" m ∈ (q, 2^(3t)] inject into pairs
(c, k) with c^k < 2^(6t), k ≥ 3, i.e. c < 2^(2t), k < 6t: at most 6t·4^t of
them.  With t = q + 10, 8^t − q > 6t·4^t, so some m is not blocked.

Not checked: nothing outside Lean.
-/
import Mathlib

/-- y is a perfect power c^k with k ≥ 2. -/
def IsPerfPow (y : ℕ) : Prop := ∃ c k : ℕ, 2 ≤ k ∧ y = c ^ k

/-- The window of m (for the fixed prime q) holds a perfect power. -/
def Blocked (q m : ℕ) : Prop := ∃ y, m ^ 2 - q + 2 ≤ y ∧ y ≤ m ^ 2 - 1 ∧ IsPerfPow y

lemma window_unique {m1 m2 y : ℕ} (h1 : (m1 - 1) ^ 2 < y) (h2 : y < m1 ^ 2)
    (h3 : (m2 - 1) ^ 2 < y) (h4 : y < m2 ^ 2) : m1 = m2 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : m1 ≤ m2 - 1 := by omega
    have : m1 ^ 2 ≤ (m2 - 1) ^ 2 := Nat.pow_le_pow_left this 2
    omega
  · have : m2 ≤ m1 - 1 := by omega
    have : m2 ^ 2 ≤ (m1 - 1) ^ 2 := Nat.pow_le_pow_left this 2
    omega

/-- In the window of m > q ≥ 2, any perfect power is c^k with 2 ≤ c and 3 ≤ k. -/
lemma window_facts {q m y : ℕ} (hq : 2 ≤ q) (hm : q < m) (hy1 : m ^ 2 - q + 2 ≤ y)
    (hy2 : y ≤ m ^ 2 - 1) :
    (m - 1) ^ 2 < y ∧ y < m ^ 2 ∧ ∀ c k, 2 ≤ k → y = c ^ k → 2 ≤ c ∧ 3 ≤ k := by
  have hmq : q < m ^ 2 := by nlinarith
  have hlow : (m - 1) ^ 2 < y := by
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at *
    have : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
    omega
  have hup : y < m ^ 2 := by omega
  refine ⟨hlow, hup, fun c k hk hyc => ⟨?_, ?_⟩⟩
  · by_contra hc
    interval_cases c
    · rw [zero_pow (by omega)] at hyc; omega
    · rw [one_pow] at hyc; omega
  · by_contra hk3
    have : k = 2 := by omega
    subst this
    have h1 : m - 1 < c := by
      by_contra h; push Not at h
      have := Nat.pow_le_pow_left h 2; omega
    have h2 : c < m := by
      by_contra h; push Not at h
      have := Nat.pow_le_pow_left h 2; omega
    omega

open Classical in
lemma card_blocked_le (q M t : ℕ) (hq : 2 ≤ q) (hM : M ^ 2 ≤ 2 ^ (6 * t)) :
    ((Finset.Ioc q M).filter (fun m => Blocked q m)).card ≤ 2 ^ (2 * t) * (6 * t) := by
  classical
  -- Pick, for each blocked m, a pair (c, k) with c^k in its window.
  let f : ℕ → ℕ × ℕ := fun m =>
    if h : Blocked q m then
      (Classical.choose (Classical.choose_spec h).2.2,
        Classical.choose (Classical.choose_spec (Classical.choose_spec h).2.2))
    else (0, 0)
  have fspec : ∀ m, Blocked q m → ∃ y, m ^ 2 - q + 2 ≤ y ∧ y ≤ m ^ 2 - 1 ∧
      2 ≤ (f m).2 ∧ y = (f m).1 ^ (f m).2 := by
    intro m hb
    simp only [f, hb, ↓reduceDIte]
    have hy := Classical.choose_spec hb
    have hc := Classical.choose_spec hy.2.2
    have hk := Classical.choose_spec hc
    exact ⟨_, hy.1, hy.2.1, hk.1, hk.2⟩
  have hT := Finset.card_le_card_of_injOn (s := (Finset.Ioc q M).filter (fun m => Blocked q m))
    (t := Finset.range (2 ^ (2 * t)) ×ˢ Finset.range (6 * t)) f ?_ ?_
  · rwa [Finset.card_product, Finset.card_range, Finset.card_range] at hT
  · intro m hmB
    have hmB2 : m ∈ Finset.Ioc q M ∧ Blocked q m := Finset.mem_filter.1 (Finset.mem_coe.1 hmB)
    obtain ⟨hmS, hb⟩ := hmB2
    obtain ⟨hqm, hmM⟩ := Finset.mem_Ioc.1 hmS
    obtain ⟨y, hy1, hy2, hk, hyc⟩ := fspec m hb
    obtain ⟨_, hyup, hck⟩ := window_facts hq hqm hy1 hy2
    obtain ⟨hc2, hk3⟩ := hck _ _ hk hyc
    have hyM : y < 2 ^ (6 * t) := by
      have : m ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hmM 2
      omega
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    constructor
    · by_contra hc
      push Not at hc
      have h1 : (2 ^ (2 * t)) ^ 3 ≤ (f m).1 ^ 3 := Nat.pow_le_pow_left hc 3
      have h2 : (f m).1 ^ 3 ≤ (f m).1 ^ (f m).2 := Nat.pow_le_pow_right (by omega) hk3
      have h3 : (2 ^ (2 * t)) ^ 3 = 2 ^ (6 * t) := by rw [← pow_mul]; ring_nf
      omega
    · by_contra hk'
      push Not at hk'
      have h1 : 2 ^ (6 * t) ≤ 2 ^ (f m).2 := Nat.pow_le_pow_right (by norm_num) hk'
      have h2 : 2 ^ (f m).2 ≤ (f m).1 ^ (f m).2 := Nat.pow_le_pow_left hc2 _
      omega
  · intro m1 hm1 m2 hm2 heq
    have hm1 : m1 ∈ Finset.Ioc q M ∧ Blocked q m1 := Finset.mem_filter.1 (Finset.mem_coe.1 hm1)
    have hm2 : m2 ∈ Finset.Ioc q M ∧ Blocked q m2 := Finset.mem_filter.1 (Finset.mem_coe.1 hm2)
    rw [Finset.mem_Ioc] at hm1 hm2
    obtain ⟨y1, a1, b1, _, e1⟩ := fspec m1 hm1.2
    obtain ⟨y2, a2, b2, _, e2⟩ := fspec m2 hm2.2
    have hy : y1 = y2 := by rw [e1, e2, heq]
    obtain ⟨l1, u1, _⟩ := window_facts hq hm1.1.1 a1 b1
    obtain ⟨l2, u2, _⟩ := window_facts hq hm2.1.1 a2 b2
    rw [hy] at l1 u1
    exact window_unique l1 u1 l2 u2

open Classical in
theorem exists_unblocked (q : ℕ) (hq : 2 ≤ q) : ∃ m, q < m ∧ ¬ Blocked q m := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, t = q + 10 := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 ^ (2 * t) * 2 ^ t := ⟨_, rfl⟩
  have hM2 : M ^ 2 ≤ 2 ^ (6 * t) := by
    rw [hMdef, ← pow_add, ← pow_mul]; apply le_of_eq; ring_nf
  have hB := card_blocked_le q M t hq hM2
  have hbig : 2 ^ (2 * t) * (6 * t) < M - q := by
    have h2q : q < 2 ^ q := Nat.lt_two_pow_self
    have h10 : 2 ^ t = 2 ^ 10 * 2 ^ q := by rw [ht, pow_add]; ring
    have hlin : 6 * t + q + 1 ≤ 2 ^ t := by rw [h10]; omega
    have hpos : 1 ≤ 2 ^ (2 * t) := Nat.one_le_two_pow
    have : 2 ^ (2 * t) * (6 * t + q + 1) ≤ M := by rw [hMdef]; exact Nat.mul_le_mul_left _ hlin
    have : 2 ^ (2 * t) * (6 * t) + q < 2 ^ (2 * t) * (6 * t + q + 1) := by nlinarith
    omega
  have hScard : (Finset.Ioc q M).card = M - q := Nat.card_Ioc q M
  by_contra hall
  push Not at hall
  have hsub : Finset.Ioc q M ⊆ (Finset.Ioc q M).filter (fun m => Blocked q m) := by
    intro m hm
    exact Finset.mem_filter.2 ⟨hm, hall m (Finset.mem_Ioc.1 hm).1⟩
  have := Finset.card_le_card hsub
  omega

theorem A094787_conjecture (q : ℕ) (hq : q.Prime) :
    ∃ n, 1 ≤ n ∧ IsLeast {p | p.Prime ∧ IsPerfPow (p + n)} q := by
  obtain ⟨m, hqm, hnb⟩ := exists_unblocked q hq.two_le
  have hmq : q < m ^ 2 := by nlinarith
  refine ⟨m ^ 2 - q, by omega, ⟨hq, m, 2, le_rfl, by omega⟩, ?_⟩
  intro p ⟨hp, hpp⟩
  by_contra hlt
  push Not at hlt
  apply hnb
  refine ⟨p + (m ^ 2 - q), ?_, ?_, hpp⟩
  · have := hp.two_le; omega
  · omega
