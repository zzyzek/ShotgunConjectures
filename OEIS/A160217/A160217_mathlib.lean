/-
OEIS A160217: minimal increasing sequence with a(1) = 3 and the property that a(n) and n are
both in or both not in A003159 (numbers whose 2-adic valuation is even).
Conjecture (Vladimir Shevelev): for every m > 3 in A003159, the minimal increasing sequence b
with b(1) = m and the same property agrees with a(n) for all large n.

Checked here (Mathlib): `A160217_conjecture`. `chi x` is membership in A003159
(padicValNat 2 x even); `nxt x c` is the least y > x with chi y = c; `gseq m 1 = m`,
`gseq m (n+1) = nxt (gseq m n) (chi (n+1))` (n >= 1); A160217 = gseq 3.
Also `A160217_formula`: a(n) = 2n+1 if chi n, else 2n+2. Nothing is outside Lean.
-/
import Mathlib

def chi (x : ℕ) : Bool := decide (padicValNat 2 x % 2 = 0)

lemma chi_odd {x : ℕ} (h : x % 2 = 1) : chi x = true := by
  have : padicValNat 2 x = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  simp [chi, this]

lemma chi_two_mul {y : ℕ} (hy : y ≠ 0) : chi (2 * y) = !chi y := by
  have : padicValNat 2 (2 * y) = 1 + padicValNat 2 y := by
    rw [padicValNat.mul two_ne_zero hy, padicValNat.self one_lt_two]
  simp only [chi, this]
  by_cases h : padicValNat 2 y % 2 = 0 <;> simp [h] <;> omega

lemma chi_pow_mul_odd {w : ℕ} (hw : w % 2 = 1) (k : ℕ) :
    chi (2 ^ k * w) = decide (k % 2 = 0) := by
  induction k with
  | zero => simp [chi_odd hw]
  | succ k ih =>
    rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, chi_two_mul (Nat.mul_ne_zero (by positivity) (by omega)), ih]
    by_cases h : k % 2 = 0 <;> simp [h] <;> omega

lemma chi_mod4_two {x : ℕ} (h : x % 4 = 2) : chi x = false := by
  obtain ⟨w, rfl⟩ : ∃ w, x = 2 * w := ⟨x / 2, by omega⟩
  rw [chi_two_mul (by omega), chi_odd (by omega)]; rfl

lemma chi_even_true {x : ℕ} (h0 : x ≠ 0) (h2 : x % 2 = 0) (hc : chi x = true) : x % 4 = 0 := by
  obtain ⟨w, rfl⟩ : ∃ w, x = 2 * w := ⟨x / 2, by omega⟩
  rw [chi_two_mul (by omega)] at hc
  by_contra hne
  have : w % 2 = 1 := by omega
  rw [chi_odd this] at hc; simp at hc

lemma nxt_exists (x : ℕ) (c : Bool) : ∃ y, x < y ∧ chi y = c := by
  cases c
  · exact ⟨2 * (2 * x + 1), by omega, by rw [chi_two_mul (by omega), chi_odd (by omega)]; rfl⟩
  · exact ⟨2 * x + 1, by omega, chi_odd (by omega)⟩

noncomputable def nxt (x : ℕ) (c : Bool) : ℕ := Nat.find (nxt_exists x c)

lemma nxt_spec (x : ℕ) (c : Bool) : x < nxt x c ∧ chi (nxt x c) = c :=
  Nat.find_spec (nxt_exists x c)

lemma nxt_le {x y : ℕ} {c : Bool} (h : x < y) (hc : chi y = c) : nxt x c ≤ y :=
  Nat.find_min' (nxt_exists x c) ⟨h, hc⟩

lemma nxt_eq {x y : ℕ} {c : Bool} (h : x < y) (hc : chi y = c)
    (hmin : ∀ z, x < z → z < y → chi z ≠ c) : nxt x c = y := by
  apply le_antisymm (nxt_le h hc)
  by_contra hlt
  push Not at hlt
  exact hmin _ (nxt_spec x c).1 hlt (nxt_spec x c).2

lemma nxt_mono {x y : ℕ} (c : Bool) (h : x ≤ y) : nxt x c ≤ nxt y c :=
  nxt_le (lt_of_le_of_lt h (nxt_spec y c).1) (nxt_spec y c).2

/-- Advance bounds: from a member, the next member is within 2 and the next non-member within 3;
from a non-member, the next member is the successor. -/
lemma adv_tt {x : ℕ} : nxt x true ≤ x + 2 := by
  rcases Nat.even_or_odd x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact le_trans (nxt_le (y := x + 1) (by omega) (chi_odd (by omega))) (by omega)
  · exact nxt_le (y := x + 2) (by omega) (chi_odd (by omega))

lemma adv_tf {x : ℕ} (hx : chi x = true) : nxt x false ≤ x + 3 := by
  by_cases h2 : x % 2 = 0
  · by_cases h0 : x = 0
    · subst h0; exact le_trans (nxt_le (y := 2) (by norm_num) (chi_mod4_two (by norm_num))) (by norm_num)
    · have h4 := chi_even_true h0 h2 hx
      exact le_trans (nxt_le (y := x + 2) (by omega) (chi_mod4_two (by omega))) (by omega)
  · by_cases h3 : (x + 1) % 4 = 2
    · exact le_trans (nxt_le (y := x + 1) (by omega) (chi_mod4_two h3)) (by omega)
    · exact nxt_le (y := x + 3) (by omega) (chi_mod4_two (by omega))

lemma adv_ft {x : ℕ} (hx : chi x = false) : nxt x true = x + 1 := by
  have : x % 2 = 0 := by
    by_contra h
    rw [chi_odd (by omega)] at hx; simp at hx
  exact nxt_eq (y := x + 1) (by omega) (chi_odd (by omega)) (fun z h1 h2 => by omega)

/-- The greedy sequence with b(1) = m (index 0 is a copy of m and is not used). -/
noncomputable def gseq (m : ℕ) : ℕ → ℕ
  | 0 => m
  | (n + 1) => if n = 0 then m else nxt (gseq m n) (chi (n + 1))

lemma gseq_one (m : ℕ) : gseq m 1 = m := by simp [gseq]

lemma gseq_succ (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    gseq m (n + 1) = nxt (gseq m n) (chi (n + 1)) := by
  rw [gseq]; simp [show n ≠ 0 by omega]

/-- A160217(n) = 2n+1 if n is in A003159, else 2n+2. -/
theorem A160217_formula (n : ℕ) (hn : 1 ≤ n) :
    gseq 3 n = if chi n then 2 * n + 1 else 2 * n + 2 := by
  induction n, hn using Nat.le_induction with
  | base => rw [gseq_one, chi_odd (by norm_num)]; rfl
  | succ n hn ih =>
    rw [gseq_succ 3 hn, ih]
    cases hc : chi n
    · -- n even, n+1 odd
      have hev : n % 2 = 0 := by
        by_contra h; rw [chi_odd (by omega)] at hc; simp at hc
      rw [chi_odd (show (n + 1) % 2 = 1 by omega)]
      simp only [Bool.false_eq_true, ite_false, ite_true]
      exact nxt_eq (y := 2 * n + 2 + 1) (by omega) (chi_odd (by omega)) (fun z h1 h2 => by omega)
    · simp only [ite_true]
      cases hc1 : chi (n + 1)
      · simp only [Bool.false_eq_true, ite_false]
        have hev : (n + 1) % 2 = 0 := by
          by_contra h; rw [chi_odd (by omega)] at hc1; simp at hc1
        have h22 : chi (2 * (n + 1)) = true := by rw [chi_two_mul (by omega), hc1]; rfl
        have h24 : chi (2 * (n + 2)) = false := by
          rw [chi_two_mul (by omega), chi_odd (by omega)]; rfl
        refine nxt_eq (y := 2 * (n + 1) + 2) (by omega) (by rw [show 2 * (n + 1) + 2 = 2 * (n + 2) by ring]; exact h24)
          (fun z h1 h2 => ?_)
        rcases (show z = 2 * (n + 1) ∨ z = 2 * n + 3 by omega) with rfl | rfl
        · rw [h22]; simp
        · rw [chi_odd (by omega)]; simp
      · simp only [ite_true]
        have h22 : chi (2 * (n + 1)) = false := by rw [chi_two_mul (by omega), hc1]; rfl
        refine nxt_eq (y := 2 * (n + 1) + 1) (by omega) (chi_odd (by omega)) (fun z h1 h2 => ?_)
        rcases (show z = 2 * (n + 1) by omega) with rfl
        rw [h22]; simp

lemma gseq_chi (m : ℕ) (hm : chi m = true) {n : ℕ} (hn : 1 ≤ n) : chi (gseq m n) = chi n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [gseq_one, hm, chi_odd (by norm_num)]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [gseq_succ m (by omega)]; exact (nxt_spec _ _).2

lemma gseq_ge (m : ℕ) (hm : 3 ≤ m) {n : ℕ} (hn : 1 ≤ n) : gseq 3 n ≤ gseq m n := by
  induction n, hn using Nat.le_induction with
  | base => rw [gseq_one, gseq_one]; exact hm
  | succ n hn ih => rw [gseq_succ 3 hn, gseq_succ m hn]; exact nxt_mono _ ih

/-- The gap b(n) - a(n) never increases. -/
lemma gap_step (m : ℕ) (hm : chi m = true) {n : ℕ} (hn : 1 ≤ n) :
    gseq m (n + 1) + gseq 3 n ≤ gseq m n + gseq 3 (n + 1) := by
  have hb := gseq_chi m hm hn
  rw [gseq_succ m hn, A160217_formula (n + 1) (by omega), A160217_formula n hn]
  cases hc : chi n <;> cases hc1 : chi (n + 1) <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · -- chi n = false forces chi (n+1) = true
    have : n % 2 = 0 := by by_contra h; rw [chi_odd (by omega)] at hc; simp at hc
    rw [chi_odd (show (n + 1) % 2 = 1 by omega)] at hc1; simp at hc1
  · rw [hc] at hb; rw [adv_ft hb]; omega
  · rw [hc] at hb; have := adv_tf hb; omega
  · have := @adv_tt (gseq m n); omega

/-- For every e >= 1 there are arbitrarily large t in A003159 with t + e not in A003159. -/
lemma exists_t (e N : ℕ) (he : 1 ≤ e) : ∃ t, N ≤ t ∧ chi t = true ∧ chi (t + e) = false := by
  obtain ⟨f, g, hg, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show e ≠ 0 by omega)
  have hg2 : g % 2 = 1 := Nat.odd_iff.1 hg
  have hp : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rcases Nat.even_or_odd f with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine ⟨2 ^ f * (4 * N + g), ?_, ?_, ?_⟩
    · nlinarith
    · rw [chi_pow_mul_odd (by omega)]; simp; omega
    · rw [show 2 ^ f * (4 * N + g) + 2 ^ f * g = 2 ^ (f + 1) * (2 * N + g) by ring,
        chi_pow_mul_odd (by omega)]
      simp; omega
  · refine ⟨2 ^ (f + 1) * (2 * N + 1), ?_, ?_, ?_⟩
    · have : 1 ≤ 2 ^ (f + 1) := Nat.one_le_two_pow
      nlinarith
    · rw [chi_pow_mul_odd (by omega)]; simp; omega
    · rw [show 2 ^ (f + 1) * (2 * N + 1) + 2 ^ f * g = 2 ^ f * (2 * (2 * N + 1) + g) by ring,
        chi_pow_mul_odd (by omega)]
      simp; omega

/-- Main theorem (Shevelev's conjecture in A160217). -/
theorem A160217_conjecture (m : ℕ) (hm3 : 3 < m) (hm : chi m = true) :
    ∃ N, ∀ n, N ≤ n → gseq m n = gseq 3 n := by
  set d : ℕ → ℕ := fun n => gseq m (n + 1) - gseq 3 (n + 1) with hd
  have hge : ∀ n, gseq 3 (n + 1) ≤ gseq m (n + 1) := fun n => gseq_ge m hm3.le (by omega)
  have hanti : ∀ n, d (n + 1) ≤ d n := by
    intro n
    have := gap_step m hm (show 1 ≤ n + 1 by omega)
    have := hge n; have := hge (n + 1)
    simp only [hd]; omega
  -- d attains its minimum value v at some index N0, and is constant from there
  obtain ⟨N0, hN0⟩ : ∃ N0, ∀ n, d N0 ≤ d n := by
    classical
    let P : ℕ → Prop := fun v => ∃ n, d n = v
    have hP : ∃ v, P v := ⟨d 0, 0, rfl⟩
    obtain ⟨N0, hN⟩ := Nat.find_spec hP
    exact ⟨N0, fun n => hN ▸ Nat.find_min' hP ⟨n, rfl⟩⟩
  have hmono : ∀ n k, d (n + k) ≤ d n := by
    intro n k; induction k with
    | zero => simp
    | succ k ih => exact le_trans (hanti _) ih
  have hconst : ∀ n, N0 ≤ n → d n = d N0 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact le_antisymm (hmono _ _) (hN0 _)
  set D := d N0 with hD
  -- values in the constant regime: b(n) = a(n) + D for n >= N0 + 1
  have hb : ∀ n, N0 + 1 ≤ n → gseq m n = gseq 3 n + D := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 : gseq m (k + 1) - gseq 3 (k + 1) = D := hconst k (by omega)
    have := hge k
    omega
  by_cases hD0 : D = 0
  · exact ⟨N0 + 1, fun n hn => by rw [hb n hn, hD0]; rfl⟩
  exfalso
  rcases Nat.even_or_odd D with ⟨e, he⟩ | ⟨e, he⟩
  · -- D = 2e: contradiction at t with chi t, not chi (t + e)
    obtain ⟨t, htN, ht, hte⟩ := exists_t e (N0 + 3) (by omega)
    have hn1 : 1 ≤ t - 1 := by omega
    have hbt := hb t (by omega)
    have hbn := hb (t - 1) (by omega)
    have hsucc := gseq_succ m hn1
    rw [show t - 1 + 1 = t by omega] at hsucc
    rw [A160217_formula t (by omega), ht] at hbt
    simp only [ite_true] at hbt
    have hz : chi (2 * (t + e)) = true := by rw [chi_two_mul (by omega), hte]; rfl
    have hchin := gseq_chi m hm hn1
    rw [A160217_formula (t - 1) hn1] at hbn
    cases hc : chi (t - 1)
    · simp only [hc, Bool.false_eq_true, ite_false] at hbn
      rw [hbn, show 2 * (t - 1) + 2 + D = 2 * (t + e) by omega, hz, hc] at hchin
      simp at hchin
    · simp only [hc, ite_true] at hbn
      have := nxt_le (x := gseq m (t - 1)) (show gseq m (t - 1) < 2 * (t + e) by omega) hz
      rw [← ht] at this
      omega
  · -- D odd: contradiction at an odd index n
    have hn1 : 1 ≤ 2 * N0 + 1 := by omega
    set n := 2 * N0 + 1 with hn
    have hcn : chi n = true := chi_odd (by omega)
    have hbn := hb n (by omega)
    have hbn1 := hb (n + 1) (by omega)
    have hchin := gseq_chi m hm hn1
    rw [A160217_formula n hn1, hcn] at hbn
    simp only [ite_true] at hbn
    rw [gseq_succ m hn1, A160217_formula (n + 1) (by omega)] at hbn1
    have hev : gseq m n % 2 = 0 := by omega
    have hne : gseq m n ≠ 0 := by omega
    rw [hcn] at hchin
    have h4 := chi_even_true hne hev hchin
    cases hc1 : chi (n + 1)
    · simp only [hc1, Bool.false_eq_true, ite_false] at hbn1
      have := nxt_le (x := gseq m n) (c := false) (show gseq m n < gseq m n + 2 by omega)
        (chi_mod4_two (by omega))
      omega
    · simp only [hc1, ite_true] at hbn1
      have := nxt_le (x := gseq m n) (c := true) (show gseq m n < gseq m n + 1 by omega)
        (chi_odd (by omega))
      omega
