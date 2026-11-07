/-
NT-F31.1 (Guy UPINT F31, Loxton–van der Poorten "awful problem"): L is the set of integers
with a base-4 representation using only the digits 0, 1, -1.  For odd k, m(k) is the least
m ≥ 1 with m ∈ L and k*m ∈ L.  Guy asks whether m(k) ≤ |k|^C for an absolute C.

Checked here (core Lean, no Mathlib):
* `chk_complete`: the greedy digit checker `chk` accepts every element of L (definition `InL`
  is the source's: a finite digit list over {-1,0,1} with that base-4 value).
* `least_133`, `least_517`: m(133) = 333 and m(517) = 5425 (k = 2*4^j + 5 for j = 3, 4):
  explicit digit lists for m and k*m, and no 1 ≤ m' < m works (kernel `decide` over `chk`).
Not checked here: the statement for all j (m(2*4^j+5) has exactly 2j-1 digits, so
m(k) > k^2/100 on this family; finite-automaton argument in certificate/family_lower.py)
and the data m(k) < k^2/48 for odd 37 ≤ k < 2*10^7 (certificate/minm2.c); see README.md.
-/

/-- Base-4 value of a little-endian digit list. -/
def val : List Int → Int
  | [] => 0
  | d :: ds => d + 4 * val ds

/-- All digits are -1, 0 or 1. -/
def okDigits : List Int → Prop
  | [] => True
  | d :: ds => (d = -1 ∨ d = 0 ∨ d = 1) ∧ okDigits ds

/-- L: integers with a base-4 representation using the digits 0, 1, -1. -/
def InL (x : Int) : Prop := ∃ ds : List Int, okDigits ds ∧ val ds = x

/-- Greedy checker with fuel: strip the forced last digit (residue 0, 1 or 3 mod 4). -/
def chk : Nat → Int → Bool
  | 0, x => x == 0
  | f + 1, x =>
    if x == 0 then true
    else if x % 4 == 2 then false
    else if x % 4 == 3 then chk f ((x + 1) / 4)
    else chk f ((x - x % 4) / 4)

theorem chk_succ (f : Nat) : ∀ x : Int, chk f x = true → chk (f + 1) x = true := by
  induction f with
  | zero =>
    intro x h
    simp only [chk, beq_iff_eq] at h
    simp [chk, h]
  | succ f ih =>
    intro x h
    unfold chk at h
    unfold chk
    by_cases h0 : x = 0
    · simp [h0]
    · simp only [h0, beq_iff_eq, ite_false] at h ⊢
      by_cases h2 : x % 4 = 2
      · simp [h2] at h
      · simp only [h2, ite_false] at h ⊢
        by_cases h3 : x % 4 = 3
        · simp only [h3, ite_true] at h ⊢
          exact ih _ h
        · simp only [h3, ite_false] at h ⊢
          exact ih _ h

theorem chk_mono (f g : Nat) (hfg : f ≤ g) (x : Int) (h : chk f x = true) : chk g x = true := by
  induction g with
  | zero =>
    have : f = 0 := by omega
    subst this; exact h
  | succ g ih =>
    by_cases hf : f = g + 1
    · subst hf; exact h
    · exact chk_succ g x (ih (by omega))

/-- One step of the greedy checker on an element of L. -/
theorem InL_step (x : Int) (hx : InL x) (h0 : x ≠ 0) :
    x % 4 ≠ 2 ∧ (x % 4 = 3 → InL ((x + 1) / 4)) ∧ (x % 4 ≠ 3 → InL ((x - x % 4) / 4)) := by
  obtain ⟨ds, hok, hv⟩ := hx
  cases ds with
  | nil => simp [val] at hv; omega
  | cons d ds =>
    simp only [okDigits] at hok
    obtain ⟨hd, hok'⟩ := hok
    simp only [val] at hv
    have hrep : InL (val ds) := ⟨ds, hok', rfl⟩
    rcases hd with hd | hd | hd <;> subst hd
    · refine ⟨by omega, fun _ => ?_, fun h => by omega⟩
      have : (x + 1) / 4 = val ds := by omega
      rw [this]; exact hrep
    · refine ⟨by omega, fun h => by omega, fun _ => ?_⟩
      have : (x - x % 4) / 4 = val ds := by omega
      rw [this]; exact hrep
    · refine ⟨by omega, fun h => by omega, fun _ => ?_⟩
      have : (x - x % 4) / 4 = val ds := by omega
      rw [this]; exact hrep

/-- Completeness: every element of L is accepted with fuel |x| + 1. -/
theorem chk_complete : ∀ (n : Nat) (x : Int), x.natAbs ≤ n → InL x → chk (x.natAbs + 1) x = true := by
  intro n
  induction n with
  | zero =>
    intro x hn _
    have : x = 0 := by omega
    subst this; simp [chk]
  | succ n ih =>
    intro x hn hx
    by_cases h0 : x = 0
    · subst h0; simp [chk]
    · obtain ⟨h2, h3, h1⟩ := InL_step x hx h0
      unfold chk
      simp only [h0, beq_iff_eq, ite_false, h2]
      by_cases hr : x % 4 = 3
      · simp only [hr, ite_true]
        have hy := h3 hr
        have hlt : ((x + 1) / 4).natAbs < x.natAbs := by omega
        exact chk_mono _ _ (by omega) _ (ih _ (by omega) hy)
      · simp only [hr, ite_false]
        have hy := h1 hr
        have hlt : ((x - x % 4) / 4).natAbs < x.natAbs := by omega
        exact chk_mono _ _ (by omega) _ (ih _ (by omega) hy)

theorem not_InL_of_chk (x : Int) (h : chk (x.natAbs + 1) x = false) : ¬ InL x := by
  intro hx
  have := chk_complete x.natAbs x (Nat.le_refl _) hx
  simp [this] at h

/-- No 1 ≤ m < B has m ∈ L and k*m ∈ L, from a kernel check of `chk`. -/
theorem none_below (k B : Nat)
    (hc : (List.range B).all (fun m => m == 0 ||
      !(chk (m + 1) (m : Int) && chk (k * m + 1) ((k * m : Nat) : Int))) = true) :
    ∀ m : Nat, 1 ≤ m → m < B → ¬ (InL (m : Int) ∧ InL ((k * m : Nat) : Int)) := by
  intro m h1 hB ⟨hm, hkm⟩
  have hmem : m ∈ List.range B := List.mem_range.mpr hB
  have := List.all_eq_true.mp hc m hmem
  have e1 := chk_complete _ _ (Nat.le_refl _) hm
  have e2 := chk_complete _ _ (Nat.le_refl _) hkm
  simp only [Int.natAbs_natCast] at e1 e2
  have hm0 : (m == 0) = false := by simp; omega
  rw [hm0, e1, e2] at this
  simp at this

theorem InL_of (ds : List Int) (x : Int) (hok : okDigits ds) (hv : val ds = x) : InL x := ⟨ds, hok, hv⟩

/-- k = 133 = 2*4^3 + 5: least multiplier 333 (Guy's example). -/
theorem least_133 :
    InL 333 ∧ InL (133 * 333) ∧
    ∀ m : Nat, 1 ≤ m → m < 333 → ¬ (InL (m : Int) ∧ InL ((133 * m : Nat) : Int)) := by
  refine ⟨InL_of [1, -1, 1, 1, 1] _ (by simp [okDigits]) (by decide),
          InL_of [1, 0, 0, 0, 1, -1, -1, -1, 1] _ (by simp [okDigits]) (by decide), ?_⟩
  exact none_below 133 333 (by decide +kernel)

/-- Chunked version of `none_below` over [a, a + len). -/
theorem none_between (k a len : Nat)
    (hc : (List.range' a len).all (fun m => m == 0 ||
      !(chk (m + 1) (m : Int) && chk (k * m + 1) ((k * m : Nat) : Int))) = true) :
    ∀ m : Nat, 1 ≤ m → a ≤ m → m < a + len → ¬ (InL (m : Int) ∧ InL ((k * m : Nat) : Int)) := by
  intro m h1 ha hB ⟨hm, hkm⟩
  have hmem : m ∈ List.range' a len := List.mem_range'_1.mpr ⟨ha, hB⟩
  have := List.all_eq_true.mp hc m hmem
  have e1 := chk_complete _ _ (Nat.le_refl _) hm
  have e2 := chk_complete _ _ (Nat.le_refl _) hkm
  simp only [Int.natAbs_natCast] at e1 e2
  have hm0 : (m == 0) = false := by simp; omega
  rw [hm0, e1, e2] at this
  simp at this

/-- k = 517 = 2*4^4 + 5: least multiplier 5425. -/
theorem least_517 :
    InL 5425 ∧ InL (517 * 5425) ∧
    ∀ m : Nat, 1 ≤ m → m < 5425 → ¬ (InL (m : Int) ∧ InL ((517 * m : Nat) : Int)) := by
  refine ⟨InL_of [1, 0, -1, 1, 1, 1, 1] _ (by simp [okDigits]) (by decide),
          InL_of [1, 1, -1, 0, 0, -1, 1, -1, -1, -1, -1, 1] _ (by simp [okDigits]) (by decide), ?_⟩
  intro m h1 hB
  have c0 := none_between 517 0 1000 (by decide +kernel)
  have c1 := none_between 517 1000 1000 (by decide +kernel)
  have c2 := none_between 517 2000 1000 (by decide +kernel)
  have c3 := none_between 517 3000 1000 (by decide +kernel)
  have c4 := none_between 517 4000 1000 (by decide +kernel)
  have c5 := none_between 517 5000 425 (by decide +kernel)
  by_cases d0 : m < 1000
  · exact c0 m h1 (by omega) (by omega)
  by_cases d1 : m < 2000
  · exact c1 m h1 (by omega) (by omega)
  by_cases d2 : m < 3000
  · exact c2 m h1 (by omega) (by omega)
  by_cases d3 : m < 4000
  · exact c3 m h1 (by omega) (by omega)
  by_cases d4 : m < 5000
  · exact c4 m h1 (by omega) (by omega)
  exact c5 m h1 (by omega) (by omega)
