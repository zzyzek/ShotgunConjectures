import Mathlib

/-!
# OEIS A225660: a(n) is odd for n > 9

`F s = (f(0), ..., f(m))` with `m = max s` and `f(i)` the number of `i` in `s`. Starting from the binary
digits of `n` (most significant first), `H n k = F^[k] (bits n)`; `a n` is the least `i` such that
`H n i` occurs again later (the number of non-repeating vectors).

Checked here: `A225660_odd : 9 < n → Odd (a n)`.
Route: the set `C` of the 8 vectors on the cycles of length 2 and 6 is closed under `F` and has period 6;
`H n i` repeats iff `H n i ∈ C`; `F (bits n) = [z, o]` (counts of 0 and 1); pairs reach pairs in an even
number of steps (`F^[2] [z,o] = [max z o - 1, 2]` for `z ≠ o`, `F^[4] [m,m] = [m-2, 3]`), so the hitting
time of `C` from a pair with `z + o ≥ 4` is even (base cases `z, o ≤ 4` by `decide`).
Not checked here: agreement with the OEIS data terms (certificate/explore.py).
-/

namespace A225660

def mx (s : List ℕ) : ℕ := s.foldr max 0

def F (s : List ℕ) : List ℕ := (List.range (mx s + 1)).map (fun i => s.count i)

def bits (n : ℕ) : List ℕ := (Nat.digits 2 n).reverse

def H (n k : ℕ) : List ℕ := F^[k] (bits n)

/-- `H n i` occurs again later. -/
def Rep (n i : ℕ) : Prop := ∃ j, i < j ∧ H n j = H n i

open Classical in
/-- A225660: the number of non-repeating vectors. -/
noncomputable def a (n : ℕ) : ℕ := if h : ∃ i, Rep n i then Nat.find h else 0

def C : List (List ℕ) :=
  [[0,0,2], [0,1,1], [0,3], [1,0,0,1], [1,1,1], [1,2], [2,0,1], [2,2]]

theorem C_closed : ∀ v ∈ C, F v ∈ C := by decide

theorem C_period : ∀ v ∈ C, F^[6] v = v := by decide

theorem C_iter (v : List ℕ) (h : v ∈ C) (t : ℕ) : F^[t] v ∈ C := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact C_closed _ ih

theorem C_len : ∀ v ∈ C, v.length ≤ 4 := by decide

/-- `v` first meets `C` at time `t`. -/
def HitAt (v : List ℕ) (t : ℕ) : Prop := F^[t] v ∈ C ∧ ∀ s < t, F^[s] v ∉ C

theorem hit_succ {v : List ℕ} {t : ℕ} (h : HitAt (F v) t) (hv : v ∉ C) : HitAt v (t + 1) := by
  refine ⟨by rw [Function.iterate_succ_apply]; exact h.1, fun s hs => ?_⟩
  rcases s with _ | s
  · exact hv
  · rw [Function.iterate_succ_apply]; exact h.2 s (by omega)

theorem hit_iter {v : List ℕ} {t k : ℕ} (h : HitAt (F^[k] v) t) (hv : ∀ s < k, F^[s] v ∉ C) :
    HitAt v (t + k) := by
  induction k generalizing v with
  | zero => simpa using h
  | succ k ih =>
    have h' : HitAt (F^[k] (F v)) t := by rwa [← Function.iterate_succ_apply]
    have := ih h' (fun s hs => by rw [← Function.iterate_succ_apply]; exact hv (s + 1) (by omega))
    rw [show t + (k + 1) = (t + k) + 1 by omega]
    exact hit_succ this (by simpa using hv 0 (by omega))

/-! ### Counting over `List.range` -/

theorem mx_append (a b : List ℕ) : mx (a ++ b) = max (mx a) (mx b) := by
  induction a with
  | nil => simp [mx]
  | cons x a ih =>
    simp only [List.cons_append, mx, List.foldr_cons] at *
    rw [ih, max_assoc]

theorem le_mx {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ mx l := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [mx, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem mx_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) : mx l ≤ b := by
  induction l with
  | nil => simp [mx]
  | cons y l ih =>
    simp only [mx, List.foldr_cons] at *
    exact max_le (h y (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem count_range (f : ℕ → ℕ) (c N : ℕ) :
    ((List.range (N + 1)).map f).count c = ((List.range N).map f).count c + if f N = c then 1 else 0 := by
  rw [List.range_succ, List.map_append, List.count_append]
  simp [List.count_cons]

/-- For `z < o`: `F [z, o]` has one `1` at `z` and at `o`, zeros elsewhere. -/
theorem count_pair (z o N : ℕ) (hzo : z ≠ o) :
    ((List.range N).map (fun i => [z, o].count i)).count 1 =
      (if z < N then 1 else 0) + (if o < N then 1 else 0) ∧
    ((List.range N).map (fun i => [z, o].count i)).count 0 =
      N - (if z < N then 1 else 0) - (if o < N then 1 else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [count_range, count_range, ih.1, ih.2]
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    constructor <;> split_ifs <;> first | omega | simp_all

theorem count_pair_le (z o i : ℕ) (hzo : z ≠ o) : [z, o].count i ≤ 1 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]; split_ifs <;> omega

theorem mx_pair (z o : ℕ) : mx [z, o] = max z o := by simp [mx]

theorem F2_pair (z o : ℕ) (hzo : z ≠ o) : F (F [z, o]) = [max z o - 1, 2] := by
  have hF : F [z, o] = (List.range (max z o + 1)).map (fun i => [z, o].count i) := by
    rw [F, mx_pair]
  have hm : mx (F [z, o]) = 1 := by
    apply le_antisymm
    · apply mx_le
      intro x hx
      rw [hF, List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact count_pair_le z o i hzo
    · apply le_mx
      rw [hF, List.mem_map]
      exact ⟨z, by simp, by simp [Ne.symm hzo]⟩
  obtain ⟨h1, h0⟩ := count_pair z o (max z o + 1) hzo
  simp only [show z < max z o + 1 by omega, show o < max z o + 1 by omega, ite_true] at h1 h0
  rw [F, hm, hF, show List.range (1 + 1) = [0, 1] from rfl, List.map_cons, List.map_cons,
    List.map_nil, h0, h1]
  congr 1

theorem count_map_range (f : ℕ → ℕ) (c N : ℕ) :
    ((List.range N).map f).count c = ((Finset.range N).filter (fun i => f i = c)).card := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [count_range, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

theorem len_F (s : List ℕ) : (F s).length = mx s + 1 := by simp [F]

theorem C_mx : ∀ v ∈ C, mx v ≤ 3 := by decide

theorem not_C_of_mx {v : List ℕ} (h : 4 ≤ mx v) : v ∉ C := fun hv => by
  have := C_mx v hv; omega

theorem not_C_of_len {v : List ℕ} (h : 5 ≤ v.length) : v ∉ C := fun hv => by
  have := C_len v hv; omega

/-- The diagonal pair `[m, m]` returns to a pair after four steps. -/
theorem F4_diag (m : ℕ) (hm : 3 ≤ m) :
    F [m, m] = (List.range (m + 1)).map (fun i => [m, m].count i) ∧
    F (F [m, m]) = [m, 0, 1] ∧
    F (F (F [m, m])) = (List.range (m + 1)).map (fun i => [m, 0, 1].count i) ∧
    F (F (F (F [m, m]))) = [m - 2, 3] := by
  have h1 : F [m, m] = (List.range (m + 1)).map (fun i => [m, m].count i) := by
    rw [F]; simp [mx]
  have cnt1 : ∀ i, [m, m].count i = if i = m then 2 else 0 := by
    intro i
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega
  have hm1 : mx (F [m, m]) = 2 := by
    apply le_antisymm
    · apply mx_le; intro x hx; rw [h1, List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx; rw [cnt1]; split_ifs <;> omega
    · apply le_mx; rw [h1, List.mem_map]; exact ⟨m, by simp, by rw [cnt1]; simp⟩
  have h2 : F (F [m, m]) = [m, 0, 1] := by
    rw [F, hm1, show List.range (2 + 1) = [0, 1, 2] from rfl]
    simp only [List.map_cons, List.map_nil, h1, count_map_range, cnt1]
    have e0 : (Finset.range (m + 1)).filter (fun i => (if i = m then 2 else 0) = 0) = Finset.range m := by
      ext i; by_cases h : i = m <;> simp [h]; omega
    have e1 : (Finset.range (m + 1)).filter (fun i => (if i = m then 2 else 0) = 1) = ∅ := by
      ext i; by_cases h : i = m <;> simp [h]
    have e2 : (Finset.range (m + 1)).filter (fun i => (if i = m then 2 else 0) = 2) = {m} := by
      ext i; by_cases h : i = m <;> simp [h]
    rw [e0, e1, e2]; simp
  have cnt3 : ∀ i, [m, 0, 1].count i = if i = m ∨ i = 0 ∨ i = 1 then 1 else 0 := by
    intro i
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega
  have h3 : F [m, 0, 1] = (List.range (m + 1)).map (fun i => [m, 0, 1].count i) := by
    rw [F]; congr 2; simp [mx]; omega
  have hm3 : mx (F [m, 0, 1]) = 1 := by
    apply le_antisymm
    · apply mx_le; intro x hx; rw [h3, List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx; rw [cnt3]; split_ifs <;> omega
    · apply le_mx; rw [h3, List.mem_map]; exact ⟨m, by simp, by rw [cnt3]; simp⟩
  have h4 : F (F [m, 0, 1]) = [m - 2, 3] := by
    rw [F, hm3, show List.range (1 + 1) = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil, h3, count_map_range, cnt3]
    have e1 : (Finset.range (m + 1)).filter
        (fun i => (if i = m ∨ i = 0 ∨ i = 1 then 1 else 0) = 1) = {m, 0, 1} := by
      ext i; by_cases h : i = m ∨ i = 0 ∨ i = 1 <;> simp [h] <;> omega
    have e0 : (Finset.range (m + 1)).filter
        (fun i => (if i = m ∨ i = 0 ∨ i = 1 then 1 else 0) = 0) = Finset.range (m + 1) \ {m, 0, 1} := by
      ext i; by_cases h : i = m ∨ i = 0 ∨ i = 1 <;> simp [h] <;> omega
    have c3 : ({m, 0, 1} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
    rw [e0, e1, Finset.card_sdiff_of_subset (by intro i; simp; omega), c3]
    simp
  exact ⟨h1, h2, by rw [h2, h3], by rw [h2, h4]⟩

instance (v : List ℕ) (t : ℕ) : Decidable (HitAt v t) := by unfold HitAt; infer_instance

theorem base : ∀ z < 5, ∀ o < 5, 4 ≤ z + o → 1 ≤ o → ∃ t < 9, Even t ∧ HitAt [z, o] t := by
  decide

theorem pair_hit (q : ℕ) : ∀ z o, max z o ≤ q → 4 ≤ z + o → 1 ≤ o → ∃ t, Even t ∧ HitAt [z, o] t := by
  induction q with
  | zero => intro z o h1 h2 h3; omega
  | succ q ih =>
    intro z o hq h4 h1
    by_cases hle : max z o ≤ q
    · exact ih z o hle h4 h1
    by_cases hq4 : q ≤ 3
    · obtain ⟨t, _, ht⟩ := base z (by omega) o (by omega) h4 h1
      exact ⟨t, ht⟩
    have hmx : max z o = q + 1 := by omega
    by_cases hzo : z = o
    · subst hzo
      have hz : z = q + 1 := by simpa using hmx
      obtain ⟨d1, d2, d3, d4⟩ := F4_diag z (by omega)
      obtain ⟨t, het, ht⟩ := ih (z - 2) 3 (by omega) (by omega) (by omega)
      refine ⟨t + 4, by rw [Nat.even_add]; simp [het]; decide, hit_iter ?_ ?_⟩
      · simpa [Function.iterate_succ_apply', d4] using ht
      · intro s hs
        interval_cases s
        · exact not_C_of_mx (by simp [mx]; omega)
        · exact not_C_of_len (by rw [Function.iterate_one, d1]; simp; omega)
        · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [d2]; exact not_C_of_mx (by simp [mx]; omega)
        · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [d3]; exact not_C_of_len (by simp; omega)
    · obtain ⟨t, het, ht⟩ := ih q 2 (by omega) (by omega) (by omega)
      refine ⟨t + 2, by rw [Nat.even_add]; simp [het], hit_iter ?_ ?_⟩
      · simpa [Function.iterate_succ_apply', F2_pair z o hzo, hmx] using ht
      · intro s hs
        interval_cases s
        · exact not_C_of_mx (by rw [Function.iterate_zero_apply, mx_pair]; omega)
        · exact not_C_of_len (by simp only [Function.iterate_one]; rw [len_F, mx_pair]; omega)

/-! ### The binary start -/

theorem bits_lt (n : ℕ) : ∀ x ∈ bits n, x < 2 := fun x hx =>
  Nat.digits_lt_base (by norm_num) (List.mem_reverse.1 hx)

theorem one_mem_bits (n : ℕ) (hn : 0 < n) : 1 ∈ bits n := by
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have h1 := Nat.getLast_digit_ne_zero 2 (by omega : n ≠ 0)
  have h2 := Nat.digits_lt_base (b := 2) (m := n) (by norm_num) (List.getLast_mem hne)
  have : (Nat.digits 2 n).getLast hne = 1 := by omega
  rw [bits, List.mem_reverse, ← this]; exact List.getLast_mem hne

theorem count01 (l : List ℕ) (h : ∀ x ∈ l, x < 2) : l.count 0 + l.count 1 = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    simp only [List.count_cons, List.length_cons, beq_iff_eq]
    split_ifs <;> omega

theorem F_bits (n : ℕ) (hn : 0 < n) : F (bits n) = [(bits n).count 0, (bits n).count 1] := by
  have hm : mx (bits n) = 1 := le_antisymm (mx_le fun x hx => by have := bits_lt n x hx; omega)
    (le_mx (one_mem_bits n hn))
  rw [F, hm]; rfl

theorem len_bits (n : ℕ) (hn : 8 ≤ n) : 4 ≤ (bits n).length := by
  rw [bits, List.length_reverse]
  have := Nat.lt_base_pow_length_digits (b := 2) (m := n) (by norm_num)
  by_contra h
  have : 2 ^ (Nat.digits 2 n).length ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem C_small : ∀ c ∈ C, Nat.ofDigits 2 c.reverse ≤ 9 := by decide

theorem bits_not_C (n : ℕ) (hn : 9 < n) : bits n ∉ C := by
  intro h
  have := C_small _ h
  rw [bits, List.reverse_reverse, Nat.ofDigits_digits] at this
  omega

theorem hit_bits (n : ℕ) (hn : 9 < n) : ∃ t, Odd t ∧ HitAt (bits n) t := by
  have hl := len_bits n (by omega)
  have hs := count01 _ (bits_lt n)
  have h1 : 1 ≤ (bits n).count 1 := List.count_pos_iff.2 (one_mem_bits n (by omega))
  obtain ⟨t, het, ht⟩ := pair_hit _ ((bits n).count 0) ((bits n).count 1) le_rfl (by omega) h1
  refine ⟨t + 1, het.add_one, hit_succ ?_ (bits_not_C n hn)⟩
  rwa [F_bits n (by omega)]

/-! ### Repetition means membership in `C` -/

theorem rep_iff (n T : ℕ) (hT : H n T ∈ C) (i : ℕ) : Rep n i ↔ H n i ∈ C := by
  constructor
  · rintro ⟨j, hij, hj⟩
    have hp : F^[j - i] (H n i) = H n i := by
      show F^[j - i] (F^[i] (bits n)) = F^[i] (bits n)
      rw [← Function.iterate_add_apply, show j - i + i = j by omega]
      exact hj
    have hper : ∀ k, F^[(j - i) * k] (H n i) = H n i := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, hp, ih]
    have hTw : F^[T] (H n i) ∈ C := by
      have : F^[T] (H n i) = F^[i] (H n T) := by
        show F^[T] (F^[i] (bits n)) = F^[i] (F^[T] (bits n))
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
      rw [this]; exact C_iter _ hT i
    have hge : T ≤ (j - i) * T := Nat.le_mul_of_pos_left T (by omega)
    rw [← hper T, show (j - i) * T = ((j - i) * T - T) + T by omega, Function.iterate_add_apply]
    exact C_iter _ hTw _
  · intro h
    refine ⟨6 + i, by omega, ?_⟩
    show F^[6 + i] (bits n) = F^[i] (bits n)
    rw [Function.iterate_add_apply]
    exact C_period _ h

/-- A225660: for `n > 9`, `a(n)` is odd. -/
theorem A225660_odd (n : ℕ) (hn : 9 < n) : Odd (a n) := by
  obtain ⟨t, hodd, hT, hmin⟩ := hit_bits n hn
  have hR : ∃ i, Rep n i := ⟨t, (rep_iff n t hT t).2 hT⟩
  have : a n = t := by
    classical
    unfold a
    split
    · rw [Nat.find_eq_iff]
      exact ⟨(rep_iff n t hT t).2 hT, fun s hs hr => hmin s hs ((rep_iff n t hT s).1 hr)⟩
    · exact absurd hR ‹_›
  rw [this]; exact hodd
