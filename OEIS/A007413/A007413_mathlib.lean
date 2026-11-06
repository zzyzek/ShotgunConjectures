/-
OEIS A007413: fixed point of the morphism 1 -> 123, 2 -> 13, 3 -> 2, starting
with 1. Conjecture (Vladimir Shevelev, entry text): the sequence is formed by
the numbers of 1's between consecutive 2's in A076826.

Definitions.
* `tm n`: Thue-Morse A010060, parity of the number of 1's in binary.
* `sig`: the morphism on lists; `A007413 n = (sig^[n] [1])[n-1]` (n >= 1).
  `A007413_iter` shows every iterate sig^[k] [1] agrees with `u` wherever it
  is defined, and `len_iter` that sig^[k] [1] has more than k letters, so this
  is the fixed point.
* `A076826 n = 2 * Σ_{k ≤ n} tm k - n` (over ℤ), the entry's definition.
* `two n`: position of the n-th 2 in A076826 (n >= 1), `Nat.nth`.

Main theorem.
* `A007413_main`: for n >= 1, A007413 n is the number of i with
  two n < i < two (n+1) and A076826 i = 1.

Route. u(n) = 2 + tm n - tm (n+1). sig maps the prefix of u of length m to
the prefix of length L m = 2m + tm m (`flat_prefix`, by four cases on
tm m, tm (m+1)), so A007413 (n+1) = u n. A076826 (2m) = 2 tm m and
A076826 (2m+1) = 1, so the 2's sit at 2 o(j) with o(j) = 2j + 1 - tm j the
odious numbers, and between 2 o(j) and 2 o(j+1) there are o(j+1) - o(j) = u j
odd positions.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py).
-/
import Mathlib

namespace A007413Proof

open Function

/-! ### Thue-Morse -/

/-- A010060: parity of the binary digit sum. -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).sum % 2

lemma tm_zero : tm 0 = 0 := by simp [tm]

lemma tm_odd (m : ℕ) : tm (2 * m + 1) = 1 - tm m := by
  unfold tm
  rw [Nat.digits_def' (by norm_num) (by omega)]
  rw [show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega, List.sum_cons]
  omega

lemma tm_even (m : ℕ) : tm (2 * m) = tm m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  unfold tm
  rw [Nat.digits_def' (by norm_num) (by omega)]
  rw [show (2 * m) % 2 = 0 by omega, show (2 * m) / 2 = m by omega, List.sum_cons]
  omega

lemma tm_le (n : ℕ) : tm n ≤ 1 := by
  unfold tm
  omega

/-! ### The morphism and its fixed point -/

/-- The morphism on letters. -/
def s : ℕ → List ℕ
  | 1 => [1, 2, 3]
  | 2 => [1, 3]
  | 3 => [2]
  | _ => []

/-- The morphism on words. -/
def sig (w : List ℕ) : List ℕ := w.flatMap s

/-- A007413 (offset 1). -/
def A007413 (n : ℕ) : ℕ := (sig^[n] [1]).getD (n - 1) 0

/-- The candidate: u n = 2 + tm n - tm (n+1). -/
def u (n : ℕ) : ℕ := 2 + tm n - tm (n + 1)

lemma u_even (m : ℕ) : u (2 * m) = 1 + 2 * tm m := by
  unfold u
  rw [tm_even, tm_odd]
  have := tm_le m
  omega

lemma u_odd (m : ℕ) : u (2 * m + 1) = 3 - tm m - tm (m + 1) := by
  unfold u
  rw [tm_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, tm_even]
  have := tm_le m
  have := tm_le (m + 1)
  omega

/-- Length of the image of the prefix of length m. -/
def L (m : ℕ) : ℕ := 2 * m + tm m

/-- The prefix of length m. -/
def P (m : ℕ) : List ℕ := (List.range m).map u

lemma s_u (m : ℕ) : L m ≤ L (m + 1) ∧
    s (u m) = (List.range (L (m + 1) - L m)).map fun j => u (L m + j) := by
  have h0 := tm_le m
  have h1 := tm_le (m + 1)
  have e0 := u_even m
  have e1 := u_odd m
  have e2 := u_even (m + 1)
  rw [show 2 * (m + 1) = 2 * m + 2 by ring] at e2
  unfold L
  refine ⟨by omega, ?_⟩
  have hu : u m = 2 + tm m - tm (m + 1) := rfl
  interval_cases hx : tm m <;> interval_cases hy : tm (m + 1)
  · rw [hu]
    simp only [show 2 * (m + 1) + 0 - (2 * m + 0) = 2 by omega, List.range_succ, List.range_zero,
      List.nil_append, List.map_cons, List.map_nil, List.cons_append]
    simp only [add_zero, Nat.reduceSub, s] at *
    rw [e0, e1]
  · rw [hu]
    simp only [show 2 * (m + 1) + 1 - (2 * m + 0) = 3 by omega, List.range_succ, List.range_zero,
      List.nil_append, List.map_cons, List.map_nil, List.cons_append]
    simp only [add_zero, s] at *
    rw [e0, e1, e2]
  · rw [hu]
    simp only [show 2 * (m + 1) + 0 - (2 * m + 1) = 1 by omega, List.range_succ, List.range_zero,
      List.nil_append, List.map_cons, List.map_nil]
    simp only [add_zero, s] at *
    rw [e1]
  · rw [hu]
    simp only [show 2 * (m + 1) + 1 - (2 * m + 1) = 2 by omega, List.range_succ, List.range_zero,
      List.nil_append, List.map_cons, List.map_nil, List.cons_append]
    simp only [add_zero, s] at *
    rw [e1, show 2 * m + 1 + 1 = 2 * m + 2 by ring, e2]

lemma P_add (a b : ℕ) : P (a + b) = P a ++ (List.range b).map fun j => u (a + j) := by
  unfold P
  rw [List.range_add, List.map_append, List.map_map]
  rfl

lemma flat_prefix (m : ℕ) : sig (P m) = P (L m) := by
  induction m with
  | zero => simp [sig, P, L, tm_zero]
  | succ m ih =>
    obtain ⟨hle, hs⟩ := s_u m
    have hP : P (m + 1) = P m ++ [u m] := by
      unfold P
      rw [List.range_succ, List.map_append]
      rfl
    rw [hP, sig, List.flatMap_append, ← sig, ih, List.flatMap_singleton, hs,
      ← P_add, Nat.add_sub_cancel' hle]

lemma u_zero : u 0 = 1 := by
  have := u_even 0
  simpa [tm_zero] using this

/-- `ℓ k`: the length of sig^[k] [1]. -/
def ℓ : ℕ → ℕ
  | 0 => 1
  | k + 1 => L (ℓ k)

lemma iter_eq (k : ℕ) : sig^[k] [1] = P (ℓ k) := by
  induction k with
  | zero => simp [P, ℓ, u_zero]
  | succ k ih => rw [iterate_succ_apply', ih, flat_prefix]; rfl

lemma len_iter (k : ℕ) : k + 1 ≤ ℓ k := by
  induction k with
  | zero => simp [ℓ]
  | succ k ih =>
    show k + 2 ≤ 2 * ℓ k + tm (ℓ k)
    omega

/-- Every iterate agrees with `u` wherever it is defined. -/
theorem A007413_iter (k i : ℕ) (hi : i < (sig^[k] [1]).length) : (sig^[k] [1])[i] = u i := by
  simp only [iter_eq, P, List.getElem_map, List.getElem_range]

/-- A007413 (n+1) = 2 + tm n - tm (n+1). -/
theorem A007413_eq (n : ℕ) : A007413 (n + 1) = u n := by
  unfold A007413
  rw [iter_eq, Nat.add_sub_cancel]
  have h := len_iter (n + 1)
  rw [List.getD_eq_getElem _ _ (by simp [P]; omega)]
  simp [P]

/-! ### A076826 -/

/-- A076826: 2 * Σ_{k ≤ n} tm k - n. -/
def A076826 (n : ℕ) : ℤ := 2 * (∑ k ∈ Finset.range (n + 1), (tm k : ℤ)) - n

lemma sum_pairs (m : ℕ) : ∑ k ∈ Finset.range (2 * m), (tm k : ℤ) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, tm_odd, tm_even]
    have := tm_le m
    push_cast [Nat.cast_sub this]
    ring

lemma b_odd (m : ℕ) : A076826 (2 * m + 1) = 1 := by
  unfold A076826
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, sum_pairs]
  push_cast
  ring

lemma b_even (m : ℕ) : A076826 (2 * m) = 2 * tm m := by
  unfold A076826
  rw [Finset.sum_range_succ, sum_pairs, tm_even]
  push_cast
  ring

lemma b_eq_two (i : ℕ) : A076826 i = 2 ↔ ∃ x, i = 2 * x ∧ tm x = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [b_even]
    constructor
    · intro h
      exact ⟨m, rfl, by have := tm_le m; omega⟩
    · rintro ⟨x, hx, h⟩
      rw [show x = m by omega] at h
      rw [h]
      norm_num
  · rw [b_odd]
    constructor
    · intro h; norm_num at h
    · rintro ⟨x, hx, _⟩; omega

lemma b_eq_one (i : ℕ) : A076826 i = 1 ↔ i % 2 = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [b_even]
    constructor
    · intro h
      have := tm_le m
      omega
    · intro h; omega
  · rw [b_odd]
    constructor
    · intro _; omega
    · intro _; rfl

/-- `Nat.nth p` is `f` when `f` is strictly increasing with range `{m | p m}`. -/
theorem nth_eq {p : ℕ → Prop} {f : ℕ → ℕ} (hf : StrictMono f)
    (hp : ∀ m, p m ↔ ∃ k, f k = m) (n : ℕ) : Nat.nth p n = f n := by
  have hinf : (Set.ofPred p).Infinite :=
    (Set.infinite_range_of_injective hf.injective).mono (by
      rintro _ ⟨k, rfl⟩
      exact (hp _).2 ⟨k, rfl⟩)
  have h := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := p) f ?_ ?_ (hf.strictMonoOn _)
  · exact (h (show n ∈ {n : ℕ | ∀ hf : (Set.ofPred p).Finite, n < hf.toFinset.card} from
      fun hfin => absurd hfin hinf)).symm
  · intro m hm
    obtain ⟨k, rfl⟩ := (hp m).1 hm
    exact ⟨k, fun hfin => absurd hfin hinf, rfl⟩
  · intro k _
    exact (hp _).2 ⟨k, rfl⟩

/-- Odious numbers: o j = 2j + 1 - tm j. -/
def o (j : ℕ) : ℕ := 2 * j + 1 - tm j

lemma o_succ (j : ℕ) : o (j + 1) = o j + u j := by
  unfold o u
  have := tm_le j
  have := tm_le (j + 1)
  omega

lemma tm_o (j : ℕ) : tm (o j) = 1 := by
  unfold o
  have := tm_le j
  rcases Nat.eq_zero_or_pos (tm j) with h | h
  · rw [h, show 2 * j + 1 - 0 = 2 * j + 1 by omega, tm_odd, h]
  · rw [show tm j = 1 by omega, show 2 * j + 1 - 1 = 2 * j by omega, tm_even]
    omega

lemma odious_cover (x : ℕ) (hx : tm x = 1) : ∃ j, o j = x := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' x
  · refine ⟨j, ?_⟩
    rw [tm_even] at hx
    unfold o
    omega
  · refine ⟨j, ?_⟩
    rw [tm_odd] at hx
    unfold o
    have := tm_le j
    omega

lemma u_pos (j : ℕ) : 1 ≤ u j := by
  unfold u
  have := tm_le (j + 1)
  omega

/-- Position of the n-th 2 in A076826 (n ≥ 1). -/
noncomputable def two (n : ℕ) : ℕ := Nat.nth (fun i => A076826 i = 2) (n - 1)

lemma two_eq (n : ℕ) : two (n + 1) = 2 * o n := by
  unfold two
  rw [Nat.add_sub_cancel]
  refine nth_eq (f := fun j => 2 * o j) ?_ ?_ n
  · apply strictMono_nat_of_lt_succ
    intro j
    simp only [o_succ]
    have := u_pos j
    omega
  · intro i
    rw [b_eq_two]
    constructor
    · rintro ⟨x, rfl, hx⟩
      obtain ⟨j, rfl⟩ := odious_cover x hx
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨o j, rfl, tm_o j⟩

lemma count_odd (x y : ℕ) :
    ((Finset.Ioo (2 * x) (2 * y)).filter fun i => A076826 i = 1).card = y - x := by
  have : ((Finset.Ioo (2 * x) (2 * y)).filter fun i => A076826 i = 1) =
      (Finset.Ico x y).image fun j => 2 * j + 1 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_image, Finset.mem_Ico, b_eq_one]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨i / 2, by omega, by omega⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      omega
  rw [this, Finset.card_image_of_injective _ (fun a b hab => by omega),
    Nat.card_Ico]

/-- **Shevelev's conjecture.** For n ≥ 1, A007413(n) is the number of 1's of A076826
strictly between its n-th and (n+1)-th 2. -/
theorem A007413_main (n : ℕ) (hn : 1 ≤ n) :
    A007413 n = ((Finset.Ioo (two n) (two (n + 1))).filter fun i => A076826 i = 1).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [two_eq, two_eq, count_odd, o_succ, A007413_eq]
  omega
