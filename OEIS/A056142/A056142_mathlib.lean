/-
OEIS A056142: concatenate n, floor(n/10), floor(n/100), ... (stop before a 0).
Conjecture (F. T. Adams-Watters, 2006, entry text): if n has 3 or more digits,
a(n) is a palindrome only if all the digits of n are the same.

Definitions.
* `a n`: a n = n for n < 10, else a n = n * 10^(#digits of a (n/10)) + a (n/10),
  i.e. the decimal string of n followed by that of a (n/10).
* Words are big-endian digit lists s = [x_1, ..., x_d]. `W s` is
  take d s ++ take (d-1) s ++ ... ++ take 1 s (the concatenation of the entry
  for the digit string s) and `RR s` is rev (take 1 s) ++ ... ++ rev (take d s),
  so that `(W s).reverse = RR s` (`W_reverse`).
* A number m is a palindrome when `(Nat.digits 10 m).reverse = Nat.digits 10 m`.

Main theorems.
* `A056142_three_digits_false`: n = 101 has 3 digits, a 101 = 101101 is a
  palindrome, and the digits of 101 are not all equal; so the conjecture as
  stated (3 or more digits) is false. (D. Wasserman's 2005 comment in the
  entry: for 3 digits, a(n) is a palindrome iff n is.)
* `A056142_conjecture`: for every n with at least 4 digits, a n is a
  palindrome iff all digits of n are equal (Nat.digits 10 n is a constant list).

Route.
* `word_reduction`, `fp_unique`: if W s is a palindrome (length d >= 2), then
  s = map φ [X 1, ..., X d] with φ false = x_1, φ true = x_2, where X is the
  fixed-point word: X 1 = false, X 2 = true, and positions T k + 1 .. T (k+1)
  (T k = k(k+1)/2) hold X (k+1), ..., X 1 (`X_block`).
* `S_of_pal`: if W [X 1..X d] is a palindrome then S d, where
  S r means X (r+1 .. 2r-1) = X (1 .. r-1).
* `not_S`: S r fails for every r >= 4. Strong induction: r < 106 by kernel
  `decide` (`S_base`); for r >= 106 the block of X just after position r,
  read through S r, puts a reversed copy of a prefix of X near the start, and
  the block structure there gives S o for some 4 <= o < r, or a contradiction
  with X 1..X 8 = abaabaaa (`X_vals`).
* `digits_a`: Nat.digits 10 (a n) is the reverse of W (big-endian digits of n).

Not checked in this file: agreement of `a` with the OEIS data terms
(certificate/check_A056142.py).
-/
import Mathlib

open List

namespace A056142

variable {α β : Type*}

/-- Concatenation of the prefixes of s, longest first. -/
def W (s : List α) : List α :=
  ((List.range s.length).reverse.map fun k => s.take (k + 1)).flatten

/-- Concatenation of the reversed prefixes of s, shortest first. -/
def RR (s : List α) : List α :=
  ((List.range s.length).map fun k => (s.take (k + 1)).reverse).flatten

theorem W_reverse (s : List α) : (W s).reverse = RR s := by
  simp [W, RR, List.reverse_flatten, List.map_reverse, Function.comp_def]

theorem W_map (φ : α → β) (s : List α) : W (s.map φ) = (W s).map φ := by
  simp [W, List.map_flatten, Function.comp_def, List.map_take]

theorem RR_map (φ : α → β) (s : List α) : RR (s.map φ) = (RR s).map φ := by
  simp [RR, List.map_flatten, Function.comp_def, List.map_take, List.map_reverse]

theorem W_append_singleton (l : List α) (x : α) :
    W (l ++ [x]) = (l ++ [x]) ++ W l := by
  simp only [W, List.length_append, List.length_singleton, List.range_succ,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons,
    List.flatten_cons]
  congr 1
  · rw [List.take_of_length_le (by simp)]
  · congr 1
    refine List.map_congr_left fun k hk => ?_
    have : k < l.length := by simpa using hk
    rw [List.take_append_of_le_length (by omega)]

theorem RR_take_succ (s : List α) (k : ℕ) (hk : k < s.length) :
    RR (s.take (k + 1)) = RR (s.take k) ++ (s.take (k + 1)).reverse := by
  have h1 : (s.take (k + 1)).length = k + 1 := by simp; omega
  have h2 : (s.take k).length = k := by simp; omega
  rw [RR, RR, h1, h2, List.range_succ, List.map_append, List.flatten_append]
  congr 1
  · congr 1
    refine List.map_congr_left fun i hi => ?_
    have : i < k := by simpa using hi
    rw [List.take_take, List.take_take, Nat.min_eq_left (by omega),
      Nat.min_eq_left (by omega)]
  · simp [List.take_take]

theorem RR_take_prefix (s : List α) :
    ∀ i j, j + i = s.length → RR (s.take j) <+: RR s := by
  intro i
  induction i with
  | zero => intro j hj; rw [List.take_of_length_le (by omega)]
  | succ i ih =>
    intro j hj
    refine List.IsPrefix.trans ?_ (ih (j + 1) (by omega))
    rw [RR_take_succ s j (by omega)]
    exact List.prefix_append _ _

theorem RR_take_length (s : List α) (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ s.length) :
    k < (RR (s.take k)).length := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [RR_take_succ s (j + 1) (by omega), RR_take_succ s j (by omega)]
  simp only [List.length_append, List.length_reverse, List.length_take]
  omega

/-- Fixed-point property: s is the prefix of RR s. -/
def fp (s : List α) : Prop := s = (RR s).take s.length

instance [DecidableEq α] (s : List α) : Decidable (fp s) := by
  unfold fp; infer_instance

theorem fp_map (φ : α → β) (s : List α) (h : fp s) : fp (s.map φ) := by
  unfold fp at *
  rw [RR_map, List.length_map, ← List.map_take, ← h]

theorem fp_of_palindrome (s : List α) (h : (W s).reverse = W s) : fp s := by
  unfold fp
  rw [← W_reverse, h]
  rcases s.eq_nil_or_concat with rfl | ⟨l, x, rfl⟩
  · simp [W]
  · rw [List.concat_eq_append, W_append_singleton, List.take_left' rfl]

theorem fp_get (s : List α) (h : fp s) (k : ℕ) (hk : k < s.length) :
    s[k]? = (RR s)[k]? := by
  conv_lhs => rw [h]
  rw [List.getElem?_take_of_lt hk]

theorem fp_unique (s t : List α) (hl : s.length = t.length) (hs : fp s) (ht : fp t)
    (h0 : s[0]? = t[0]?) (h1 : s[1]? = t[1]?) : s = t := by
  have key : ∀ k, k ≤ s.length → s.take k = t.take k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [List.take_add_one, List.take_add_one, ih (by omega)]
      congr 1
      congr 1
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · exact h0
        · exact h1
      · have hlt := RR_take_length s k hk2 (by omega)
        have hlt' := RR_take_length t k hk2 (by omega)
        obtain ⟨u, hu⟩ := RR_take_prefix s (s.length - k) k (by omega)
        obtain ⟨v, hv⟩ := RR_take_prefix t (t.length - k) k (by omega)
        rw [fp_get s hs k (by omega), fp_get t ht k (by omega), ← hu, ← hv,
          List.getElem?_append_left hlt, List.getElem?_append_left hlt', ih (by omega)]
  have := key s.length le_rfl
  rwa [List.take_length, hl, List.take_length] at this

/-- Reduction: a word whose concatenation is a palindrome is the image of the
Bool fixed point under false ↦ x_1, true ↦ x_2. -/
theorem word_reduction (Xw : List Bool) (hX : ∀ d, d ≤ Xw.length → fp (Xw.take d))
    (h0 : Xw[0]? = some false) (h1 : Xw[1]? = some true)
    (s : List α) (hs : 2 ≤ s.length) (hd : s.length ≤ Xw.length)
    (hp : (W s).reverse = W s) :
    s = (Xw.take s.length).map (fun b => if b then s[1] else s[0]) := by
  apply fp_unique
  · simp; omega
  · exact fp_of_palindrome s hp
  · exact fp_map _ _ (hX _ hd)
  · rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), h0]
    simp [List.getElem?_eq_getElem (show 0 < s.length by omega)]
  · rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), h1]
    simp [List.getElem?_eq_getElem (show 1 < s.length by omega)]

/-! ### The fixed-point word X (1-indexed): X 1 = a (false), X 2 = b (true),
and block k+1 (positions T k + 1 .. T (k+1)) is the reverse of X 1 .. X (k+1). -/

def T (k : ℕ) : ℕ := k * (k + 1) / 2

theorem two_T (k : ℕ) : 2 * T k = k * (k + 1) := by
  unfold T
  have : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  omega

theorem T_succ (k : ℕ) : T (k + 1) = T k + (k + 1) := by
  have h1 := two_T k; have h2 := two_T (k + 1)
  have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
  omega

theorem T_mono {a b : ℕ} (h : a ≤ b) : T a ≤ T b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem le_T (k : ℕ) : k ≤ T k := by
  induction k with
  | zero => simp [T]
  | succ k ih => rw [T_succ]; omega

theorem exists_tri (p : ℕ) (hp : 1 ≤ p) : ∃ k, T k < p ∧ p ≤ T (k + 1) := by
  induction p with
  | zero => omega
  | succ p ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hp'
    · exact ⟨0, by simp [T], by simp [T]⟩
    · obtain ⟨k, h1, h2⟩ := ih hp'
      by_cases h : p + 1 ≤ T (k + 1)
      · exact ⟨k, by omega, h⟩
      · refine ⟨k + 1, by omega, ?_⟩
        rw [T_succ (k + 1)]; omega

/-- Block index: T (mOf p - 1) < p ≤ T (mOf p). -/
def mOf (p : ℕ) : ℕ := Nat.findGreatest (fun m => T m < p) p + 1

theorem mOf_eq {p k : ℕ} (h1 : T k < p) (h2 : p ≤ T (k + 1)) : mOf p = k + 1 := by
  unfold mOf
  congr 1
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨le_trans (le_T k) h1.le, fun _ => h1, fun n hn hnp => ?_⟩
  have := T_mono (show k + 1 ≤ n by omega)
  omega

/-- Fuelled definition; `X p = Xf (p+1) p`. -/
def Xf : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, p => if p = 2 then true else if p ≤ 2 then false else Xf n (T (mOf p) + 1 - p)

def X (p : ℕ) : Bool := Xf (p + 1) p

theorem g_bounds {p : ℕ} (hp : 3 ≤ p) :
    1 ≤ T (mOf p) + 1 - p ∧ T (mOf p) + 1 - p < p := by
  obtain ⟨k, h1, h2⟩ := exists_tri p (by omega)
  rw [mOf_eq h1 h2]
  rw [T_succ] at h2 ⊢
  have : k + 1 < p := by
    by_contra hc
    have hk : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> simp [T] at h1 h2 <;> omega
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    rw [T_succ] at h1
    have := le_T c
    omega
  omega

theorem Xf_stable : ∀ p n m, p ≤ n → p ≤ m → Xf (n + 1) p = Xf (m + 1) p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro n m hn hm
    simp only [Xf]
    by_cases h2 : p = 2
    · simp [h2]
    by_cases h3 : p ≤ 2
    · simp [h2, h3]
    simp only [h2, h3, ite_false]
    have hg := g_bounds (p := p) (by omega)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact ih _ hg.2 n' m' (by omega) (by omega)

theorem X_rec {p : ℕ} (hp : 3 ≤ p) : X p = X (T (mOf p) + 1 - p) := by
  have hg := g_bounds hp
  unfold X
  conv_lhs => simp only [Xf]
  simp only [show p ≠ 2 by omega, show ¬ p ≤ 2 by omega, ite_false]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  exact Xf_stable _ p' _ (by omega) le_rfl

/-- Block property. -/
theorem X_block (k j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ k + 1) :
    X (T k + j) = X (k + 2 - j) := by
  by_cases hp : 3 ≤ T k + j
  · rw [X_rec hp, mOf_eq (k := k) (by omega) (by rw [T_succ]; omega), T_succ]
    congr 1; omega
  · have hk : k ≤ 1 := by
      by_contra hk
      have := T_mono (show 2 ≤ k by omega)
      have h3 : T 2 = 3 := by decide
      omega
    interval_cases k <;> simp [T] at hp ⊢ <;> congr 1 <;> omega

theorem X_vals : X 1 = false ∧ X 2 = true ∧ X 4 = false ∧ X 5 = true ∧ X 8 = false := by
  decide

/-- S r: X (r+1 .. 2r-1) = X (1 .. r-1). -/
def S (r : ℕ) : Prop := ∀ i < r, 1 ≤ i → X (r + i) = X i

instance (r : ℕ) : Decidable (S r) := by unfold S; infer_instance

theorem S_base : ∀ r < 106, 4 ≤ r → ¬ S r := by
  decide +kernel

theorem not_S : ∀ r, 4 ≤ r → ¬ S r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro hr hS
  by_cases hsmall : r < 106
  · exact S_base r hsmall hr hS
  obtain ⟨K', hK1, hK2⟩ := exists_tri r (by omega)
  have tK' := two_T K'
  have tK := two_T (K' + 1)
  have hK15 : 14 ≤ K' := by
    by_contra hc
    have := T_mono (show K' + 1 ≤ 14 by omega)
    have h3 : T 14 = 105 := by decide
    omega
  have hbig : 2 * (K' + 1) + 2 ≤ r := by
    have : K' * 15 ≤ K' * (K' + 1) := Nat.mul_le_mul_left K' (by omega)
    omega
  -- block R_{K+1} with K = K'+1 lies in r+1 .. 2r-1; e = T(K+1) - r
  set K := K' + 1 with hKdef
  have hTK : T K = T K' + K := by rw [hKdef, T_succ]
  have hTK1 : T (K + 1) = T K + (K + 1) := T_succ K
  set e := T (K + 1) - r with he
  have he1 : K + 1 ≤ e := by omega
  have he2 : e ≤ 2 * K := by omega
  have hmir : ∀ t, 1 ≤ t → t ≤ K + 1 → X t = X (e + 1 - t) := by
    intro t ht1 ht2
    have hb := X_block K (K + 2 - t) (by omega) (by omega)
    rw [show K + 2 - (K + 2 - t) = t by omega] at hb
    rw [← hb]
    have := hS (e + 1 - t) (by omega) (by omega)
    rw [← this]
    congr 1; omega
  have htrans : ∀ c, T (c + 1) ≤ e → e - T c ≤ K + 1 →
      ∀ t, e - T (c + 1) + 1 ≤ t → t ≤ e - T c → X t = X (t - (e - T (c + 1))) := by
    intro c hc1 hc2 t ht1 ht2
    have hTc := T_succ c
    rw [hmir t (by omega) (by omega)]
    have hb := X_block c (e + 1 - t - T c) (by omega) (by omega)
    rw [show T c + (e + 1 - t - T c) = e + 1 - t by omega] at hb
    rw [hb]; congr 1; omega
  obtain ⟨k, hk1, hk2⟩ := exists_tri (e + 1) (by omega)
  have tk := two_T k
  have tk1 := two_T (k + 1)
  have hTk1 : T (k + 1) = T k + (k + 1) := T_succ k
  have hk2K : 2 * k ≤ K + 1 := by
    by_contra hc
    have h1 : (K + 2) * (k + 1) ≤ (2 * k) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (K + 2) * (K + 4) ≤ (K + 2) * (2 * (k + 1)) := Nat.mul_le_mul_left _ (by omega)
    have h3 : (K + 2) * (2 * (k + 1)) = 2 * ((K + 2) * (k + 1)) := by ring
    have h4 : (2 * k) * (k + 1) = 2 * (k * (k + 1)) := by ring
    have h5 : (K + 2) * (K + 4) = K * K + 6 * K + 8 := by ring
    have h6 : 15 * K ≤ K * K := Nat.mul_le_mul_right _ (by omega)
    omega
  have hk5 : 5 ≤ k := by
    by_contra hc
    have := T_mono (show k + 1 ≤ 5 by omega)
    have h3 : T 5 = 15 := by decide
    omega
  obtain ⟨c, hc⟩ : ∃ c, k = c + 2 := ⟨k - 2, by omega⟩
  have hTc1 : T (c + 1) + (c + 2) = T k := by rw [hc, T_succ (c + 1)]
  have hTc : T c + (c + 1) = T (c + 1) := (T_succ c).symm
  by_cases ho : e = T k
  · -- offset 0: use block R_{k-1}; gives S k
    apply ih k (by omega) (by omega)
    intro i hi1 hi2
    have := htrans c (by omega) (by omega) (k + i) (by omega) (by omega)
    rw [this]; congr 1; omega
  · set o := e - T k with hodef
    have ho1 : 1 ≤ o := by omega
    have hok : o ≤ k := by omega
    have hX : ∀ t, o + 1 ≤ t → t ≤ o + k → X t = X (t - o) := by
      intro t ht1 ht2
      have := htrans (c + 1) (by rw [← hc]; omega) (by omega) t
        (by rw [← hc]; omega) (by omega)
      rw [this, ← hc]
    obtain ⟨h1, h2, h4, h5, h8⟩ := X_vals
    by_cases ho4 : 4 ≤ o
    · apply ih o (by omega) ho4
      intro i hi1 hi2
      rw [hX (o + i) (by omega) (by omega)]; congr 1; omega
    · interval_cases o
      · have := hX 2 (by omega) (by omega)
        rw [show (2 : ℕ) - 1 = 1 from rfl, h2, h1] at this; exact absurd this (by decide)
      · have := hX 4 (by omega) (by omega)
        rw [show (4 : ℕ) - 2 = 2 from rfl, h4, h2] at this; exact absurd this (by decide)
      · have := hX 8 (by omega) (by omega)
        rw [show (8 : ℕ) - 3 = 5 from rfl, h8, h5] at this; exact absurd this (by decide)

/-! ### Words built from X -/

/-- c d = [X 1, ..., X d]. -/
def cw (d : ℕ) : List Bool := (List.range d).map fun i => X (i + 1)

theorem cw_length (d : ℕ) : (cw d).length = d := by simp [cw]

theorem take_cw {m d : ℕ} (h : m ≤ d) : (cw d).take m = cw m := by
  simp [cw, List.take_range, Nat.min_eq_left h, ← List.map_take]

theorem cw_succ (d : ℕ) : cw (d + 1) = cw d ++ [X (d + 1)] := by
  simp [cw, List.range_succ]

theorem RR_cw (d : ℕ) : RR (cw d) = (List.range (T d)).map fun i => X (i + 1) := by
  induction d with
  | zero => simp [cw, RR, T]
  | succ d ih =>
    have h1 : RR (cw (d + 1)) = RR ((cw (d + 1)).take (d + 1)) := by
      rw [List.take_of_length_le (by simp [cw_length])]
    rw [h1, RR_take_succ _ d (by simp [cw_length]), take_cw (by omega),
      List.take_of_length_le (by simp [cw_length]), ih, T_succ, List.range_add,
      List.map_append, List.map_map]
    congr 1
    apply List.ext_getElem (by simp [cw_length])
    intro j hj1 hj2
    simp only [List.getElem_reverse, cw, List.getElem_map, List.getElem_range,
      Function.comp_apply, List.length_map, List.length_range] at hj1 hj2 ⊢
    have := X_block d (j + 1) (by omega) (by omega)
    rw [show T d + j + 1 = T d + (j + 1) by omega, this]
    congr 1; omega

theorem fp_cw (d : ℕ) : fp (cw d) := by
  unfold fp
  rw [RR_cw, cw_length, ← List.map_take, List.take_range, Nat.min_eq_left (le_T d)]
  rfl

theorem S_of_pal (d : ℕ) (hd : 4 ≤ d) (hp : (W (cw d)).reverse = W (cw d)) : S d := by
  intro i hi1 hi2
  have hWR : W (cw d) = RR (cw d) := by rw [← W_reverse, hp]
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hW : W (cw (d' + 1)) = cw (d' + 1) ++ (cw d' ++ W (cw d'.pred)) := by
    rw [cw_succ, W_append_singleton]
    obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
    rw [cw_succ d'', W_append_singleton]
    simp
  have e1 : (W (cw (d' + 1)))[d' + 1 + (i - 1)]? = some (X i) := by
    rw [hW, List.getElem?_append_right (by simp [cw_length]), cw_length,
      show d' + 1 + (i - 1) - (d' + 1) = i - 1 by omega,
      List.getElem?_append_left (by simp [cw_length]; omega)]
    simp [cw, show i - 1 < d' by omega, show i - 1 + 1 = i by omega]
  have e2 : (RR (cw (d' + 1)))[d' + 1 + (i - 1)]? = some (X (d' + 1 + i)) := by
    have hT := two_T (d' + 1)
    rw [RR_cw]
    have h3 : 4 * (d' + 1) ≤ (d' + 1) * (d' + 1 + 1) := by
      rw [Nat.mul_comm 4]; exact Nat.mul_le_mul_left _ (by omega)
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    exact congrArg some (congrArg X (by omega : d' + 1 + (i - 1) + 1 = d' + 1 + i))
  rw [hWR, e2] at e1
  simpa using e1

/-- Word form, every length d ≥ 4. -/
theorem word_all (s : List α) (h4 : 4 ≤ s.length)
    (hp : (W s).reverse = W s) : s = List.replicate s.length s[0] := by
  have hred := word_reduction (cw s.length)
    (fun d hd => by rw [take_cw (by simpa [cw_length] using hd)]; exact fp_cw d)
    (by simp [cw, show 0 < s.length by omega, X_vals.1])
    (by simp [cw, show 1 < s.length by omega, X_vals.2.1]) s (by omega)
    (by simp [cw_length]) hp
  rw [take_cw le_rfl] at hred
  by_cases h01 : s[1] = s[0]
  · apply List.eq_replicate_iff.mpr
    refine ⟨rfl, fun b hb => ?_⟩
    rw [hred] at hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    cases c <;> simp [h01]
  · exfalso
    set φ : Bool → α := fun b => if b then s[1] else s[0]
    have hinj : Function.Injective φ := by
      intro b c hbc
      cases b <;> cases c <;> simp [φ] at hbc ⊢ <;> first | exact h01 hbc | exact h01 hbc.symm
    apply not_S s.length h4
    apply S_of_pal s.length h4
    rw [hred, W_map, ← List.map_reverse] at hp
    exact List.map_injective_iff.mpr hinj hp

theorem W_replicate (d : ℕ) (x : α) : (W (List.replicate d x)).reverse = W (List.replicate d x) := by
  have : List.replicate d x = (List.range d).map (fun _ => x) := by simp
  rw [this, W_map, ← List.map_reverse]
  simp

/-- A056142. -/
def a (n : ℕ) : ℕ :=
  if h : n < 10 then n
  else n * 10 ^ (Nat.digits 10 (a (n / 10))).length + a (n / 10)
decreasing_by omega

theorem digits_a (n : ℕ) :
    Nat.digits 10 (a n) = (W (Nat.digits 10 n).reverse).reverse := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with h | h
    · rw [a]; simp only [h, ↓reduceDIte]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [W]
      · rw [Nat.digits_of_lt 10 n (by omega) h]; simp [W]
    · have h' : ¬ n < 10 := by omega
      rw [a]; simp only [h', ↓reduceDIte]
      rw [Nat.digits_def' (by norm_num) (by omega : 0 < n),
        List.reverse_cons, W_append_singleton, List.reverse_append, ← ih (n / 10) (by omega),
        mul_comm, add_comm, ← Nat.digits_append_digits (by norm_num),
        Nat.digits_def' (by norm_num) (by omega : 0 < n)]
      simp

theorem A056142_three_digits_false :
    (Nat.digits 10 101).length = 3 ∧ a 101 = 101101 ∧
      (Nat.digits 10 (a 101)).reverse = Nat.digits 10 (a 101) ∧
      Nat.digits 10 101 ≠ List.replicate 3 ((Nat.digits 10 101)[0]!) := by
  have h : Nat.digits 10 101 = [1, 0, 1] := by norm_num
  have ha : Nat.digits 10 (a 101) = [1, 0, 1, 1, 0, 1] := by
    rw [digits_a, h]; decide
  refine ⟨by rw [h]; rfl, ?_, by rw [ha]; rfl, by rw [h]; decide⟩
  rw [← Nat.ofDigits_digits 10 (a 101), ha]; norm_num [Nat.ofDigits]

theorem A056142_conjecture (n : ℕ) (h4 : 4 ≤ (Nat.digits 10 n).length) :
    (Nat.digits 10 (a n)).reverse = Nat.digits 10 (a n) ↔
      ∃ c, Nat.digits 10 n = List.replicate (Nat.digits 10 n).length c := by
  set s := (Nat.digits 10 n).reverse with hs
  have hlen : s.length = (Nat.digits 10 n).length := List.length_reverse
  have e : Nat.digits 10 n = s.reverse := by rw [hs, List.reverse_reverse]
  rw [digits_a, List.reverse_reverse]
  constructor
  · intro hp
    have hW : (W s).reverse = W s := by rw [hs]; exact hp.symm
    obtain ⟨c, hc⟩ : ∃ c, s = List.replicate s.length c :=
      ⟨_, word_all s (by omega) hW⟩
    refine ⟨c, ?_⟩
    rw [e, hc, List.reverse_replicate, List.length_replicate]
  · rintro ⟨c, hc⟩
    have : s = List.replicate s.length c := by
      rw [hs, hc, List.reverse_replicate, List.length_replicate]
    rw [← hs, this]
    exact (W_replicate _ _).symm
