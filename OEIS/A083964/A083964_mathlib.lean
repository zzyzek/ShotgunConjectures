import Mathlib
import OpenProblemsLib.Digits10

/-!
# OEIS A083964: a(n) ≠ 0 when 5 does not divide 2n - 1

A083964(n): smallest palindromic multiple of `k = 2n - 1` beginning with the digit string of `k`, or 0 if none
exists. Conjecture: if `n` is not of the form `(5j + 1)/2` (i.e. `5 ∤ 2n - 1`), then a(n) ≠ 0.

Digit lists are Mathlib's `Nat.digits 10` (least significant digit first). "P begins with the digit string of k"
is `BeginsWith k P : ∃ u, digits P = u ++ digits k` (the most significant digits of `P` are those of `k`).

Checked here:
* `construct` : if `k = g * m` with `gcd(m, 10) = 1` and `g` divides `rev(k)` (the number with the
  digits of `k` reversed), then a positive palindromic multiple of `k` beginning with `k` exists:
  `k`'s digits then reversed, repeated `j + 2` times (Euler's theorem via `OpenProblemsLib.Digits10.dvd_rep`).
* `necessary` : if such a palindrome exists then `gcd(k, 10^c) ∣ rev(k)`, `c` the number of digits of `k`.
* `A083964_main` : for `n ≥ 1` with `¬ 5 ∣ 2n - 1` such a palindrome exists, so a(n) ≠ 0.
* `A083964_zero` : for `n ≥ 1`, if `¬ gcd(2n-1, 10^c) ∣ rev(2n-1)` then no such palindrome exists (a(n) = 0).
* `A083964_nonzero_of` : for `n ≥ 1`, if `5^v ∣ rev(2n-1)` where `5^v` is the full power of 5 in `2n - 1`, then
  a(n) ≠ 0. Together with `A083964_zero` this decides every n except those with `5^c ∣ rev(k)` and `5^(c+1) ∣ k`.
Not checked: the least values (the data); only existence is proved.
-/

namespace A083964

open Nat OpenProblemsLib.Digits10

def IsPal (P : ℕ) : Prop := (Nat.digits 10 P).reverse = Nat.digits 10 P

def BeginsWith (k P : ℕ) : Prop := ∃ u : List ℕ, Nat.digits 10 P = u ++ Nat.digits 10 k

/-- `rev k`: the number whose decimal digits are those of `k` reversed. -/
def rev (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

theorem construct (k g m : ℕ) (hk : 0 < k) (hkm : k = g * m)
    (hc : Nat.Coprime 10 m) (hg : g ∣ rev k) :
    ∃ P, 0 < P ∧ k ∣ P ∧ IsPal P ∧ BeginsWith k P := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hkm; omega)
  set D := Nat.digits 10 k with hD
  have hDne : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  set Y := D.reverse ++ D with hY
  have hYpal : Y.reverse = Y := by simp [Y]
  have hYlen : 1 ≤ Y.length := by
    simp only [Y, List.length_append, List.length_reverse]
    have := List.length_pos_iff.2 hDne
    omega
  obtain ⟨j, hj⟩ := dvd_rep m Y.length hm0 hYlen hc
  set W := rp Y (j + 2)
  have hWlt : ∀ x ∈ W, x < 10 := by
    intro x hx
    have hx' := mem_rp hx
    simp only [Y, List.mem_append, List.mem_reverse] at hx'
    rcases hx' with hx' | hx' <;> exact Nat.digits_lt_base (by norm_num) hx'
  have hWsplit : W = (rp Y (j + 1) ++ D.reverse) ++ D := by
    show Y ++ rp Y (j + 1) = _
    rw [← rp_comm Y (j + 1)]
    simp only [Y, List.append_assoc]
  have hWlast : ∀ h : W ≠ [], W.getLast h ≠ 0 := by
    intro h
    have hlast := Nat.getLast_digit_ne_zero 10 (show k ≠ 0 by omega)
    have : W.getLast h = D.getLast hDne := by
      simp only [hWsplit]
      exact List.getLast_append_of_ne_nil _ hDne
    rw [this]
    exact hlast
  have hYne : Y ≠ [] := List.ne_nil_of_length_pos hYlen
  have hWne : W ≠ [] := by simp [W, rp, hYne]
  have hdig : Nat.digits 10 (Nat.ofDigits 10 W) = W :=
    Nat.digits_ofDigits 10 (by norm_num) W hWlt hWlast
  refine ⟨Nat.ofDigits 10 W, ?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 W) with h | h
    · rw [h, Nat.digits_zero] at hdig; exact absurd hdig.symm hWne
    · exact h
  · rw [ofDigits_rp, hkm]
    apply Nat.mul_dvd_mul _ hj
    rw [Nat.ofDigits_append, Nat.ofDigits_digits]
    exact dvd_add hg (Dvd.dvd.mul_left (hkm ▸ Dvd.intro m rfl) _)
  · rw [IsPal, hdig, rp_reverse, hYpal]
  · exact ⟨rp Y (j + 1) ++ D.reverse, by rw [hdig, hWsplit]⟩

theorem necessary (k P : ℕ) (hpal : IsPal P) (hkP : k ∣ P) (hb : BeginsWith k P) :
    Nat.gcd k (10 ^ (Nat.digits 10 k).length) ∣ rev k := by
  obtain ⟨u, hu⟩ := hb
  have hP : P = rev k + 10 ^ (Nat.digits 10 k).length * Nat.ofDigits 10 u.reverse := by
    have h1 : Nat.digits 10 P = (Nat.digits 10 k).reverse ++ u.reverse := by
      rw [← hpal, hu, List.reverse_append]
    have h2 := Nat.ofDigits_digits 10 P
    rw [h1, Nat.ofDigits_append, List.length_reverse] at h2
    rw [rev, ← h2]
  have hg1 : Nat.gcd k (10 ^ (Nat.digits 10 k).length) ∣ P :=
    Nat.dvd_trans (Nat.gcd_dvd_left _ _) hkP
  have hg2 : Nat.gcd k (10 ^ (Nat.digits 10 k).length) ∣
      10 ^ (Nat.digits 10 k).length * Nat.ofDigits 10 u.reverse :=
    Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _
  rw [hP] at hg1
  exact (Nat.dvd_add_left hg2).1 hg1

theorem A083964_main (n : ℕ) (hn : 1 ≤ n) (h5 : ¬ 5 ∣ 2 * n - 1) :
    ∃ P, 0 < P ∧ (2 * n - 1) ∣ P ∧ IsPal P ∧ BeginsWith (2 * n - 1) P := by
  have hc : Nat.Coprime 10 (2 * n - 1) := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num]
    refine Nat.coprime_mul_iff_left.2 ⟨?_, (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  exact construct (2 * n - 1) 1 (2 * n - 1) (by omega) (by ring) hc (one_dvd _)

theorem A083964_zero (n : ℕ)
    (h : ¬ Nat.gcd (2 * n - 1) (10 ^ (Nat.digits 10 (2 * n - 1)).length) ∣ rev (2 * n - 1)) :
    ¬ ∃ P, 0 < P ∧ (2 * n - 1) ∣ P ∧ IsPal P ∧ BeginsWith (2 * n - 1) P := by
  rintro ⟨P, -, hkP, hpal, hb⟩
  exact h (necessary _ P hpal hkP hb)

theorem A083964_nonzero_of (n v m : ℕ) (hn : 1 ≤ n) (hkm : 2 * n - 1 = 5 ^ v * m) (hm5 : ¬ 5 ∣ m)
    (hv : 5 ^ v ∣ rev (2 * n - 1)) :
    ∃ P, 0 < P ∧ (2 * n - 1) ∣ P ∧ IsPal P ∧ BeginsWith (2 * n - 1) P := by
  have hm2 : ¬ 2 ∣ m := by
    intro h
    have : 2 ∣ 2 * n - 1 := hkm ▸ Dvd.dvd.mul_left h _
    omega
  have hc : Nat.Coprime 10 m := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num]
    exact Nat.coprime_mul_iff_left.2 ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2,
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hm5⟩
  exact construct (2 * n - 1) (5 ^ v) m (by omega) hkm hc hv

/-! ## The full criterion: a(n) ≠ 0 iff gcd(k, 10^c) ∣ rev(k) -/

/-- The construction with a palindromic middle block `Mid`: `Y = rev(D) ++ Mid ++ D` repeated. -/
theorem constructM (k g m : ℕ) (Mid : List ℕ) (hk : 0 < k) (hkm : k = g * m)
    (hc : Nat.Coprime 10 m) (hMid : Mid.reverse = Mid) (hMlt : ∀ x ∈ Mid, x < 10)
    (hg : g ∣ Nat.ofDigits 10 ((Nat.digits 10 k).reverse ++ Mid ++ Nat.digits 10 k)) :
    ∃ P, 0 < P ∧ k ∣ P ∧ IsPal P ∧ BeginsWith k P := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hkm; omega)
  set D := Nat.digits 10 k with hD
  have hDne : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  set Y := D.reverse ++ Mid ++ D with hY
  have hYpal : Y.reverse = Y := by simp [Y, hMid, List.append_assoc]
  have hYlen : 1 ≤ Y.length := by
    simp only [Y, List.length_append, List.length_reverse]
    have := List.length_pos_iff.2 hDne
    omega
  obtain ⟨j, hj⟩ := dvd_rep m Y.length hm0 hYlen hc
  set W := rp Y (j + 2)
  have hWlt : ∀ x ∈ W, x < 10 := by
    intro x hx
    have hx' := mem_rp hx
    simp only [Y, List.mem_append, List.mem_reverse] at hx'
    rcases hx' with (hx' | hx') | hx'
    · exact Nat.digits_lt_base (by norm_num) hx'
    · exact hMlt x hx'
    · exact Nat.digits_lt_base (by norm_num) hx'
  have hWsplit : W = (rp Y (j + 1) ++ (D.reverse ++ Mid)) ++ D := by
    show Y ++ rp Y (j + 1) = _
    rw [← rp_comm Y (j + 1)]
    simp only [Y, List.append_assoc]
  have hWlast : ∀ h : W ≠ [], W.getLast h ≠ 0 := by
    intro h
    have hlast := Nat.getLast_digit_ne_zero 10 (show k ≠ 0 by omega)
    have : W.getLast h = D.getLast hDne := by
      simp only [hWsplit]
      exact List.getLast_append_of_ne_nil _ hDne
    rw [this]
    exact hlast
  have hYne : Y ≠ [] := List.ne_nil_of_length_pos hYlen
  have hWne : W ≠ [] := by simp [W, rp, hYne]
  have hdig : Nat.digits 10 (Nat.ofDigits 10 W) = W :=
    Nat.digits_ofDigits 10 (by norm_num) W hWlt hWlast
  refine ⟨Nat.ofDigits 10 W, ?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 W) with h | h
    · rw [h, Nat.digits_zero] at hdig; exact absurd hdig.symm hWne
    · exact h
  · rw [ofDigits_rp, hkm]
    exact Nat.mul_dvd_mul hg hj
  · rw [IsPal, hdig, rp_reverse, hYpal]
  · exact ⟨rp Y (j + 1) ++ (D.reverse ++ Mid), by rw [hdig, hWsplit]⟩

/-- Solving `10^c x ≡ -r (mod 5^v)` when `gcd(5^v, 10^c) ∣ r`, with `x < 5^v`. -/
theorem solve (v c r : ℕ) (h : Nat.gcd (5 ^ v) (10 ^ c) ∣ r) :
    ∃ x, x < 5 ^ v ∧ 5 ^ v ∣ r + 10 ^ c * x := by
  set M := 5 ^ v
  set d := Nat.gcd M (10 ^ c)
  have hM : 0 < M := by positivity
  obtain ⟨s, hs⟩ := h
  have hb := Nat.gcd_eq_gcd_ab M (10 ^ c)
  set a := Nat.gcdA M (10 ^ c)
  set b := Nat.gcdB M (10 ^ c)
  set X : ℤ := (-(s : ℤ) * b) % M
  have hX0 : 0 ≤ X := Int.emod_nonneg _ (by positivity)
  have hXlt : X < M := Int.emod_lt_of_pos _ (by exact_mod_cast hM)
  refine ⟨X.toNat, by omega, ?_⟩
  have key : (M : ℤ) ∣ (r : ℤ) + (10 ^ c : ℤ) * X := by
    have hXm : (M : ℤ) ∣ X - (-(s : ℤ) * b) := by
      have : X - (-(s : ℤ) * b) = -((M : ℤ) * ((-(s : ℤ) * b) / M)) := by
        simp only [X]; rw [Int.emod_def]; ring
      rw [this]; exact (Dvd.intro _ rfl).neg_right
    have e1 : (r : ℤ) + (10 ^ c : ℤ) * X =
        (10 ^ c : ℤ) * (X - (-(s : ℤ) * b)) + (M : ℤ) * (s * a) := by
      rw [hs]; push_cast at hb ⊢; rw [hb]; ring
    rw [e1]
    exact dvd_add (Dvd.dvd.mul_left hXm _) (Dvd.intro _ rfl)
  have : ((r + 10 ^ c * X.toNat : ℕ) : ℤ) = (r : ℤ) + (10 ^ c : ℤ) * X := by
    push_cast; rw [Int.toNat_of_nonneg hX0]
  exact Int.natCast_dvd_natCast.1 (by rw [this]; exact_mod_cast key)

theorem A083964_iff (n : ℕ) (hn : 1 ≤ n) :
    (∃ P, 0 < P ∧ (2 * n - 1) ∣ P ∧ IsPal P ∧ BeginsWith (2 * n - 1) P) ↔
      Nat.gcd (2 * n - 1) (10 ^ (Nat.digits 10 (2 * n - 1)).length) ∣ rev (2 * n - 1) := by
  constructor
  · rintro ⟨P, -, hkP, hpal, hb⟩
    exact necessary _ P hpal hkP hb
  · intro hgk
    set k := 2 * n - 1 with hk
    obtain ⟨v, m, hm5, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) 5 (by norm_num)
    have hm2 : ¬ 2 ∣ m := by
      intro h
      have : 2 ∣ k := hkm ▸ Dvd.dvd.mul_left h _
      omega
    have hc : Nat.Coprime 10 m := by
      rw [show (10 : ℕ) = 2 * 5 by norm_num]
      exact Nat.coprime_mul_iff_left.2 ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2,
        (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hm5⟩
    set c := (Nat.digits 10 k).length
    have hsub : Nat.gcd (5 ^ v) (10 ^ c) ∣ rev k :=
      (Nat.gcd_dvd_gcd_of_dvd_left _ (Dvd.intro m hkm.symm)).trans hgk
    obtain ⟨x, hx, hdx⟩ := solve v c (rev k) hsub
    -- `x` padded to `v` digits, mirrored.
    have hx10 : x < 10 ^ v := lt_of_lt_of_le hx (Nat.pow_le_pow_left (by norm_num) v)
    set X := Nat.digits 10 x
    have hXl : X.length ≤ v := (Nat.digits_length_le_iff (by norm_num) x).2 hx10
    set Xp := X ++ List.replicate (v - X.length) 0
    have hXp : Nat.ofDigits 10 Xp = x := by
      rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
    have hXpl : Xp.length = v := by simp [Xp]; omega
    have hXlt : ∀ y ∈ Xp, y < 10 := by
      intro y hy
      simp only [Xp, List.mem_append, List.mem_replicate] at hy
      rcases hy with hy | hy
      · exact Nat.digits_lt_base (by norm_num) hy
      · omega
    set Mid := Xp ++ Xp.reverse
    have hMid : Mid.reverse = Mid := by simp [Mid]
    have hMlt : ∀ y ∈ Mid, y < 10 := by
      intro y hy
      simp only [Mid, List.mem_append, List.mem_reverse] at hy
      rcases hy with hy | hy <;> exact hXlt y hy
    apply constructM k (5 ^ v) m Mid (by omega) hkm hc hMid hMlt
    have hval : Nat.ofDigits 10 ((Nat.digits 10 k).reverse ++ Mid ++ Nat.digits 10 k) =
        (rev k + 10 ^ c * x) + 10 ^ (c + v) *
          (Nat.ofDigits 10 Xp.reverse + 10 ^ v * k) := by
      simp only [Mid, List.append_assoc, Nat.ofDigits_append, List.length_reverse, hXpl,
        Nat.ofDigits_digits, hXp, rev]
      rw [pow_add]; ring
    rw [hval]
    refine dvd_add hdx (Dvd.dvd.mul_right ?_ _)
    rw [pow_add, show (10 : ℕ) ^ v = 2 ^ v * 5 ^ v by rw [← mul_pow]; norm_num]
    exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _
