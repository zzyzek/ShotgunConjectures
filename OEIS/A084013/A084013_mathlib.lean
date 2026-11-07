import Mathlib

/-!
# OEIS A084013 and A084015: every n has an n-digit palindromic multiple

A084013(n) (A084015(n)): smallest (largest) n-digit palindromic multiple of `n`; "for n = 10k it is sufficient
that the multiple is palindromic with leading zeros ignored"; 0 if no such number exists. Conjecture in both
entries: no entry is zero. Both conjectures say that for every `n ≥ 1` an admissible `n`-digit multiple exists.

Reading: for `10 ∤ n` the multiple is an ordinary palindrome; for `n = 10^s n'` with `s ≥ 1`, `10 ∤ n'`, it is
`10^s * u` with `u` a palindrome (`PalLZ`; the digit string with `s` leading zeros prepended reads the same
both ways). This reading reproduces the data (a(10) = 1000000010, not 10^9).
Digit lists are Mathlib's `Nat.digits 10` (least significant digit first).

Checked here:
* `pal_U` : if `9m ∣ 10^r - 1` and `1 ≤ r ≤ L`, the `L`-digit palindrome `U_r (10^(L-r) + 1)`
  (`U_r` = r ones; digits 1, and 2 where the two copies overlap) is divisible by `m`.
* `ord_bound` : for `gcd(m, 10) = 1` there is such an `r` with `r ≤ m` (`r = 3^k φ(m')`, `m = 3^k m'`,
  using `3^(k+2) ∣ 10^(3^k) - 1`).
* `pal_G` : if `g ∣ 10^e`, `g < 10^e`, `10 ∤ g`, `gcd(g, m) = 1`, `10^R ≡ 1 (mod m)`, `e ≤ R` and
  `2(R + e) ≤ L`, the palindrome with low half `Gp 9^(R-e) (9 - Gp)` (Gp = digits of g padded to e places),
  zeros in the middle, and the mirror image on top, has `L` digits and is divisible by `g m`.
* `pal_exists` : for `10 ∤ n'` and `L ≥ n'` (and `L ≥ 12` when `n' ∈ {2, 4, 8}`) there is an `L`-digit
  palindrome divisible by `n'`.
* `A084013_main` : for every `n ≥ 1` there is an `n`-digit multiple `N` of `n` which is a palindrome when
  `10 ∤ n` and is `10^s u` with `u` a palindrome when `n = 10^s n'`, `s ≥ 1`, `10 ∤ n'`. So no term of A084013 or A084015 is 0.
Not checked: the least or greatest values (the data).
-/

namespace A084013

open Nat

def IsPal (N : ℕ) : Prop := (Nat.digits 10 N).reverse = Nat.digits 10 N

/-- "Palindromic with leading zeros ignored" for `n = 10^s n'`, `10 ∤ n'`: `N = 10^s u` with `u` a palindrome
(prepending `s` zeros to the digit string of `N` gives a palindrome). This is the reading that reproduces
a(10) = 1000000010 (10^9 is excluded). -/
def PalLZ (n N : ℕ) : Prop := ∃ s n' u, n = 10 ^ s * n' ∧ ¬ 10 ∣ n' ∧ N = 10 ^ s * u ∧ IsPal u

theorem ofDigits_rep (d k : ℕ) : 9 * Nat.ofDigits 10 (List.replicate k d) + d = d * 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons]
    have : d * 10 ^ (k + 1) = 10 * (d * 10 ^ k) := by ring
    rw [this, ← ih]
    ring

theorem ofDigits_compl (l : List ℕ) (h : ∀ x ∈ l, x < 10) :
    Nat.ofDigits 10 (l.map (9 - ·)) + Nat.ofDigits 10 l + 1 = 10 ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, pow_succ]
    set t := 10 ^ l.length
    omega

/-- A digit list that reads the same both ways and starts with a nonzero digit is the digit list of a
palindrome with that many digits. -/
theorem of_list (W : List ℕ) (hlt : ∀ x ∈ W, x < 10) (hpal : W.reverse = W)
    (hhead : ∃ d t, W = d :: t ∧ d ≠ 0) :
    (Nat.digits 10 (Nat.ofDigits 10 W)).length = W.length ∧ IsPal (Nat.ofDigits 10 W) := by
  obtain ⟨d, t, hW, hd⟩ := hhead
  have hne : W ≠ [] := by simp [hW]
  have hlast : ∀ h : W ≠ [], W.getLast h ≠ 0 := by
    intro h
    have h1 := List.head_reverse (l := W) (by simpa using h)
    simp only [hpal] at h1
    rw [← h1]
    simp [hW, hd]
  have hdig := Nat.digits_ofDigits 10 (by norm_num) W hlt hlast
  refine ⟨by rw [hdig], ?_⟩
  rw [IsPal, hdig, hpal]

theorem dvd_of_modEq_add (v A B M : ℕ) (h : v + A = B) (hAB : A ≡ B [MOD M]) : M ∣ v := by
  have h1 : v + A ≡ 0 + A [MOD M] := by rw [h, zero_add]; exact hAB.symm
  exact (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_right_cancel' A h1)

/-- The `g = 1` construction: two overlapping or separated runs of ones. -/
theorem pal_U (m L r : ℕ) (hr : 1 ≤ r) (hrL : r ≤ L) (h9 : 9 * m ∣ 10 ^ r - 1) :
    ∃ P, (Nat.digits 10 P).length = L ∧ m ∣ P ∧ IsPal P := by
  have h10 : 10 ^ r ≡ 1 [MOD 9 * m] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).2 h9).symm
  rcases Nat.lt_or_ge L (2 * r) with hL | hL
  · -- `a` ones, `b` twos, `a` ones, with `a + b = r`, `2a + b = L`.
    set a := L - r
    set b := 2 * r - L
    set W := List.replicate a 1 ++ List.replicate b 2 ++ List.replicate a 1
    have hlt : ∀ x ∈ W, x < 10 := by
      intro x hx; simp only [W, List.mem_append, List.mem_replicate] at hx; omega
    have hpal : W.reverse = W := by simp [W, List.reverse_replicate, List.append_assoc]
    have hhead : ∃ d t, W = d :: t ∧ d ≠ 0 := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · refine ⟨2, List.replicate (b - 1) 2, ?_, by norm_num⟩
        simp only [W, ha, List.replicate_zero, List.nil_append, List.append_nil]
        rw [← List.replicate_succ]; congr 1; omega
      · refine ⟨1, List.replicate (a - 1) 1 ++ List.replicate b 2 ++ List.replicate a 1, ?_, by norm_num⟩
        simp only [W, List.append_assoc]
        rw [← List.cons_append, ← List.replicate_succ]; congr 2; omega
    obtain ⟨hlen, hP⟩ := of_list W hlt hpal hhead
    refine ⟨Nat.ofDigits 10 W, by rw [hlen]; simp [W]; omega, ?_, hP⟩
    have e1 := ofDigits_rep 1 a
    have e2 := ofDigits_rep 2 b
    have hval : Nat.ofDigits 10 W = Nat.ofDigits 10 (List.replicate a 1) +
        10 ^ a * (Nat.ofDigits 10 (List.replicate b 2) +
          10 ^ b * Nat.ofDigits 10 (List.replicate a 1)) := by
      simp only [W, List.append_assoc, Nat.ofDigits_append, List.length_replicate]
    have hab : a + b = r := by omega
    have hpow : 10 ^ a * 10 ^ b = 10 ^ r := by rw [← pow_add, hab]
    have key : 9 * Nat.ofDigits 10 W + (1 + 2 * 10 ^ a + 10 ^ r) =
        10 ^ a + 2 * 10 ^ r + 10 ^ r * 10 ^ a := by
      rw [hval]
      rw [← hpow]
      set X := Nat.ofDigits 10 (List.replicate a 1)
      set Y := Nat.ofDigits 10 (List.replicate b 2)
      set A := 10 ^ a
      set B := 10 ^ b
      have e1' : 9 * X + 1 = A := by omega
      have e2' : 9 * Y + 2 = 2 * B := by omega
      zify at e1' e2' ⊢
      linear_combination (1 + (A : ℤ) * B) * e1' + (A : ℤ) * e2'
    have hmod : 1 + 2 * 10 ^ a + 10 ^ r ≡ 10 ^ a + 2 * 10 ^ r + 10 ^ r * 10 ^ a [MOD 9 * m] := by
      have := ((h10.mul_left 2).add_left (10 ^ a)).add (h10.mul_right (10 ^ a))
      simp only [mul_one, one_mul] at this
      have h' : 1 + 2 * 10 ^ a + 10 ^ r ≡ 1 + 2 * 10 ^ a + 1 [MOD 9 * m] :=
        Nat.ModEq.add_left _ h10
      refine h'.trans ?_
      refine Nat.ModEq.trans ?_ this.symm
      rw [show 1 + 2 * 10 ^ a + 1 = 10 ^ a + 2 * 1 + 10 ^ a by ring]
    have h9m := dvd_of_modEq_add _ _ _ _ key hmod
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9m
  · -- `r` ones, zeros, `r` ones.
    set z := L - 2 * r
    set W := List.replicate r 1 ++ List.replicate z 0 ++ List.replicate r 1
    have hlt : ∀ x ∈ W, x < 10 := by
      intro x hx; simp only [W, List.mem_append, List.mem_replicate] at hx; omega
    have hpal : W.reverse = W := by simp [W, List.reverse_replicate, List.append_assoc]
    have hhead : ∃ d t, W = d :: t ∧ d ≠ 0 := by
      refine ⟨1, List.replicate (r - 1) 1 ++ List.replicate z 0 ++ List.replicate r 1, ?_, by norm_num⟩
      simp only [W, List.append_assoc]
      rw [← List.cons_append, ← List.replicate_succ]; congr 2; omega
    obtain ⟨hlen, hP⟩ := of_list W hlt hpal hhead
    refine ⟨Nat.ofDigits 10 W, by rw [hlen]; simp [W]; omega, ?_, hP⟩
    have e1 := ofDigits_rep 1 r
    have hval : Nat.ofDigits 10 W = Nat.ofDigits 10 (List.replicate r 1) +
        10 ^ (r + z) * Nat.ofDigits 10 (List.replicate r 1) := by
      simp only [W, List.append_assoc, Nat.ofDigits_append, List.length_replicate,
        Nat.ofDigits_replicate_zero, zero_add, pow_add]
      ring
    set X := Nat.ofDigits 10 (List.replicate r 1)
    have key : 9 * Nat.ofDigits 10 W + (1 + 10 ^ (r + z)) = 10 ^ r + 10 ^ r * 10 ^ (r + z) := by
      rw [hval]
      have e1' : 10 ^ r = 9 * X + 1 := by omega
      rw [e1']
      ring
    have hmod : 1 + 10 ^ (r + z) ≡ 10 ^ r + 10 ^ r * 10 ^ (r + z) [MOD 9 * m] := by
      have := h10.add (h10.mul_right (10 ^ (r + z)))
      simp only [one_mul] at this
      exact this.symm
    have h9m := dvd_of_modEq_add _ _ _ _ key hmod
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9m

/-- `3^(k+2) ∣ 10^(3^k) - 1` (lifting the exponent). -/
theorem lte3 (k : ℕ) : 3 ^ (k + 2) ∣ 10 ^ (3 ^ k) - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    have hx : 1 ≤ 10 ^ (3 ^ k) := Nat.one_le_pow _ _ (by norm_num)
    set x := 10 ^ (3 ^ k) with hxdef
    have hpow : 10 ^ (3 ^ (k + 1)) = x ^ 3 := by rw [hxdef, ← pow_mul, pow_succ]
    rw [hpow]
    have hx' : x = 3 ^ (k + 2) * c + 1 := by omega
    refine ⟨c * ((3 ^ (k + 2) * c) ^ 2 + 3 * (3 ^ (k + 2) * c) + 3) / 3, ?_⟩
    have h3 : 3 ∣ (3 ^ (k + 2) * c) ^ 2 + 3 * (3 ^ (k + 2) * c) + 3 := by
      refine dvd_add (dvd_add ?_ (dvd_mul_right _ _)) (dvd_refl _)
      exact Dvd.dvd.pow (Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _) (by norm_num)
    obtain ⟨d, hd⟩ := h3
    rw [hx', show c * ((3 ^ (k + 2) * c) ^ 2 + 3 * (3 ^ (k + 2) * c) + 3) = 3 * (c * d) by rw [hd]; ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    have : (3 ^ (k + 2) * c + 1) ^ 3 = 3 ^ (k + 2) * c * ((3 ^ (k + 2) * c) ^ 2 + 3 * (3 ^ (k + 2) * c) + 3) + 1 := by
      ring
    rw [this, hd, Nat.add_sub_cancel]
    ring

theorem ord_bound (m : ℕ) (hm : 0 < m) (hc : Nat.Coprime 10 m) :
    ∃ r, 1 ≤ r ∧ r ≤ m ∧ 9 * m ∣ 10 ^ r - 1 := by
  obtain ⟨k, m', h3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) 3 (by norm_num)
  have hm' : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hc' : Nat.Coprime 10 m' := Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hc
  refine ⟨3 ^ k * φ m', ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (Nat.totient_pos.2 hm').ne')
  · exact Nat.mul_le_mul_left _ (Nat.totient_le m')
  · have hA : 3 ^ (k + 2) ∣ 10 ^ (3 ^ k * φ m') - 1 :=
      (lte3 k).trans (Nat.pow_sub_one_dvd_pow_sub_one 10 (Dvd.intro _ rfl))
    have hB : m' ∣ 10 ^ (3 ^ k * φ m') - 1 := by
      have h1 : 10 ^ φ m' ≡ 1 [MOD m'] := Nat.ModEq.pow_totient hc'
      have h2 : m' ∣ 10 ^ φ m' - 1 :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h1.symm
      exact h2.trans (Nat.pow_sub_one_dvd_pow_sub_one 10 (Dvd.intro_left _ rfl))
    have hcop : Nat.Coprime (3 ^ (k + 2)) m' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hA hB
    rw [show 9 * (3 ^ k * m') = 3 ^ (k + 2) * m' by ring]
    exact this

/-- The `g > 1` construction: low half `Gp 9^(R-e) (9 - Gp)`, zeros, mirror image. -/
theorem pal_G (g m e R L : ℕ) (hg0 : 0 < g) (hge : g ∣ 10 ^ e) (hglt : g < 10 ^ e)
    (hg10 : g % 10 ≠ 0) (hcop : Nat.Coprime g m) (h10 : 10 ^ R ≡ 1 [MOD m]) (heR : e ≤ R)
    (hL : 2 * (R + e) ≤ L) :
    ∃ P, (Nat.digits 10 P).length = L ∧ g * m ∣ P ∧ IsPal P := by
  set G := Nat.digits 10 g with hG
  have hGl : G.length ≤ e := (Nat.digits_length_le_iff (by norm_num) g).2 hglt
  set Gp := G ++ List.replicate (e - G.length) 0 with hGpdef
  have hGp : Nat.ofDigits 10 Gp = g := by
    rw [hGpdef, Nat.ofDigits_append_replicate_zero, hG, Nat.ofDigits_digits]
  have hGpl : Gp.length = e := by simp [Gp]; omega
  have hGlt : ∀ x ∈ Gp, x < 10 := by
    intro x hx
    simp only [Gp, List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | hx
    · exact Nat.digits_lt_base (by norm_num) hx
    · omega
  have hGcons : G = g % 10 :: Nat.digits 10 (g / 10) := Nat.digits_def' (by norm_num) hg0
  set Cp := Gp.map (9 - ·) with hCp
  set Lo := Gp ++ List.replicate (R - e) 9 ++ Cp with hLo
  set z := L - 2 * (R + e)
  set W := Lo ++ List.replicate z 0 ++ Lo.reverse with hW
  have hLolt : ∀ x ∈ Lo, x < 10 := by
    intro x hx
    simp only [Lo, Cp, List.mem_append, List.mem_replicate, List.mem_map] at hx
    rcases hx with (hx | ⟨_, rfl⟩) | ⟨y, _, rfl⟩
    · exact hGlt x hx
    · norm_num
    · omega
  have hlt : ∀ x ∈ W, x < 10 := by
    intro x hx
    simp only [W, List.mem_append, List.mem_reverse, List.mem_replicate] at hx
    rcases hx with (hx | ⟨_, rfl⟩) | hx
    · exact hLolt x hx
    · norm_num
    · exact hLolt x hx
  have hpal : W.reverse = W := by simp [W, List.append_assoc]
  have hhead : ∃ d t, W = d :: t ∧ d ≠ 0 :=
    ⟨g % 10, Nat.digits 10 (g / 10) ++ List.replicate (e - G.length) 0 ++
      List.replicate (R - e) 9 ++ Cp ++ List.replicate z 0 ++ Lo.reverse,
      by simp only [W, Lo, Gp, hGcons, List.cons_append, List.append_assoc], hg10⟩
  obtain ⟨hlen, hP⟩ := of_list W hlt hpal hhead
  have hLol : Lo.length = R + e := by simp [Lo, Cp, hGpl]; omega
  refine ⟨Nat.ofDigits 10 W, by rw [hlen]; simp [W, hLol]; omega, ?_, hP⟩
  -- Values of the pieces.
  set N9 := Nat.ofDigits 10 (List.replicate (R - e) 9)
  have e9 : N9 + 1 = 10 ^ (R - e) := by have := ofDigits_rep 9 (R - e); omega
  have eC : Nat.ofDigits 10 Cp + g + 1 = 10 ^ e := by
    have := ofDigits_compl Gp hGlt; rw [hGp, hGpl] at this; exact this
  set g' := Nat.ofDigits 10 Gp.reverse
  have eC' : Nat.ofDigits 10 Cp.reverse + g' + 1 = 10 ^ e := by
    have := ofDigits_compl Gp.reverse (fun x hx => hGlt x (List.mem_reverse.1 hx))
    rw [List.length_reverse, hGpl] at this
    rw [hCp, ← List.map_reverse]
    exact this
  have hRe : 10 ^ R = 10 ^ e * 10 ^ (R - e) := by rw [← pow_add]; congr 1; omega
  have vLo : Nat.ofDigits 10 Lo = g + 10 ^ e * (N9 + 10 ^ (R - e) * Nat.ofDigits 10 Cp) := by
    simp only [Lo, List.append_assoc, Nat.ofDigits_append, List.length_replicate, hGp, hGpl]
    rfl
  have vRev : Nat.ofDigits 10 Lo.reverse =
      Nat.ofDigits 10 Cp.reverse + 10 ^ e * (N9 + 10 ^ (R - e) * g') := by
    simp only [Lo, List.reverse_append, List.reverse_replicate, List.append_assoc,
      Nat.ofDigits_append, List.length_replicate, List.length_reverse]
    have hCl : Cp.length = e := by rw [hCp, List.length_map, hGpl]
    rw [hCl]
  have vW : Nat.ofDigits 10 W = Nat.ofDigits 10 Lo +
      10 ^ (R + e + z) * Nat.ofDigits 10 Lo.reverse := by
    simp only [W, List.append_assoc, Nat.ofDigits_append, List.length_replicate,
      Nat.ofDigits_replicate_zero, zero_add, hLol, pow_add]
    ring
  -- `m` divides both halves.
  have hmLo : m ∣ Nat.ofDigits 10 Lo := by
    have key : Nat.ofDigits 10 Lo + (10 ^ e + 10 ^ R * (g + 1)) =
        g + 10 ^ R + 10 ^ R * 10 ^ e := by
      rw [vLo, hRe]
      set E := 10 ^ e
      set F := 10 ^ (R - e)
      zify at e9 eC ⊢
      linear_combination (E : ℤ) * e9 + (E : ℤ) * F * eC
    apply dvd_of_modEq_add _ _ _ _ key
    have hA : 10 ^ e + 10 ^ R * (g + 1) ≡ 10 ^ e + 1 * (g + 1) [MOD m] :=
      Nat.ModEq.add_left _ (h10.mul_right _)
    have hB : g + 10 ^ R + 10 ^ R * 10 ^ e ≡ g + 1 + 1 * 10 ^ e [MOD m] :=
      (Nat.ModEq.add_left g h10).add (h10.mul_right _)
    refine hA.trans (Nat.ModEq.trans ?_ hB.symm)
    rw [show 10 ^ e + 1 * (g + 1) = g + 1 + 1 * 10 ^ e by ring]
  have hmRev : m ∣ Nat.ofDigits 10 Lo.reverse := by
    have key : Nat.ofDigits 10 Lo.reverse + (g' + 1) = 10 ^ R * (g' + 1) := by
      rw [vRev, hRe]
      set E := 10 ^ e
      set F := 10 ^ (R - e)
      zify at e9 eC' ⊢
      linear_combination eC' + (E : ℤ) * e9
    apply dvd_of_modEq_add _ _ _ _ key
    have := h10.mul_right (g' + 1)
    rw [one_mul] at this
    exact this.symm
  have hgLo : g ∣ Nat.ofDigits 10 Lo := by
    rw [vLo]; exact dvd_add dvd_rfl (Dvd.dvd.mul_right hge _)
  have hgRev : g ∣ 10 ^ (R + e + z) * Nat.ofDigits 10 Lo.reverse :=
    Dvd.dvd.mul_right (hge.trans (Nat.pow_dvd_pow 10 (by omega))) _
  rw [vW]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (dvd_add hgLo hgRev)
    (dvd_add hmLo (Dvd.dvd.mul_left hmRev _))

theorem two_mul_le (a : ℕ) : 2 * a ≤ 2 ^ a := by
  rcases a with _ | a
  · norm_num
  · have := Nat.lt_two_pow_self (n := a)
    rw [pow_succ]; omega

theorem four_mul_le (a : ℕ) (ha : 4 ≤ a) : 4 * a ≤ 2 ^ a := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  have := two_mul_le c
  rw [pow_add]; omega

theorem four_mul_le5 (b : ℕ) : 4 * b ≤ 5 ^ b := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    have := Nat.one_le_pow b 5 (by norm_num)
    rw [pow_succ]; omega

theorem pal_exists (n L : ℕ) (hn : 0 < n) (h10 : ¬ 10 ∣ n) (hL : n ≤ L)
    (h248 : n = 2 ∨ n = 4 ∨ n = 8 → 12 ≤ L) :
    ∃ P, (Nat.digits 10 P).length = L ∧ n ∣ P ∧ IsPal P := by
  obtain ⟨a, n1, h2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 (by norm_num)
  have hn1 : n1 ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨b, m, h5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn1 5 (by norm_num)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn1)
  have h2m : ¬ 2 ∣ m := fun h => h2 (Dvd.dvd.mul_left h _)
  have hc2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2m
  have hc5 : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5
  have hc : Nat.Coprime 10 m := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num]; exact Nat.coprime_mul_iff_left.2 ⟨hc2, hc5⟩
  have hab : a = 0 ∨ b = 0 := by
    by_contra h
    push Not at h
    apply h10
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact ⟨2 ^ a' * (5 ^ b' * m), by ring⟩
  rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
  · -- `n = m` is coprime to 10.
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    simp only [pow_zero, one_mul] at hL ⊢
    obtain ⟨r, hr1, hrm, h9⟩ := ord_bound m hm0 hc
    exact pal_U m L r hr1 (by omega) h9
  · set g := 2 ^ a * 5 ^ b with hg
    set e := a + b
    have hge : g ∣ 10 ^ e := by
      rw [show (10 : ℕ) ^ e = 2 ^ e * 5 ^ e by rw [← mul_pow]; norm_num]
      exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (Nat.pow_dvd_pow 5 (by omega))
    have hglt : g < 10 ^ e := by
      rw [hg, show (10 : ℕ) ^ e = 10 ^ a * 10 ^ b by rw [← pow_add]]
      rcases hab with ha | hb
      · subst ha
        simp only [pow_zero, one_mul]
        exact Nat.pow_lt_pow_left (by norm_num) (by omega)
      · subst hb
        simp only [pow_zero, mul_one]
        exact Nat.pow_lt_pow_left (by norm_num) (by omega)
    have hg0 : 0 < g := by positivity
    have hg10 : g % 10 ≠ 0 := by
      intro h
      apply h10
      exact (Nat.dvd_of_mod_eq_zero h).trans ⟨m, by rw [hg]; ring⟩
    have hcop : Nat.Coprime g m := Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.pow_left a hc2,
      Nat.Coprime.pow_left b hc5⟩
    have ht : 0 < φ m := Nat.totient_pos.2 hm0
    have h10R : 10 ^ (e * φ m) ≡ 1 [MOD m] := by
      have := (Nat.ModEq.pow_totient hc).pow e
      rw [one_pow, ← pow_mul, mul_comm] at this
      exact this
    have hmul : 2 ^ a * (5 ^ b * m) = g * m := by rw [hg]; ring
    rw [hmul] at hL ⊢
    apply pal_G g m e (e * φ m) L hg0 hge hglt hg10 hcop h10R (Nat.le_mul_of_pos_right e ht)
    -- Length bound `2 (e φ(m) + e) ≤ L`.
    have h2e : 2 * e ≤ g := by
      rcases hab with ha | hb
      · subst ha; simp only [pow_zero, one_mul, g, e, zero_add]
        have := four_mul_le5 b; omega
      · subst hb; simp only [pow_zero, mul_one, g, e, add_zero]
        exact two_mul_le a
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · have hm : m = 1 := by omega
      subst hm
      simp only [Nat.totient_one, mul_one] at hL ⊢
      rcases hab with ha | hb
      · subst ha; simp only [pow_zero, one_mul, g, e, zero_add] at hL ⊢
        have := four_mul_le5 b; omega
      · subst hb; simp only [pow_zero, mul_one, g, e, add_zero] at hL h248 ⊢
        rcases Nat.lt_or_ge a 4 with ha4 | ha4
        · have ha1 : 1 ≤ a := by omega
          have : 2 ^ a = 2 ∨ 2 ^ a = 4 ∨ 2 ^ a = 8 := by
            interval_cases a <;> simp
          have := h248 this
          omega
        · have := four_mul_le a ha4; omega
    · have hphi : φ m + 1 ≤ m := Nat.totient_lt m (by omega)
      have h1 : 2 * (e * φ m + e) ≤ 2 * e * m := by nlinarith
      have h2 : 2 * e * m ≤ g * m := Nat.mul_le_mul_right m h2e
      omega

theorem A084013_main (n : ℕ) (hn : 1 ≤ n) :
    ∃ N, (Nat.digits 10 N).length = n ∧ n ∣ N ∧ (¬ 10 ∣ n → IsPal N) ∧ (10 ∣ n → PalLZ n N) := by
  by_cases h10 : 10 ∣ n
  · obtain ⟨s, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 10 (by norm_num)
    have hs : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · subst h; simp at h10; exact absurd h10 hn'
      · exact h
    have hn'0 : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hsl : 10 * s ≤ 10 ^ s := by
      obtain ⟨c, rfl⟩ : ∃ c, s = c + 1 := ⟨s - 1, by omega⟩
      have : c < 10 ^ c := Nat.lt_pow_self (by norm_num)
      rw [pow_succ]; omega
    have hbig : 10 * (s * n') ≤ 10 ^ s * n' := by
      have := Nat.mul_le_mul_right n' hsl
      calc 10 * (s * n') = 10 * s * n' := by ring
        _ ≤ 10 ^ s * n' := this
    have hX1 : s ≤ s * n' := Nat.le_mul_of_pos_right s hn'0
    have hX2 : n' ≤ s * n' := Nat.le_mul_of_pos_left n' (by omega)
    set X := s * n'
    set Y := 10 ^ s * n'
    obtain ⟨u, hul, hnu, hpal⟩ := pal_exists n' (Y - s) hn'0 hn'
      (by omega) (by
        intro h
        have : 2 * s ≤ X := by
          rcases h with h | h | h <;> (rw [h] at hX2; simp only [X, h]; omega)
        omega)
    have hu0 : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · subst h; simp at hul; omega
      · exact h
    refine ⟨10 ^ s * u, ?_, Nat.mul_dvd_mul_left _ hnu, fun h => absurd h10 h,
      fun _ => ⟨s, n', u, rfl, hn', rfl, hpal⟩⟩
    rw [Nat.digits_base_pow_mul (by norm_num) hu0, List.length_append, List.length_replicate, hul]
    omega
  · by_cases h248 : n = 2 ∨ n = 4 ∨ n = 8
    · rcases h248 with rfl | rfl | rfl
      · exact ⟨22, by norm_num, by norm_num, fun _ => by norm_num [IsPal], fun h => by omega⟩
      · exact ⟨2112, by norm_num, by norm_num, fun _ => by norm_num [IsPal], fun h => by omega⟩
      · exact ⟨21100112, by norm_num, by norm_num, fun _ => by norm_num [IsPal], fun h => by omega⟩
    · obtain ⟨P, hPl, hnP, hpal⟩ := pal_exists n n (by omega) h10 le_rfl (fun h => absurd h h248)
      exact ⟨P, hPl, hnP, fun _ => hpal, fun h => absurd h h10⟩
