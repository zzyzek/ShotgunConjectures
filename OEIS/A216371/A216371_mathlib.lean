import Mathlib

/-
OEIS A216371: odd primes with one coach, i.e. primes p with A135303((p-1)/2) = 1,
A135303(n) = phi(2n+1) / (2 A003558(n)), A003558(n) = least m > 0 with 2^m = +-1 mod 2n+1.
Conjecture (G. W. Adamson, Sep 08 2012): for such p = 4q-1 or 4q+1 the top row of the coach
of p is a permutation of the first q odd integers.

Definitions.  `f p a` = odd part of p - a (one coach step: p - a = 2^k * f p a).
The coach top row is 1, f p 1, f p (f p 1), ... up to the first return to 1.
`sord r` = A003558(r) (Nat.find), `coaches r` = A135303(r) (natural-number division).

Main theorem.
* `A216371_coach`: p prime, 2 < p, coaches ((p-1)/2) = 1  ==>  (f p)^[(p+1)/4] 1 = 1, no earlier
  return to 1, and the list [(f p)^[j] 1 | j < (p+1)/4] is a permutation of [2i+1 | i < (p+1)/4].
Route.  `h` folds doubling on S = {1..r} (p = 2r+1), i.e. multiplication by 2 on (Z/p)/{+-1}
(`hit_cast`).  Greathouse's condition `NoSmallPm r` (no 0 < m < r with 2^m = +-1) makes the
h-orbit of 1 cover S (`hcover`, `hper`).  `f_rep`: f undoes a run of doublings (h^[k+1] (f a) = a
with even intermediate values); hence f is injective on odd elements of S (`f_inj`) and steps back
to the previous odd value along the h-cycle (`f_back`), so the f-orbit of 1 meets every odd element
of S (`odd_in_orbit`); counting gives the period q (`A216371_coach_of_noSmallPm`).
`noSmallPm_of_coaches`: coaches = 1 implies Greathouse's condition (2^r = +-1 by Fermat, sord | r).
Not checked here: nothing beyond the reading of "coach" (Hilton-Pedersen) as the orbit of 1 under f.
-/

namespace A216371

/-- Folding doubling on {1, ..., (b-1)/2}: multiplication by 2 on (ℤ/b)/±1. -/
def h (b x : ℕ) : ℕ := if 4 * x < b then 2 * x else b - 2 * x

/-- One coach step: the odd part of b - a. -/
def f (b a : ℕ) : ℕ := (b - a) / 2 ^ ((b - a).factorization 2)

variable {r : ℕ}

lemma h_S {x : ℕ} (hx1 : 1 ≤ x) (hx : x ≤ r) : 1 ≤ h (2*r+1) x ∧ h (2*r+1) x ≤ r := by
  unfold h; split_ifs <;> omega

lemma h_inj {x y : ℕ} (hx : x ≤ r) (hy : y ≤ r) (e : h (2*r+1) x = h (2*r+1) y) : x = y := by
  unfold h at e; split_ifs at e <;> omega

lemma hit_S (i : ℕ) {x : ℕ} (hx1 : 1 ≤ x) (hx : x ≤ r) :
    1 ≤ (h (2*r+1))^[i] x ∧ (h (2*r+1))^[i] x ≤ r := by
  induction i with
  | zero => exact ⟨hx1, hx⟩
  | succ i ih => rw [Function.iterate_succ_apply']; exact h_S ih.1 ih.2

lemma hit_inj (i : ℕ) {x y : ℕ} (hx1 : 1 ≤ x) (hx : x ≤ r) (hy1 : 1 ≤ y) (hy : y ≤ r)
    (e : (h (2*r+1))^[i] x = (h (2*r+1))^[i] y) : x = y := by
  induction i with
  | zero => exact e
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at e
    exact ih (h_inj (hit_S i hx1 hx).2 (hit_S i hy1 hy).2 e)

/-- The coach step undone by doubling: for odd a in S, c = f a is odd, in S, and
h^[k+1] c = a with all intermediate values even. -/
lemma f_rep {a : ℕ} (ha1 : 1 ≤ a) (har : a ≤ r) (hao : Odd a) :
    let c := f (2*r+1) a
    1 ≤ c ∧ c ≤ r ∧ Odd c ∧ ∃ k, (h (2*r+1))^[k+1] c = a ∧
      ∀ i, 0 < i → i < k + 1 → Even ((h (2*r+1))^[i] c) := by
  intro c
  set n := 2*r+1 - a with hn
  have hn0 : n ≠ 0 := by omega
  have hev : 2 ∣ n := by
    obtain ⟨t, ht⟩ := hao; exact ⟨r - t, by omega⟩
  have hk : 0 < n.factorization 2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 hev
  obtain ⟨k, hk'⟩ : ∃ k, n.factorization 2 = k + 1 := ⟨n.factorization 2 - 1, by omega⟩
  have hmul : 2 ^ (k+1) * c = n := by
    have := Nat.ordProj_mul_ordCompl_eq_self n 2
    simpa [c, f, hk', ← hn] using this
  have hodd : ¬ 2 ∣ c := by
    have := Nat.not_dvd_ordCompl Nat.prime_two hn0
    simpa [c, f, ← hn] using this
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hmul; omega
    · exact h0
  have hpow : 2 ≤ 2 ^ (k+1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn' : n + a = 2*r+1 := by omega
  have hcr : c ≤ r := by
    have := Nat.mul_le_mul_right c hpow
    omega
  -- h^[i] c = 2^i c for i ≤ k
  have hdbl : ∀ i, i ≤ k → (h (2*r+1))^[i] c = 2 ^ i * c := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      have : 4 * (2 ^ i * c) < 2*r+1 := by
        have h1 : 2 ^ (i+2) ≤ 2 ^ (k+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 := Nat.mul_le_mul_right c h1
        have e1 : 4 * (2 ^ i * c) = 2 ^ (i+2) * c := by ring
        omega
      simp only [h, this, ↓reduceIte]; ring
  refine ⟨hc1, hcr, Nat.odd_iff.mpr (by omega), k, ?_, ?_⟩
  · rw [Function.iterate_succ_apply', hdbl k le_rfl]
    have e1 : 2 * (2 ^ k * c) = n := by rw [← hmul]; ring
    have hn4 : ¬ 4 * (2 ^ k * c) < 2*r+1 := by omega
    simp only [h, hn4, ↓reduceIte]; omega
  · intro i hi0 hik
    rw [hdbl i (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact ⟨2 ^ j * c, by ring⟩

lemma f_inj {a a' : ℕ} (ha1 : 1 ≤ a) (har : a ≤ r) (hao : Odd a)
    (ha1' : 1 ≤ a') (har' : a' ≤ r) (hao' : Odd a') (e : f (2*r+1) a = f (2*r+1) a') : a = a' := by
  obtain ⟨-, -, -, k, hk, hev⟩ := f_rep ha1 har hao
  obtain ⟨-, -, -, k', hk', hev'⟩ := f_rep ha1' har' hao'
  rw [e] at hk hev
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd (hk ▸ hev' (k+1) (by omega) (by omega)) (Nat.not_even_iff_odd.mpr hao)
  · subst heq; exact hk.symm.trans hk'
  · exact absurd (hk' ▸ hev (k'+1) (by omega) (by omega)) (Nat.not_even_iff_odd.mpr hao')

lemma f_back {a i : ℕ} (ha1 : 1 ≤ a) (har : a ≤ r) (hao : Odd a) (hi : 0 < i)
    (hodd : Odd ((h (2*r+1))^[i] a))
    (hev : ∀ j, 0 < j → j < i → Even ((h (2*r+1))^[j] a)) :
    f (2*r+1) ((h (2*r+1))^[i] a) = a := by
  have hS := hit_S i ha1 har
  obtain ⟨hc1, hcr, hco, k, hk, hevc⟩ := f_rep hS.1 hS.2 hodd
  set c := f (2*r+1) ((h (2*r+1))^[i] a)
  rcases lt_trichotomy (k+1) i with hlt | heq | hgt
  · have e : (h (2*r+1))^[k+1] c = (h (2*r+1))^[k+1] ((h (2*r+1))^[i - (k+1)] a) := by
      rw [hk, ← Function.iterate_add_apply]; congr 1; omega
    have := hit_inj (k+1) hc1 hcr (hit_S _ ha1 har).1 (hit_S _ ha1 har).2 e
    exact absurd (this ▸ hev (i - (k+1)) (by omega) (by omega)) (Nat.not_even_iff_odd.mpr hco)
  · subst heq; exact hit_inj (k+1) hc1 hcr ha1 har hk
  · have e : (h (2*r+1))^[i] ((h (2*r+1))^[k+1-i] c) = (h (2*r+1))^[i] a := by
      rw [← Function.iterate_add_apply, ← hk]; congr 1; omega
    have := hit_inj i (hit_S _ hc1 hcr).1 (hit_S _ hc1 hcr).2 ha1 har e
    exact absurd (this ▸ hevc (k+1-i) (by omega) (by omega)) (Nat.not_even_iff_odd.mpr hao)

lemma h_cast {x : ℕ} (hxr : x ≤ r) :
    ((h (2*r+1) x : ℕ) : ZMod (2*r+1)) = 2 * x ∨ ((h (2*r+1) x : ℕ) : ZMod (2*r+1)) = -(2 * x) := by
  unfold h
  split_ifs with hx
  · left; push_cast; ring
  · right
    rw [Nat.cast_sub (by omega)]
    have : ((2*r+1 : ℕ) : ZMod (2*r+1)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    rw [this]; ring

lemma hit_cast (hr : 1 ≤ r) (j : ℕ) :
    (((h (2*r+1))^[j] 1 : ℕ) : ZMod (2*r+1)) = 2 ^ j ∨
    (((h (2*r+1))^[j] 1 : ℕ) : ZMod (2*r+1)) = -(2 ^ j) := by
  induction j with
  | zero => left; simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hS := hit_S j (le_refl 1) hr
    rcases h_cast (r := r) hS.2 with e | e <;> rw [e] <;> rcases ih with e' | e' <;> rw [e'] <;>
      [left; right; right; left] <;> ring

/-- Greathouse's form of membership: 2^m is not ±1 mod 2r+1 for 0 < m < r. -/
def NoSmallPm (r : ℕ) : Prop :=
  ∀ m, 0 < m → m < r → ¬ (2 ^ m ≡ 1 [MOD 2*r+1]) ∧ ¬ (2 ^ m + 1 ≡ 0 [MOD 2*r+1])

lemma two_unit : IsUnit (2 : ZMod (2*r+1)) := by
  refine isUnit_iff_exists_inv.mpr ⟨((r + 1 : ℕ) : ZMod (2*r+1)), ?_⟩
  have : ((2*r+1 : ℕ) : ZMod (2*r+1)) = 0 := ZMod.natCast_self _
  have e : (2 : ZMod (2*r+1)) * ((r + 1 : ℕ) : ZMod (2*r+1)) = ((2*r+1 : ℕ) : ZMod (2*r+1)) + 1 := by
    push_cast; ring
  rw [e, this, zero_add]

lemma hit_distinct (hr : 1 ≤ r) (hyp : NoSmallPm r) {i j : ℕ} (hij : i < j) (hjr : j - i < r)
    (e : (h (2*r+1))^[i] 1 = (h (2*r+1))^[j] 1) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
  have hm := hyp m (by omega) (by omega)
  have hu : IsUnit ((2 : ZMod (2*r+1)) ^ i) := two_unit.pow i
  have ec := congrArg (fun n : ℕ => (n : ZMod (2*r+1))) e
  have h1 : (2 : ZMod (2*r+1)) ^ m = 1 → False := by
    intro h; apply hm.1
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast; exact h
  have h2 : (2 : ZMod (2*r+1)) ^ m = -1 → False := by
    intro h; apply hm.2
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast; rw [h]; ring
  rcases hit_cast hr i with a | a <;> rcases hit_cast hr (i+m) with b | b <;>
    rw [a, b, pow_add] at ec
  · exact h1 (hu.mul_left_cancel (by rw [mul_one]; exact ec.symm))
  · exact h2 (hu.mul_left_cancel (by linear_combination ec))
  · exact h2 (hu.mul_left_cancel (by linear_combination -ec))
  · exact h1 (hu.mul_left_cancel (by linear_combination ec))

lemma hcover (hr : 1 ≤ r) (hyp : NoSmallPm r) {x : ℕ} (hx1 : 1 ≤ x) (hxr : x ≤ r) :
    ∃ j < r, (h (2*r+1))^[j] 1 = x := by
  have hsub : (Finset.range r).image (fun j => (h (2*r+1))^[j] 1) ⊆ Finset.Icc 1 r := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_Icc.mpr (hit_S j (le_refl 1) hr)
  have hcard : ((Finset.range r).image (fun j => (h (2*r+1))^[j] 1)).card = r := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hit_distinct hr hyp hlt (by omega) e
    · exact hit_distinct hr hyp hgt (by omega) e.symm
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Nat.card_Icc]; omega)
  have hx : x ∈ Finset.Icc 1 r := Finset.mem_Icc.mpr ⟨hx1, hxr⟩
  rw [← heq] at hx
  obtain ⟨j, hj, e⟩ := Finset.mem_image.mp hx
  exact ⟨j, Finset.mem_range.mp hj, e⟩

lemma hper (hr : 1 ≤ r) (hyp : NoSmallPm r) : (h (2*r+1))^[r] 1 = 1 := by
  obtain ⟨j, hj, e⟩ := hcover hr hyp (hit_S r (le_refl 1) hr).1 (hit_S r (le_refl 1) hr).2
  rcases Nat.eq_zero_or_pos j with j0 | jpos
  · subst j0; exact e.symm
  · have e2 : (h (2*r+1))^[j] ((h (2*r+1))^[r-j] 1) = (h (2*r+1))^[j] 1 := by
      rw [← Function.iterate_add_apply, e]; congr 1; omega
    have e3 := hit_inj j (hit_S _ (le_refl 1) hr).1 (hit_S _ (le_refl 1) hr).2 (le_refl 1) hr e2
    exact (hit_distinct (i := 0) (j := r - j) hr hyp (by omega) (by omega) e3.symm).elim

lemma fit_S (t : ℕ) {a : ℕ} (ha1 : 1 ≤ a) (har : a ≤ r) (hao : Odd a) :
    1 ≤ (f (2*r+1))^[t] a ∧ (f (2*r+1))^[t] a ≤ r ∧ Odd ((f (2*r+1))^[t] a) := by
  induction t with
  | zero => exact ⟨ha1, har, hao⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, h3, -⟩ := f_rep ih.1 ih.2.1 ih.2.2
    exact ⟨h1, h2, h3⟩

lemma fit_inj (t : ℕ) {a a' : ℕ} (ha1 : 1 ≤ a) (har : a ≤ r) (hao : Odd a)
    (ha1' : 1 ≤ a') (har' : a' ≤ r) (hao' : Odd a')
    (e : (f (2*r+1))^[t] a = (f (2*r+1))^[t] a') : a = a' := by
  induction t with
  | zero => exact e
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at e
    have A := fit_S t ha1 har hao
    have B := fit_S t ha1' har' hao'
    exact ih (f_inj A.1 A.2.1 A.2.2 B.1 B.2.1 B.2.2 e)

lemma odd_in_orbit (hr : 1 ≤ r) (hyp : NoSmallPm r) {x : ℕ} (hx1 : 1 ≤ x) (hxr : x ≤ r)
    (hxo : Odd x) : ∃ t, (f (2*r+1))^[t] 1 = x := by
  have key : ∀ d j, j + d = r → Odd ((h (2*r+1))^[j] 1) →
      ∃ t, (f (2*r+1))^[t] 1 = (h (2*r+1))^[j] 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hjd hodd
      rcases Nat.eq_zero_or_pos d with d0 | dpos
      · refine ⟨0, ?_⟩
        rw [show j = r by omega, hper hr hyp]; rfl
      · classical
        set a := (h (2*r+1))^[j] 1 with ha
        have hP : ∃ i, 0 < i ∧ Odd ((h (2*r+1))^[i] a) := by
          refine ⟨r - j, by omega, ?_⟩
          rw [ha, ← Function.iterate_add_apply, show r - j + j = r by omega, hper hr hyp]
          exact odd_one
        set i := Nat.find hP with hi
        have hspec := Nat.find_spec hP
        have hle : i ≤ r - j := Nat.find_min' hP ⟨by omega, by
          rw [ha, ← Function.iterate_add_apply, show r - j + j = r by omega, hper hr hyp]
          exact odd_one⟩
        have hev : ∀ i', 0 < i' → i' < i → Even ((h (2*r+1))^[i'] a) := by
          intro i' h0 hlt
          by_contra hne
          exact Nat.find_min hP hlt ⟨h0, Nat.not_even_iff_odd.mp hne⟩
        have e1 : (h (2*r+1))^[i] a = (h (2*r+1))^[j + i] 1 := by
          rw [ha, ← Function.iterate_add_apply, Nat.add_comm i j]
        obtain ⟨t, ht⟩ := ih (r - (j + i)) (by omega) (j + i) (by omega) (e1 ▸ hspec.2)
        have hS := hit_S j (le_refl 1) hr
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply', ht, ← e1]
        exact f_back hS.1 hS.2 hodd hspec.1 hspec.2 hev
  obtain ⟨j, hj, rfl⟩ := hcover hr hyp hx1 hxr
  exact key (r - j) j (by omega) hxo

end A216371

open A216371 in
/-- The coach of p = 2r+1 (top row: iterate a ↦ odd part of p - a from 1 until it returns to 1),
under Greathouse's condition (no 0 < m < (p-1)/2 with 2^m ≡ ±1 mod p): the top row has length
q = (p+1)/4 and is a permutation of 1, 3, ..., 2q-1. -/
theorem A216371_coach_of_noSmallPm (r : ℕ) (hr : 1 ≤ r) (hyp : NoSmallPm r) :
    (f (2*r+1))^[(2*r+1+1)/4] 1 = 1 ∧
    (∀ j, 0 < j → j < (2*r+1+1)/4 → (f (2*r+1))^[j] 1 ≠ 1) ∧
    ((List.range ((2*r+1+1)/4)).map (fun j => (f (2*r+1))^[j] 1)).Perm
      ((List.range ((2*r+1+1)/4)).map (fun i => 2*i+1)) := by
  set q := (2*r+1+1)/4 with hq
  set g : ℕ → ℕ := fun t => (f (2*r+1))^[t] 1 with hg
  set O := (Finset.range q).image (fun i => 2*i+1) with hO
  have memO : ∀ x, x ∈ O ↔ 1 ≤ x ∧ x ≤ r ∧ Odd x := by
    intro x
    simp only [hO, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨by omega, by omega, ⟨i, by ring⟩⟩
    · rintro ⟨h1, h2, ⟨i, rfl⟩⟩; exact ⟨i, by omega, by ring⟩
  have cardO : O.card = q := by
    rw [hO, Finset.card_image_of_injective _ (fun a b e => by simpa using e), Finset.card_range]
  have gS : ∀ t, g t ∈ O := fun t => (memO _).mpr (fit_S t (le_refl 1) hr odd_one)
  have hdist : ∀ i j, i < j → j < q → g i = g j → False := by
    intro i j hij hjq e
    have e2 : (f (2*r+1))^[i] 1 = (f (2*r+1))^[i] ((f (2*r+1))^[j - i] 1) := by
      rw [← Function.iterate_add_apply]; simp only [hg] at e; rw [e]; congr 1; omega
    have hS := fit_S (j - i) (r := r) (le_refl 1) hr odd_one
    have e3 := fit_inj i (le_refl 1) hr odd_one hS.1 hS.2.1 hS.2.2 e2
    have hpp : Function.IsPeriodicPt (f (2*r+1)) (j - i) 1 := e3.symm
    have hsub : O ⊆ (Finset.range (j - i)).image g := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := (memO x).mp hx
      obtain ⟨t, ht⟩ := odd_in_orbit hr hyp h1 h2 h3
      refine Finset.mem_image.mpr ⟨t % (j - i), Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
      simp only [hg]; rw [hpp.iterate_mod_apply]; exact ht
    have := Finset.card_le_card hsub
    have := Finset.card_image_le (s := Finset.range (j - i)) (f := g)
    rw [Finset.card_range] at this
    omega
  have hinj : Set.InjOn g (Finset.range q) := by
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hdist i j hlt hj e
    · exact hdist j i hgt hi e.symm
  have himg : (Finset.range q).image g = O := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx; exact gS t
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range, cardO]
  refine ⟨?_, ?_, ?_⟩
  · have hq0 : 0 < q := by omega
    have hm : g q ∈ (Finset.range q).image g := by rw [himg]; exact gS q
    obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with i0 | ipos
    · subst i0; exact e.symm
    · exfalso
      have e2 : (f (2*r+1))^[i] ((f (2*r+1))^[q - i] 1) = (f (2*r+1))^[i] 1 := by
        rw [← Function.iterate_add_apply, show i + (q - i) = q by omega]; exact e.symm
      have hS := fit_S (q - i) (r := r) (le_refl 1) hr odd_one
      have e3 := fit_inj i hS.1 hS.2.1 hS.2.2 (le_refl 1) hr odd_one e2
      exact hdist 0 (q - i) (by omega) (by omega) e3.symm
  · intro j hj0 hjq e
    exact hdist 0 j hj0 hjq (by simp only [hg]; rw [e]; rfl)
  · rw [List.perm_ext_iff_of_nodup]
    · intro x
      have h1 : x ∈ (List.range q).map g ↔ x ∈ O := by
        rw [← himg]; simp [Finset.mem_image]
      have h2 : x ∈ (List.range q).map (fun i => 2*i+1) ↔ x ∈ O := by
        simp [hO, Finset.mem_image]
      exact h1.trans h2.symm
    · exact (List.nodup_range).map_on (fun a ha b hb e => hinj (by simpa using ha) (by simpa using hb) e)
    · exact (List.nodup_range).map (fun a b e => by simpa using e)

namespace A216371

lemma exists_pm (r : ℕ) : ∃ m, 0 < m ∧ (2 ^ m ≡ 1 [MOD 2*r+1] ∨ 2 ^ m + 1 ≡ 0 [MOD 2*r+1]) := by
  refine ⟨Nat.totient (2*r+1), Nat.totient_pos.mpr (by omega), Or.inl (Nat.ModEq.pow_totient ?_)⟩
  rw [Nat.coprime_two_left]; exact ⟨r, by ring⟩

/-- A003558(r): least m > 0 with 2^m ≡ ±1 (mod 2r+1) (suborder of 2). -/
noncomputable def sord (r : ℕ) : ℕ := Nat.find (exists_pm r)

/-- A135303(r) = phi(2r+1) / (2 A003558(r)): the number of coaches of 2r+1. -/
noncomputable def coaches (r : ℕ) : ℕ := Nat.totient (2*r+1) / (2 * sord r)

lemma pm_iff (r m : ℕ) :
    (2 ^ m ≡ 1 [MOD 2*r+1] ∨ 2 ^ m + 1 ≡ 0 [MOD 2*r+1]) ↔
    ((2 : ZMod (2*r+1)) ^ m = 1 ∨ (2 : ZMod (2*r+1)) ^ m = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; linear_combination h
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h]; ring

lemma noSmallPm_of_coaches (r : ℕ) (hp : (2*r+1).Prime) (hc : coaches r = 1) : NoSmallPm r := by
  have : Fact (2*r+1).Prime := ⟨hp⟩
  intro m hm0 hmr
  rw [← not_or]; intro hAB
  have hs_le : sord r ≤ m := Nat.find_min' (exists_pm r) ⟨hm0, hAB⟩
  have hs := Nat.find_spec (exists_pm r)
  have hsZ := (pm_iff r (sord r)).mp hs.2
  have hs0 : 0 < sord r := hs.1
  have h2ne : (2 : ZMod (2*r+1)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod (2*r+1)) = ((0 : ℕ) : ZMod (2*r+1)) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at h'
    omega
  have hferm : (2 : ZMod (2*r+1)) ^ (2*r) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one h2ne
    simpa using this
  have hrpm : (2 : ZMod (2*r+1)) ^ r = 1 ∨ (2 : ZMod (2*r+1)) ^ r = -1 := by
    rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul]; exact hferm
  have hdecomp : (2 : ZMod (2*r+1)) ^ r =
      ((2 : ZMod (2*r+1)) ^ sord r) ^ (r / sord r) * (2 : ZMod (2*r+1)) ^ (r % sord r) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hupm : ((2 : ZMod (2*r+1)) ^ sord r) ^ (r / sord r) = 1 ∨
      ((2 : ZMod (2*r+1)) ^ sord r) ^ (r / sord r) = -1 := by
    rcases hsZ with h | h <;> rw [h]
    · left; exact one_pow _
    · exact neg_one_pow_eq_or _ _
  have hvpm : (2 : ZMod (2*r+1)) ^ (r % sord r) = 1 ∨ (2 : ZMod (2*r+1)) ^ (r % sord r) = -1 := by
    rcases hupm with hu | hu <;> rw [hu] at hdecomp <;> rcases hrpm with hr | hr <;> rw [hr] at hdecomp
    · left; linear_combination -hdecomp
    · right; linear_combination -hdecomp
    · right; linear_combination hdecomp
    · left; linear_combination hdecomp
  have hmod : r % sord r = 0 := by
    by_contra hne
    exact Nat.find_min (exists_pm r) (Nat.mod_lt r hs0)
      ⟨Nat.pos_of_ne_zero hne, (pm_iff r _).mpr hvpm⟩
  have htot : Nat.totient (2*r+1) = 2 * r := by rw [Nat.totient_prime hp]; omega
  unfold coaches at hc
  rw [htot, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)] at hc
  have := Nat.div_add_mod r (sord r)
  rw [hc, hmod] at this
  omega

end A216371

/-- OEIS A216371 (odd primes with one coach) and Adamson's conjecture: if p is an odd prime with
A135303((p-1)/2) = phi(p)/(2 A003558((p-1)/2)) = 1, then the top row of its coach (iterate
a ↦ odd part of p - a from a = 1 until the first return to 1) has q = (p+1)/4 entries and is a
permutation of 1, 3, ..., 2q-1 (p = 4q-1 or 4q+1). -/
theorem A216371_coach (p : ℕ) (hp : p.Prime) (h2 : 2 < p) (hone : A216371.coaches ((p - 1) / 2) = 1) :
    (A216371.f p)^[(p+1)/4] 1 = 1 ∧
    (∀ j, 0 < j → j < (p+1)/4 → (A216371.f p)^[j] 1 ≠ 1) ∧
    ((List.range ((p+1)/4)).map (fun j => (A216371.f p)^[j] 1)).Perm
      ((List.range ((p+1)/4)).map (fun i => 2*i+1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, p = 2*r+1 := by
    rcases hp.eq_two_or_odd' with h | ⟨r, hr⟩
    · omega
    · exact ⟨r, hr⟩
  have hr : (2*r+1-1)/2 = r := by omega
  rw [hr] at hone
  exact A216371_coach_of_noSmallPm r (by omega) (A216371.noSmallPm_of_coaches r hp hone)

open A216371
