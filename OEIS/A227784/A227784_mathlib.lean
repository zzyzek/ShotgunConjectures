/-
OEIS A227781 (least number of squares which add to -1 mod n) and
OEIS A227784 (least number of fourth powers which add to -1 mod n).

Checked here (Lean + Mathlib, no sorry, no native_decide):
* `A227781_conjecture`: for n >= 1, a(n) = 4 iff 8 | n, and a(n) = 3 iff n = 4 (mod 8);
  `A227781_le_two`: a(n) <= 2 when 4 does not divide n.
* `A227784_corrected`: for n >= 1, b(n) = 15 if n = 0 (mod 16), b(n) = 7 if n = 8 (mod 16),
  and b(n) <= 4 if 8 does not divide n.
* `A227784_literal_false`: the conjecture as printed ("a(n) = 15 if n = 9 mod 16") fails at n = 9.

Definitions: `IsRep d n k` says that -1 is a sum of k d-th powers in `ZMod n`;
`a n` and `b n` are the least such k for d = 2 and d = 4 (`sInf`), as in the OEIS names.
Declarations live in namespace A227784 (left open so the axiom check can name them).
Not checked in Lean: agreement of `a`, `b` with the b-files (certificate/check.py).
-/
import Mathlib

open Finset
open scoped Pointwise

namespace A227784

/-- -1 is a sum of `k` `d`-th powers in `ZMod n`. -/
def IsRep (d n k : ℕ) : Prop := ∃ x : Fin k → ZMod n, ∑ i, x i ^ d = -1

/-- OEIS A227781: least number of squares which add to -1 mod n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | IsRep 2 n k}

/-- OEIS A227784: least number of fourth powers which add to -1 mod n. -/
noncomputable def b (n : ℕ) : ℕ := sInf {k | IsRep 4 n k}

lemma isRep_mono {d n k m : ℕ} (hd : 0 < d) (h : IsRep d n k) (hkm : k ≤ m) :
    IsRep d n m := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  refine ⟨Fin.append x (fun _ : Fin j => 0), ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, zero_pow hd.ne', hx]

lemma sInf_eq_of {d n k : ℕ} (hd : 0 < d) (h : IsRep d n (k + 1)) (hn : ¬ IsRep d n k) :
    sInf {j | IsRep d n j} = k + 1 := by
  refine le_antisymm (Nat.sInf_le h) (le_csInf ⟨k + 1, h⟩ fun j hj => ?_)
  by_contra hlt
  exact hn (isRep_mono hd hj (by omega))

lemma isRep_one (d k : ℕ) : IsRep d 1 k := ⟨fun _ => 0, Subsingleton.elim _ _⟩

lemma isRep_mul {d m n k : ℕ} (h : m.Coprime n) (hm : IsRep d m k) (hn : IsRep d n k) :
    IsRep d (m * n) k := by
  obtain ⟨x, hx⟩ := hm
  obtain ⟨y, hy⟩ := hn
  let e := (ZMod.chineseRemainder h).symm
  refine ⟨fun i => e (x i, y i), ?_⟩
  have h1 : ∑ i, e (x i, y i) ^ d = e (∑ i, (x i, y i) ^ d) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_pow e _ d).symm
  have h2 : ∑ i, (x i, y i) ^ d = (-1 : ZMod m × ZMod n) := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, hx, hy]
  rw [h1, h2, map_neg, map_one]

lemma isRep_of_dvd {d m n k : ℕ} (hmn : m ∣ n) (h : IsRep d n k) : IsRep d m k := by
  obtain ⟨x, hx⟩ := h
  refine ⟨fun i => ZMod.castHom hmn (ZMod m) (x i), ?_⟩
  simp only [← map_pow, ← map_sum, hx, map_neg, map_one]

/-! ### Hensel lifting at an odd prime -/

lemma lift_step {p : ℕ} (hp : p.Prime) (P : ℤ → ℤ) {y c D : ℤ}
    (hP : ∀ s, ∃ r, P (y + s) = P y + D * s + s ^ 2 * r) (hD : ¬ (p : ℤ) ∣ D) {j : ℕ}
    (h : (p : ℤ) ^ (j + 1) ∣ P y + c) :
    ∃ y', (p : ℤ) ∣ y' - y ∧ (p : ℤ) ^ (j + 2) ∣ P y' + c := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨u, v, huv⟩ := ((hpZ.irreducible.coprime_iff_not_dvd).mpr hD).symm
  obtain ⟨t, ht⟩ := h
  obtain ⟨r, hr⟩ := hP ((p : ℤ) ^ (j + 1) * (-t * u))
  refine ⟨y + (p : ℤ) ^ (j + 1) * (-t * u), ⟨(p : ℤ) ^ j * (-t * u), by ring⟩,
    ⟨t * v + (p : ℤ) ^ j * ((t * u) ^ 2 * r), ?_⟩⟩
  rw [hr]
  linear_combination ht - ((p : ℤ) ^ (j + 1) * t) * huv

lemma not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have h' : p ∣ 2 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

lemma lift_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ} (hd : d = 2 ∨ d = 4) {c y : ℤ}
    (hy : ¬ (p : ℤ) ∣ y) (h : (p : ℤ) ∣ y ^ d + c) (j : ℕ) :
    ∃ y', ¬ (p : ℤ) ∣ y' ∧ (p : ℤ) ^ (j + 1) ∣ y' ^ d + c := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  induction j with
  | zero => exact ⟨y, hy, by simpa using h⟩
  | succ j ih =>
    obtain ⟨y1, hy1, h1⟩ := ih
    have key : ∃ y', (p : ℤ) ∣ y' - y1 ∧ (p : ℤ) ^ (j + 2) ∣ y' ^ d + c := by
      rcases hd with rfl | rfl
      · refine lift_step hp (fun z => z ^ 2) (D := 2 * y1) (fun s => ⟨1, by ring⟩) ?_ h1
        intro h2
        rcases hpZ.dvd_or_dvd h2 with h3 | h3
        · exact not_dvd_two hp hp2 h3
        · exact hy1 h3
      · refine lift_step hp (fun z => z ^ 4) (D := 4 * y1 ^ 3)
          (fun s => ⟨6 * y1 ^ 2 + 4 * y1 * s + s ^ 2, by ring⟩) ?_ h1
        intro h2
        rcases hpZ.dvd_or_dvd h2 with h3 | h3
        · exact not_dvd_two hp hp2 (hpZ.dvd_of_dvd_pow (n := 2) (by norm_num at h3 ⊢; exact h3))
        · exact hy1 (hpZ.dvd_of_dvd_pow h3)
    obtain ⟨y2, hd2, h2⟩ := key
    refine ⟨y2, fun h3 => hy1 ?_, h2⟩
    simpa using dvd_sub h3 hd2

lemma rep_prime_pow {d k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : d = 2 ∨ d = 4)
    (base : ∃ y : ZMod p, y ≠ 0 ∧ ∃ z : Fin k → ZMod p, y ^ d + ∑ i, z i ^ d = -1)
    (j : ℕ) : IsRep d (p ^ (j + 1)) (k + 1) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨y, hy0, z, hz⟩ := base
  have hYc : (((y.val : ℕ) : ℤ) : ZMod p) = y := by simp
  have hZc : ∀ i, ((((z i).val : ℕ) : ℤ) : ZMod p) = z i := fun i => by simp
  have hy : ¬ (p : ℤ) ∣ ((y.val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hYc]; exact hy0
  have h : (p : ℤ) ∣ ((y.val : ℕ) : ℤ) ^ d + (∑ i, (((z i).val : ℕ) : ℤ) ^ d + 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [hYc, hZc]
    linear_combination hz
  obtain ⟨Y, -, hY⟩ := lift_pow hp hp2 hd hy h j
  refine ⟨Fin.cons (Y : ZMod (p ^ (j + 1))) (fun i => ((((z i).val : ℕ) : ℤ) : ZMod (p ^ (j + 1)))), ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ (j + 1))).mpr (by exact_mod_cast hY)
  push_cast at h3 ⊢
  linear_combination h3

lemma rep_odd {d k : ℕ} (hd : d = 2 ∨ d = 4)
    (base : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ y : ZMod p, y ≠ 0 ∧ ∃ z : Fin k → ZMod p, y ^ d + ∑ i, z i ^ d = -1) :
    ∀ m, Odd m → IsRep d m (k + 1) := by
  intro m
  induction m using Nat.recOnPrimeCoprime with
  | zero => intro h; simp at h
  | prime_pow p n hp =>
    intro hodd
    have hp' : p.Prime := hp
    cases n with
    | zero => simpa using isRep_one d (k + 1)
    | succ j =>
      have hp2 : p ≠ 2 := by
        rintro rfl
        have := (Nat.odd_pow_iff (Nat.succ_ne_zero j)).mp hodd
        exact (Nat.not_odd_iff_even.mpr even_two) this
      exact rep_prime_pow hp' hp2 hd (base p hp' hp2) j
  | coprime a b _ _ hab iha ihb =>
    intro h
    have h' := Nat.odd_mul.mp h
    exact isRep_mul hab (iha h'.1) (ihb h'.2)

/-! ### Odd moduli: two squares, four fourth powers -/

lemma base2 (p : ℕ) (hp : p.Prime) :
    ∃ y : ZMod p, y ≠ 0 ∧ ∃ z : Fin 1 → ZMod p, y ^ 2 + ∑ i, z i ^ 2 = -1 := by
  have := Fact.mk hp
  obtain ⟨u, v, h⟩ := ZMod.sq_add_sq p (-1)
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      rintro rfl
      subst hu
      simp at h
    exact ⟨v, hv, fun _ => u, by simp; linear_combination h⟩
  · exact ⟨u, hu, fun _ => v, by simp; linear_combination h⟩

lemma base4 (p : ℕ) (hp : p.Prime) :
    ∃ y : ZMod p, y ≠ 0 ∧ ∃ z : Fin 3 → ZMod p, y ^ 4 + ∑ i, z i ^ 4 = -1 := by
  classical
  have := Fact.mk hp
  set A : Finset (ZMod p) := univ.image (fun x => x ^ 4) with hA
  set U : Finset (ZMod p) := univ.erase 0 with hUdef
  set T : Finset (ZMod p) := U.image (fun x => x ^ 4) with hTdef
  have hU : #U = p - 1 := by simp [U, Finset.card_erase_of_mem, ZMod.card]
  have hfib : ∀ c ∈ U.image (fun x : ZMod p => x ^ 4), #{x ∈ U | x ^ 4 = c} ≤ 4 := by
    intro c _
    calc #{x ∈ U | x ^ 4 = c} ≤ #(Polynomial.nthRootsFinset 4 c) := by
          apply card_le_card
          intro x hx
          simp only [mem_filter] at hx
          rw [Polynomial.mem_nthRootsFinset (by norm_num)]
          exact hx.2
      _ ≤ 4 := by
          rw [Polynomial.nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 4 c)
  have hUT : #U ≤ 4 * #T := card_le_mul_card_image U 4 hfib
  have h0T : (0 : ZMod p) ∉ T := by
    simp only [T, U, mem_image, mem_erase]
    rintro ⟨x, ⟨hx, _⟩, h⟩
    exact hx (pow_eq_zero_iff (by norm_num) |>.mp h)
  have hTA : insert 0 T ⊆ A := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_image.mpr ⟨0, mem_univ _, by simp⟩
    · obtain ⟨y, _, rfl⟩ := mem_image.mp hx
      exact mem_image_of_mem _ (mem_univ _)
  have hA' : #T + 1 ≤ #A := by
    have := card_le_card hTA
    rwa [card_insert_of_notMem h0T] at this
  have hp1 : 2 ≤ p := hp.two_le
  have hAn : A.Nonempty := ⟨0, mem_image.mpr ⟨0, mem_univ _, by simp⟩⟩
  have c2 := ZMod.cauchy_davenport hp hAn hAn
  have c3 := ZMod.cauchy_davenport hp (hAn.add hAn) hAn
  have c4 := ZMod.cauchy_davenport hp ((hAn.add hAn).add hAn) hAn
  rw [min_le_iff] at c2 c3 c4
  have hle : #(A + A + A + A) ≤ p := by
    simpa [ZMod.card] using card_le_univ (A + A + A + A)
  have hcard : #(A + A + A + A) = p := by omega
  have huniv : A + A + A + A = univ := eq_univ_of_card _ (by rw [hcard, ZMod.card])
  have hm : (-1 : ZMod p) ∈ A + A + A + A := huniv ▸ mem_univ _
  obtain ⟨s3, hs3, a4, ha4, h4⟩ := mem_add.mp hm
  obtain ⟨s2, hs2, a3, ha3, h3⟩ := mem_add.mp hs3
  obtain ⟨a1, ha1, a2, ha2, h2⟩ := mem_add.mp hs2
  obtain ⟨y1, -, rfl⟩ := mem_image.mp ha1
  obtain ⟨y2, -, rfl⟩ := mem_image.mp ha2
  obtain ⟨y3, -, rfl⟩ := mem_image.mp ha3
  obtain ⟨y4, -, rfl⟩ := mem_image.mp ha4
  have hs : y1 ^ 4 + y2 ^ 4 + y3 ^ 4 + y4 ^ 4 = -1 := by rw [← h4, ← h3, ← h2]
  by_cases g1 : y1 = 0
  · by_cases g2 : y2 = 0
    · by_cases g3 : y3 = 0
      · by_cases g4 : y4 = 0
        · subst g1 g2 g3 g4
          simp at hs
        · exact ⟨y4, g4, ![y1, y2, y3], by simp [Fin.sum_univ_three]; linear_combination hs⟩
      · exact ⟨y3, g3, ![y1, y2, y4], by simp [Fin.sum_univ_three]; linear_combination hs⟩
    · exact ⟨y2, g2, ![y1, y3, y4], by simp [Fin.sum_univ_three]; linear_combination hs⟩
  · exact ⟨y1, g1, ![y2, y3, y4], by simp [Fin.sum_univ_three]; linear_combination hs⟩

lemma rep2_odd (m : ℕ) (hm : Odd m) : IsRep 2 m 2 :=
  rep_odd (k := 1) (Or.inl rfl) (fun p hp _ => base2 p hp) m hm

lemma rep4_odd (m : ℕ) (hm : Odd m) : IsRep 4 m 4 :=
  rep_odd (k := 3) (Or.inr rfl) (fun p hp _ => base4 p hp) m hm

/-! ### Powers of two -/

lemma two_adic (f : ℕ) : ∃ y : ℤ, Odd y ∧ (2 : ℤ) ^ (f + 4) ∣ y ^ 4 + 15 := by
  induction f with
  | zero => exact ⟨1, odd_one, by norm_num⟩
  | succ f ih =>
    obtain ⟨y, hy, t, ht⟩ := ih
    rcases Int.even_or_odd t with ⟨w, hw⟩ | htodd
    · exact ⟨y, hy, ⟨w, by rw [ht, hw]; ring⟩⟩
    · obtain ⟨w, hw⟩ := Odd.add_odd htodd (hy.pow (n := 3))
      refine ⟨y + 2 ^ (f + 2), ?_, ⟨w + 3 * y ^ 2 * 2 ^ f + y * 2 ^ (2 * f + 3) + 2 ^ (3 * f + 3), ?_⟩⟩
      · exact hy.add_even ⟨2 ^ (f + 1), by ring⟩
      · linear_combination ht + (2 : ℤ) ^ (f + 4) * hw

lemma rep_two_pow (f : ℕ) : IsRep 4 (2 ^ (f + 4)) 15 := by
  obtain ⟨y, -, hy⟩ := two_adic f
  have : NeZero (2 ^ (f + 4)) := ⟨by positivity⟩
  refine ⟨Fin.cons (y : ZMod (2 ^ (f + 4))) (fun _ : Fin 14 => 1), ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ (f + 4))).mpr (by exact_mod_cast hy)
  push_cast at h3
  linear_combination h3

/-! ### Lower bounds by residues -/

lemma sum01 {M k : ℕ} (x : Fin k → ZMod M) (h : ∀ i, x i ^ 4 = 0 ∨ x i ^ 4 = 1) :
    ∃ c ≤ k, ∑ i, x i ^ 4 = (c : ZMod M) := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc, hs⟩ := ih (fun i => x i.succ) (fun i => h _)
    rw [Fin.sum_univ_succ, hs]
    rcases h 0 with h0 | h0
    · exact ⟨c, by omega, by rw [h0]; ring⟩
    · exact ⟨c + 1, by omega, by rw [h0]; push_cast; ring⟩

lemma lower_count {M k : ℕ} (hM : 0 < M) (h01 : ∀ x : ZMod M, x ^ 4 = 0 ∨ x ^ 4 = 1)
    (h : IsRep 4 M k) : M - 1 ≤ k := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨c, hc, hs⟩ := sum01 x (fun i => h01 _)
  rw [hs] at hx
  have h1 : ((c + 1 : ℕ) : ZMod M) = 0 := by push_cast; rw [hx]; ring
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by omega) h1
  omega

lemma not_rep_16 : ¬ IsRep 4 16 14 := fun h => by
  have := lower_count (by norm_num) (by decide) h
  omega

lemma not_rep_8 : ¬ IsRep 4 8 6 := fun h => by
  have := lower_count (by norm_num) (by decide) h
  omega

lemma not_sq_8 : ¬ IsRep 2 8 3 := by
  rintro ⟨x, hx⟩
  rw [Fin.sum_univ_three] at hx
  have key : ∀ u v w : ZMod 8, u ^ 2 + v ^ 2 + w ^ 2 ≠ -1 := by decide
  exact key _ _ _ hx

lemma not_sq_4 : ¬ IsRep 2 4 2 := by
  rintro ⟨x, hx⟩
  rw [Fin.sum_univ_two] at hx
  have key : ∀ u v : ZMod 4, u ^ 2 + v ^ 2 ≠ -1 := by decide
  exact key _ _ hx

lemma coprime_two_pow {m : ℕ} (hm : Odd m) (e : ℕ) : Nat.Coprime (2 ^ e) m := by
  refine Nat.Coprime.pow_left e ((Nat.prime_two.coprime_iff_not_dvd).mpr ?_)
  obtain ⟨r, rfl⟩ := hm
  omega

/-! ### A227781 -/

lemma a_eq_four {n : ℕ} (hn : 0 < n) (h8 : 8 ∣ n) : a n = 4 := by
  refine sInf_eq_of (k := 3) (by norm_num) ?_ (fun h => not_sq_8 (isRep_of_dvd h8 h))
  obtain ⟨p, q, r, s, h⟩ := Nat.sum_four_squares (n - 1)
  refine ⟨![(p : ZMod n), q, r, s], ?_⟩
  have hc : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
  rw [← hc, ← h]
  simp [Fin.sum_univ_four]

lemma a_eq_three {n : ℕ} (h4 : n % 8 = 4) : a n = 3 := by
  refine sInf_eq_of (k := 2) (by norm_num) ?_
    (fun h => not_sq_4 (isRep_of_dvd (by omega) h))
  have hodd : Odd (n / 4) := ⟨n / 8, by omega⟩
  have h4' : IsRep 2 4 3 := ⟨fun _ => 1, by decide⟩
  have := isRep_mul (coprime_two_pow hodd 2) h4' (isRep_mono (by norm_num) (rep2_odd _ hodd)
    (by norm_num : 2 ≤ 3))
  have hn : 2 ^ 2 * (n / 4) = n := by omega
  rwa [hn] at this

theorem A227781_le_two {n : ℕ} (h4 : ¬ 4 ∣ n) : a n ≤ 2 := by
  apply Nat.sInf_le
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn
  · have hodd : Odd m := by
      rcases Nat.even_or_odd m with ⟨r, hr⟩ | h
      · exact absurd ⟨r, by omega⟩ h4
      · exact h
    have h2 : IsRep 2 2 2 := ⟨![1, 0], by decide⟩
    have := isRep_mul (coprime_two_pow hodd 1) h2 (rep2_odd m hodd)
    have hn' : 2 ^ 1 * m = n := by omega
    rwa [hn'] at this
  · exact rep2_odd n hn

/-- The A227781 conjecture: a(n) = 4 iff 8 | n, and a(n) = 3 iff n = 4 (mod 8). -/
theorem A227781_conjecture (n : ℕ) (hn : 0 < n) :
    (a n = 4 ↔ 8 ∣ n) ∧ (a n = 3 ↔ n % 8 = 4) := by
  by_cases h8 : 8 ∣ n
  · have := a_eq_four hn h8
    refine ⟨⟨fun _ => h8, fun _ => this⟩, ⟨fun h => by omega, fun h => by omega⟩⟩
  · by_cases h4 : n % 8 = 4
    · have := a_eq_three h4
      refine ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun _ => h4, fun _ => this⟩⟩
    · have := A227781_le_two (n := n) (by omega)
      refine ⟨⟨fun h => by omega, fun h => absurd h h8⟩, ⟨fun h => by omega, fun h => absurd h h4⟩⟩

/-! ### A227784 -/

lemma b_eq_15 {n : ℕ} (hn : 0 < n) (h16 : n % 16 = 0) : b n = 15 := by
  refine sInf_eq_of (k := 14) (by norm_num) ?_
    (fun h => not_rep_16 (isRep_of_dvd (by omega) h))
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have he : 4 ≤ e := by
    have h1 : 2 ^ 4 ∣ 2 ^ e * m := by omega
    have h2 := (Nat.Coprime.dvd_of_dvd_mul_right (coprime_two_pow hm 4) h1)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' he
  exact isRep_mul (coprime_two_pow hm _) (rep_two_pow f)
    (isRep_mono (by norm_num) (rep4_odd m hm) (by norm_num))

lemma b_eq_7 {n : ℕ} (h8 : n % 16 = 8) : b n = 7 := by
  refine sInf_eq_of (k := 6) (by norm_num) ?_
    (fun h => not_rep_8 (isRep_of_dvd (by omega) h))
  have hodd : Odd (n / 8) := ⟨n / 16, by omega⟩
  have h8' : IsRep 4 8 7 := ⟨fun _ => 1, by decide⟩
  have := isRep_mul (coprime_two_pow hodd 3) h8' (isRep_mono (by norm_num) (rep4_odd _ hodd)
    (by norm_num : 4 ≤ 7))
  have hn : 2 ^ 3 * (n / 8) = n := by omega
  rwa [hn] at this

lemma b_le_4 {n : ℕ} (h8 : n % 8 ≠ 0) : b n ≤ 4 := by
  apply Nat.sInf_le
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn
  · rcases Nat.even_or_odd m with ⟨r, hr⟩ | hmo
    · have hodd : Odd r := by
        rcases Nat.even_or_odd r with ⟨s, hs⟩ | h
        · omega
        · exact h
      have h2 : IsRep 4 4 4 := ⟨![1, 1, 1, 0], by decide⟩
      have := isRep_mul (coprime_two_pow hodd 2) h2 (rep4_odd r hodd)
      have hn' : 2 ^ 2 * r = n := by omega
      rwa [hn'] at this
    · have h2 : IsRep 4 2 4 := ⟨![1, 0, 0, 0], by decide⟩
      have := isRep_mul (coprime_two_pow hmo 1) h2 (rep4_odd m hmo)
      have hn' : 2 ^ 1 * m = n := by omega
      rwa [hn'] at this
  · exact rep4_odd n hn

/-- The A227784 conjecture with "9 mod 16" read as "0 mod 16". -/
theorem A227784_corrected (n : ℕ) (hn : 0 < n) :
    (n % 16 = 0 → b n = 15) ∧ (n % 16 = 8 → b n = 7) ∧ (n % 8 ≠ 0 → b n ≤ 4) :=
  ⟨b_eq_15 hn, b_eq_7, b_le_4⟩

/-- The conjecture as printed ("a(n) = 15 if n = 9 mod 16") is false: b(9) <= 2. -/
theorem A227784_literal_false : ¬ ∀ n, n % 16 = 9 → b n = 15 := by
  intro h
  have h9 : b 9 ≤ 2 := Nat.sInf_le (⟨![1, 2], by decide⟩ : IsRep 4 9 2)
  have := h 9 (by norm_num)
  omega

