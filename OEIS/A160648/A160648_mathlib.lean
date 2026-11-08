/-
OEIS A160648, Mathlib proof of the conjectured interpretation.

Definitions (as in the entries): pp m = number of partitions of m (Fintype.card of
Nat.Partition m); A053445(n) = p(n+2) - 2p(n+1) + p(n); A160644(n) = A053445(2n);
A160648(n) = A160644(n) - 2 A160644(n-1) + A160644(n-2) (n >= 2; this reproduces the data
0, 1, 0, 0, 2, ... from a(2) on). cc m = number of partitions of m with all parts >= 3 whose
largest part has multiplicity >= 3 (the three largest parts equal).

Main theorem `A160648_conj`: for n >= 2, A160648 n = cc (2n+2) + [n = 2]; the extra 1 at
n = 2 is the partition 222 of the conjecture.

Proof: removing a part 1 or 2 (`q_rec`, via Nat.Partition.partitionWithPartEquiv) gives
p(j) - p(j-1) = q2(j) and q2(j) - q2(j-2) = q3(j); lowering the r copies of the largest part
by one (`dn`, inverse `upm`, `E_eq`) gives E_r(m) = g_r(m-r) for m != 3r, where E_r / g_r
count partitions with parts >= 3 whose largest part has multiplicity exactly / at least r;
the exception m = 6, r = 2 is the partition 3+3 (`E26`).

Checked here: the full statement for every n >= 2. Not checked here: a(1) = 0 (data value,
not covered by the second-difference formula as indexed here).
-/
import Mathlib
open Finset Nat.Partition

/-- partitions of m with every part ≥ k -/
def q (k m : ℕ) : ℕ := #(Nat.Partition.restricted m (k ≤ ·))

theorem q_one (m : ℕ) : q 1 m = Fintype.card (Nat.Partition m) := by
  rw [q, Nat.Partition.restricted, ← Finset.card_univ]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  intro i hi
  exact x.parts_pos hi

theorem q_rec {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) : q k m = q (k + 1) m + q k (m - k) := by
  rw [q, ← Finset.card_filter_add_card_filter_not (fun x : m.Partition => k ∈ x.parts)]
  rw [add_comm]
  congr 1
  · rw [q]
    congr 1
    ext x
    simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      have := h1 i hi
      rcases Nat.eq_or_lt_of_le this with h | h
      · subst h; exact absurd hi h2
      · exact h
    · intro h
      exact ⟨fun i hi => le_of_lt (h i hi), fun hk' => absurd (h k hk') (lt_irrefl k)⟩
  · rw [q]
    refine Finset.card_bij' (fun x hx => Nat.Partition.partitionWithPartEquiv hk hkm
        ⟨x, (Finset.mem_filter.mp hx).2⟩)
      (fun y _ => ((Nat.Partition.partitionWithPartEquiv hk hkm).symm y).1) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      intro i hi
      rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
      exact hx.1 i (Multiset.mem_of_mem_erase hi)
    · intro y hy
      simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts, Multiset.mem_cons] at hi
        rcases hi with rfl | hi
        · exact le_refl _
        · exact hy i hi
      · rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]; exact Multiset.mem_cons_self _ _
    · intro x hx
      simp
    · intro y hy
      simp

theorem sup_add_rep {ν : Multiset ℕ} {a r : ℕ} (hr : 1 ≤ r) (h : ∀ x ∈ ν, x ≤ a) :
    (ν + Multiset.replicate r a).sup = a := by
  rw [Multiset.sup_add]
  have h1 : ν.sup ≤ a := Multiset.sup_le.2 h
  have h2 : (Multiset.replicate r a).sup = a :=
    le_antisymm (Multiset.sup_le.2 fun x hx => (Multiset.eq_of_mem_replicate hx).le)
      (Multiset.le_sup (Multiset.mem_replicate.2 ⟨by omega, rfl⟩))
  rw [h2]; exact max_eq_right h1

/-- partitions of m, parts ≥ 3 -/
def S (m : ℕ) : Finset m.Partition := Nat.Partition.restricted m (3 ≤ ·)

/-- largest part has multiplicity ≥ r -/
def gg (r m : ℕ) : ℕ := #((S m).filter fun x => r ≤ x.parts.count x.parts.sup)
/-- largest part has multiplicity exactly r -/
def E (r m : ℕ) : ℕ := #((S m).filter fun x => x.parts.count x.parts.sup = r)

theorem gg_split (r m : ℕ) : gg r m = gg (r + 1) m + E r m := by
  rw [gg, gg, E, ← Finset.card_filter_add_card_filter_not (s := (S m).filter fun x => r ≤ x.parts.count x.parts.sup)
    (fun x : m.Partition => r + 1 ≤ x.parts.count x.parts.sup)]
  congr 2
  · ext x; simp only [Finset.mem_filter]
    grind
  · ext x; simp only [Finset.mem_filter]
    grind

theorem sup_mem_of_ne_zero (s : Multiset ℕ) (hs : s ≠ 0) : s.sup ∈ s := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a t ih =>
    rw [Multiset.sup_cons]
    by_cases ht : t = 0
    · subst ht; simp
    · rcases max_choice a t.sup with h | h
      · rw [h]; exact Multiset.mem_cons_self _ _
      · rw [h]; exact Multiset.mem_cons_of_mem (ih ht)

theorem q3_eq_gg1 {m : ℕ} (hm : 1 ≤ m) : q 3 m = gg 1 m := by
  rw [q, gg]
  congr 1
  ext x
  simp only [S, Finset.mem_filter, iff_self_and]
  intro _
  have hne : x.parts ≠ 0 := by
    intro h0; have := x.parts_sum; rw [h0] at this; simp at this; omega
  have hmem : x.parts.sup ∈ x.parts := by
    exact sup_mem_of_ne_zero _ hne
  exact Multiset.one_le_count_iff_mem.2 hmem

open Multiset in
/-- lower the r copies of the largest part by one -/
def dn (r : ℕ) (s : Multiset ℕ) : Multiset ℕ := s - replicate r s.sup + replicate r (s.sup - 1)

open Multiset in
/-- raise r copies of the largest part by one -/
def upm (r : ℕ) (s : Multiset ℕ) : Multiset ℕ := s - replicate r s.sup + replicate r (s.sup + 1)

open Multiset in
theorem rest_le_sup (s : Multiset ℕ) (r y : ℕ) (hy : y ∈ s - replicate r s.sup) : y ≤ s.sup :=
  Multiset.le_sup (Multiset.mem_of_le (Multiset.sub_le_self _ _) hy)

open Multiset in
theorem decomp {s : Multiset ℕ} {r : ℕ} (h : r ≤ count s.sup s) :
    s - replicate r s.sup + replicate r s.sup = s :=
  Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.1 h)

open Multiset in
/-- facts about `dn` for a partition whose largest part has multiplicity exactly r -/
theorem dn_facts {s : Multiset ℕ} {r m : ℕ} (hr : 1 ≤ r) (hc : count s.sup s = r)
    (h3 : ∀ i ∈ s, 3 ≤ i) (hsum : s.sum = m) (hm : m ≠ 3 * r) :
    4 ≤ s.sup ∧ (dn r s).sup = s.sup - 1 ∧ r ≤ count (dn r s).sup (dn r s) ∧
      (∀ i ∈ dn r s, 3 ≤ i) ∧ (dn r s).sum = m - r := by
  set L := s.sup with hL
  set ν := s - replicate r L with hν
  have hdec : ν + replicate r L = s := decomp (le_of_eq hc.symm)
  have hcν : count L ν = 0 := by
    rw [hν, Multiset.count_sub, Multiset.count_replicate_self]; omega
  have hlt : ∀ y ∈ ν, y ≤ L - 1 := by
    intro y hy
    have h1 := rest_le_sup s r y hy
    have h2 : y ≠ L := by
      rintro rfl; rw [Multiset.count_eq_zero] at hcν; exact hcν hy
    omega
  have hLmem : L ∈ s := by
    rw [← Multiset.one_le_count_iff_mem]; omega
  have hL3 : 3 ≤ L := h3 L hLmem
  have hνmem : ∀ y ∈ ν, y ∈ s := fun y hy => Multiset.mem_of_le (Multiset.sub_le_self _ _) hy
  have hL4 : 4 ≤ L := by
    by_contra hcon
    have hL3' : L = 3 := by omega
    have hν0 : ν = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro y hy
      have := hlt y hy; have := h3 y (hνmem y hy); omega
    rw [hν0, zero_add] at hdec
    have : s.sum = 3 * r := by rw [← hdec, Multiset.sum_replicate, hL3', smul_eq_mul]; ring
    omega
  have hsumν : ν.sum + r * L = m := by
    rw [← hsum, ← hdec, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
  have hdn : dn r s = ν + replicate r (L - 1) := rfl
  have hsup : (dn r s).sup = L - 1 := by rw [hdn]; exact sup_add_rep hr hlt
  refine ⟨hL4, hsup, ?_, ?_, ?_⟩
  · rw [hsup, hdn, Multiset.count_add, Multiset.count_replicate_self]; omega
  · intro i hi
    rw [hdn, Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact h3 i (hνmem i hi)
    · rw [Multiset.eq_of_mem_replicate hi]; omega
  · rw [hdn, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    have : r * (L - 1) + r = r * L := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

open Multiset in
theorem upm_facts {s : Multiset ℕ} {r n : ℕ} (hr : 1 ≤ r) (hc : r ≤ count s.sup s)
    (h3 : ∀ i ∈ s, 3 ≤ i) (hsum : s.sum = n) :
    (upm r s).sup = s.sup + 1 ∧ count (upm r s).sup (upm r s) = r ∧
      (∀ i ∈ upm r s, 3 ≤ i) ∧ (upm r s).sum = n + r := by
  set L := s.sup with hL
  set ν := s - replicate r L with hν
  have hdec : ν + replicate r L = s := decomp hc
  have hle : ∀ y ∈ ν, y ≤ L := fun y hy => rest_le_sup s r y hy
  have hνmem : ∀ y ∈ ν, y ∈ s := fun y hy => Multiset.mem_of_le (Multiset.sub_le_self _ _) hy
  have hLmem : L ∈ s := by rw [← Multiset.one_le_count_iff_mem]; omega
  have hL3 : 3 ≤ L := h3 L hLmem
  have hup : upm r s = ν + replicate r (L + 1) := rfl
  have hsup : (upm r s).sup = L + 1 := by
    rw [hup]; exact sup_add_rep hr fun y hy => Nat.le_succ_of_le (hle y hy)
  have hsumν : ν.sum + r * L = n := by
    rw [← hsum, ← hdec, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
  refine ⟨hsup, ?_, ?_, ?_⟩
  · rw [hsup, hup, Multiset.count_add, Multiset.count_replicate_self, Multiset.count_eq_zero.2]
    · simp
    · intro hm; have := hle _ hm; omega
  · intro i hi
    rw [hup, Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact h3 i (hνmem i hi)
    · rw [Multiset.eq_of_mem_replicate hi]; omega
  · rw [hup, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    rw [Nat.mul_succ]; omega

theorem upm_dn {s : Multiset ℕ} {r m : ℕ} (hr : 1 ≤ r) (hc : s.count s.sup = r)
    (h3 : ∀ i ∈ s, 3 ≤ i) (hsum : s.sum = m) (hm : m ≠ 3 * r) : upm r (dn r s) = s := by
  obtain ⟨hL4, hsup, -, -, -⟩ := dn_facts hr hc h3 hsum hm
  have hdn : dn r s = (s - Multiset.replicate r s.sup) + Multiset.replicate r (s.sup - 1) := rfl
  rw [upm, hsup, hdn, Multiset.add_sub_cancel_right, show s.sup - 1 + 1 = s.sup by omega]
  exact decomp (le_of_eq hc.symm)

theorem dn_upm {s : Multiset ℕ} {r n : ℕ} (hr : 1 ≤ r) (hc : r ≤ s.count s.sup)
    (h3 : ∀ i ∈ s, 3 ≤ i) (hsum : s.sum = n) : dn r (upm r s) = s := by
  obtain ⟨hsup, -, -, -⟩ := upm_facts hr hc h3 hsum
  have hup : upm r s = (s - Multiset.replicate r s.sup) + Multiset.replicate r (s.sup + 1) := rfl
  rw [dn, hsup, hup, Multiset.add_sub_cancel_right, show s.sup + 1 - 1 = s.sup by omega]
  exact decomp hc

theorem memS {m : ℕ} (x : m.Partition) : x ∈ S m ↔ ∀ i ∈ x.parts, 3 ≤ i := by
  simp [S, Nat.Partition.restricted]

theorem E_eq {r m : ℕ} (hr : 1 ≤ r) (hrm : r ≤ m) (hm : m ≠ 3 * r) : E r m = gg r (m - r) := by
  rw [E, gg]
  refine Finset.card_bij'
    (fun x hx => (⟨dn r x.parts,
      fun {i} hi => by
        have h := (Finset.mem_filter.1 hx)
        have := (dn_facts hr h.2 ((memS x).1 h.1) x.parts_sum hm).2.2.2.1 i hi
        omega,
      (dn_facts hr (Finset.mem_filter.1 hx).2 ((memS x).1 (Finset.mem_filter.1 hx).1)
        x.parts_sum hm).2.2.2.2⟩ : (m - r).Partition))
    (fun y hy => (⟨upm r y.parts,
      fun {i} hi => by
        have h := (Finset.mem_filter.1 hy)
        have := (upm_facts hr h.2 ((memS y).1 h.1) y.parts_sum).2.2.1 i hi
        omega,
      by
        have h := (Finset.mem_filter.1 hy)
        rw [(upm_facts hr h.2 ((memS y).1 h.1) y.parts_sum).2.2.2]
        omega⟩ : m.Partition)) ?_ ?_ ?_ ?_
  · intro x hx
    have h := Finset.mem_filter.1 hx
    obtain ⟨-, -, hc, h3, -⟩ := dn_facts hr h.2 ((memS x).1 h.1) x.parts_sum hm
    exact Finset.mem_filter.2 ⟨(memS _).2 h3, hc⟩
  · intro y hy
    have h := Finset.mem_filter.1 hy
    obtain ⟨-, hc, h3, -⟩ := upm_facts hr h.2 ((memS y).1 h.1) y.parts_sum
    exact Finset.mem_filter.2 ⟨(memS _).2 h3, hc⟩
  · intro x hx
    have h := Finset.mem_filter.1 hx
    exact Nat.Partition.ext (upm_dn hr h.2 ((memS x).1 h.1) x.parts_sum hm)
  · intro y hy
    have h := Finset.mem_filter.1 hy
    exact Nat.Partition.ext (dn_upm hr h.2 ((memS y).1 h.1) y.parts_sum)

theorem three_mul_le {j r : ℕ} (x : j.Partition) (hx : x ∈ S j) (hr : 1 ≤ r)
    (hc : r ≤ x.parts.count x.parts.sup) : 3 * r ≤ j := by
  have hdec := decomp hc
  have hLmem : x.parts.sup ∈ x.parts := by rw [← Multiset.one_le_count_iff_mem]; omega
  have hL3 := (memS x).1 hx _ hLmem
  have hs := x.parts_sum
  rw [← hdec, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at hs
  have := Nat.mul_le_mul_left r hL3
  omega

theorem gg_small {r j : ℕ} (hr : 1 ≤ r) (hj : j < 3 * r) : gg r j = 0 := by
  rw [gg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hc
  have := three_mul_le x hx hr hc
  omega

/-- the partition 3+3 -/
def p33 : (6 : ℕ).Partition := ⟨{3, 3}, by decide, by decide⟩

theorem E26 : E 2 6 = 1 := by
  rw [E, Finset.card_eq_one]
  refine ⟨p33, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hc⟩
    have hdec := decomp (le_of_eq hc.symm)
    have hLmem : x.parts.sup ∈ x.parts := by rw [← Multiset.one_le_count_iff_mem]; omega
    have hL3 := (memS x).1 hx _ hLmem
    have hs := x.parts_sum
    rw [← hdec, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at hs
    have hν0 : (x.parts - Multiset.replicate 2 x.parts.sup).sum = 0 := by omega
    have hL : x.parts.sup = 3 := by omega
    have hν : x.parts - Multiset.replicate 2 x.parts.sup = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro y hy
      have hy3 := (memS x).1 hx y (Multiset.mem_of_le (Multiset.sub_le_self _ _) hy)
      have := Multiset.le_sum_of_mem hy
      omega
    apply Nat.Partition.ext
    rw [← hdec, hν, zero_add, hL]
    rfl
  · rintro rfl
    refine ⟨(memS _).2 (by decide), by decide⟩

/-- p(m): number of partitions of m -/
def pp (m : ℕ) : ℤ := Fintype.card m.Partition

/-- A053445(n) = p(n+2) - 2 p(n+1) + p(n) -/
def A053445 (n : ℕ) : ℤ := pp (n + 2) - 2 * pp (n + 1) + pp n

/-- A160644(n) = A053445(2n) (even bisection) -/
def A160644 (n : ℕ) : ℤ := A053445 (2 * n)

/-- A160648(n) = second differences of A160644, n ≥ 2 -/
def A160648 (n : ℕ) : ℤ := A160644 n - 2 * A160644 (n - 1) + A160644 (n - 2)

/-- c(m): partitions of m with all parts ≥ 3 and the three largest parts equal
(largest part of multiplicity ≥ 3) -/
def cc (m : ℕ) : ℕ := gg 3 m

/-- **A160648 conjecture.** For n ≥ 2, a(n) = c(2n+2) + [n = 2] (the extra 1 is 222). -/
theorem A160648_conj {n : ℕ} (hn : 2 ≤ n) :
    A160648 n = (cc (2 * n + 2) : ℤ) + (if n = 2 then 1 else 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  -- p(j) = q2(j) + p(j-1)
  have P : ∀ j, 1 ≤ j → pp j = (q 2 j : ℤ) + pp (j - 1) := by
    intro j hj
    have := q_rec (k := 1) (m := j) le_rfl hj
    rw [q_one, q_one] at this
    rw [pp, pp, this]; push_cast; ring
  -- q2(j) = q3(j) + q2(j-2)
  have Q : ∀ j, 2 ≤ j → (q 2 j : ℤ) = q 3 j + q 2 (j - 2) := by
    intro j hj
    have := q_rec (k := 2) (m := j) (by norm_num) hj
    rw [this]; push_cast; ring
  have G1 : ∀ j, 1 ≤ j → (gg 1 j : ℤ) = q 3 j := fun j hj => by rw [q3_eq_gg1 hj]
  have S1 : ∀ j, 1 ≤ j → j ≠ 3 → (gg 2 j : ℤ) = gg 1 j - gg 1 (j - 1) := by
    intro j hj hj3
    have h1 := gg_split 1 j
    have h2 := E_eq (r := 1) (m := j) le_rfl hj (by omega)
    rw [h1, h2]; push_cast; ring
  have S2 : (cc (2 * (k + 2) + 2) : ℤ) = gg 2 (2 * k + 6) - E 2 (2 * k + 6) := by
    have h1 := gg_split 2 (2 * k + 6)
    rw [cc, show 2 * (k + 2) + 2 = 2 * k + 6 by ring, h1]; push_cast; ring
  have E2 : (E 2 (2 * k + 6) : ℤ) = gg 2 (2 * k + 4) + (if k = 0 then 1 else 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [E26, gg_small (r := 2) (j := 4) (by norm_num) (by norm_num)]
    · rw [E_eq (by norm_num) (by omega) (by omega), show 2 * k + 6 - 2 = 2 * k + 4 by omega]
      simp [show k ≠ 0 by omega]
  have hA : A160648 (k + 2) = pp (2 * k + 6) - 2 * pp (2 * k + 5) - pp (2 * k + 4) + 4 * pp (2 * k + 3)
      - pp (2 * k + 2) - 2 * pp (2 * k + 1) + pp (2 * k) := by
    simp only [A160648, A160644, A053445, show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    ring_nf
  rw [hA, S2, E2, S1 (2 * k + 6) (by omega) (by omega), S1 (2 * k + 4) (by omega) (by omega),
    show 2 * k + 6 - 1 = 2 * k + 5 by omega, show 2 * k + 4 - 1 = 2 * k + 3 by omega,
    G1 _ (by omega), G1 _ (by omega), G1 _ (by omega), G1 _ (by omega)]
  have p6 := P (2 * k + 6) (by omega)
  have p5 := P (2 * k + 5) (by omega)
  have p4 := P (2 * k + 4) (by omega)
  have p3 := P (2 * k + 3) (by omega)
  have p2 := P (2 * k + 2) (by omega)
  have p1 := P (2 * k + 1) (by omega)
  have q6 := Q (2 * k + 6) (by omega)
  have q5 := Q (2 * k + 5) (by omega)
  have q4 := Q (2 * k + 4) (by omega)
  have q3 := Q (2 * k + 3) (by omega)
  simp only [show 2 * k + 6 - 1 = 2 * k + 5 by omega, show 2 * k + 5 - 1 = 2 * k + 4 by omega,
    show 2 * k + 4 - 1 = 2 * k + 3 by omega, show 2 * k + 3 - 1 = 2 * k + 2 by omega,
    show 2 * k + 2 - 1 = 2 * k + 1 by omega, show 2 * k + 1 - 1 = 2 * k by omega,
    show 2 * k + 6 - 2 = 2 * k + 4 by omega, show 2 * k + 5 - 2 = 2 * k + 3 by omega,
    show 2 * k + 4 - 2 = 2 * k + 2 by omega, show 2 * k + 3 - 2 = 2 * k + 1 by omega] at *
  have hk2 : (k + 2 = 2) ↔ k = 0 := by omega
  simp only [hk2]
  linarith
