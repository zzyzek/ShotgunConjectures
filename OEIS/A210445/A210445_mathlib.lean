import Mathlib
import OpenProblemsLib.ArithFactor

/-
OEIS-A210445 (Mathlib). a(n) = least k ≥ 1 with k n practical (m is practical when every
j ≤ m is a sum of distinct divisors of m). Conjecture (Sun 2013): a(n) < n for n > 1 and
a(n) < n/2 for n > 47. README result: true.

Main theorem `A210445_main`: (1) every n > 1 has some k with 0 < k < n and `Practical (k * n)`;
(2) every n > 47 has some k with 0 < k, 2k < n and `Practical (k * n)`. Since a(n) is the least
such k, these are exactly a(n) < n and a(n) < n/2.

Proof. Sufficient direction of the Stewart–Sierpiński criterion: if every j ≤ σ(m) is a sum of
distinct divisors of m (`RepF`), q is a prime not dividing m and q ≤ σ(m) + 1, then the same
holds for m q^e (divisors of m q^(e+1) = divisors of m ⊔ q · divisors of m q^e; write
j = r + q s with r ≤ σ(m), s ≤ σ(m q^e)). Hence 2^t n is practical when every prime factor of
n is ≤ 2^(t+1) (`pt`); this gives (1) with 2^t ≤ n - 1 and (2) for composite n with
2^t ≤ (n-1)/2. Primes 47 < p ≤ 840: a table of k and the factorisation of k p in increasing
order, each step checked (`chk`, trial-division primality from OpenProblemsLib.ArithFactor) by
`decide +kernel`, and coverage of all primes in the range checked the same way. Primes p > 840:
k from the family 2^(a+2)·105, 2^(a+2)·165 with σ = 192 (2^(a+3) - 1), 288 (2^(a+3) - 1); the
first member with p ≤ σ(k) + 1 satisfies 2k < p.

Outside Lean: nothing. (The table was produced by a Python search; Lean checks it.)
-/

open Finset OpenProblemsLib OpenProblemsLib.ArithFactor

/-- m is practical: every j ≤ m is a sum of distinct divisors of m. -/
def Practical (m : ℕ) : Prop := ∀ j ≤ m, ∃ s ⊆ m.divisors, ∑ x ∈ s, x = j

/-- Every j up to the sum of A is a subset sum of A. -/
def RepF (A : Finset ℕ) : Prop := ∀ j ≤ ∑ x ∈ A, x, ∃ s ⊆ A, ∑ x ∈ s, x = j

def mulE (q : ℕ) (hq : 0 < q) : ℕ ↪ ℕ := ⟨fun x => q * x, fun _ _ h => Nat.eq_of_mul_eq_mul_left hq h⟩

theorem rep_union {A B : Finset ℕ} {q : ℕ} (hq : 0 < q) (hA : RepF A) (hB : RepF B)
    (hqA : q ≤ ∑ x ∈ A, x + 1) (hdis : Disjoint A (B.map (mulE q hq))) :
    RepF (A ∪ B.map (mulE q hq)) ∧
      ∑ x ∈ A ∪ B.map (mulE q hq), x = ∑ x ∈ A, x + q * ∑ x ∈ B, x := by
  have hsum : ∑ x ∈ A ∪ B.map (mulE q hq), x = ∑ x ∈ A, x + q * ∑ x ∈ B, x := by
    rw [sum_union hdis, sum_map, mul_sum]; rfl
  refine ⟨?_, hsum⟩
  intro j hj
  rw [hsum] at hj
  set SA := ∑ x ∈ A, x
  set SB := ∑ x ∈ B, x
  obtain ⟨r, t, hr, ht, hjrt⟩ : ∃ r t, r ≤ SA ∧ t ≤ SB ∧ j = r + q * t := by
    by_cases h : j ≤ q * SB
    · refine ⟨j % q, j / q, ?_, ?_, (Nat.mod_add_div j q).symm⟩
      · have := Nat.mod_lt j hq; omega
      · exact Nat.div_le_of_le_mul h
    · exact ⟨j - q * SB, SB, by omega, le_rfl, by omega⟩
  obtain ⟨s₁, hs₁, hs₁r⟩ := hA r hr
  obtain ⟨s₂, hs₂, hs₂t⟩ := hB t ht
  refine ⟨s₁ ∪ s₂.map (mulE q hq), union_subset_union hs₁ (map_subset_map.2 hs₂), ?_⟩
  rw [sum_union (disjoint_of_subset_left hs₁ (disjoint_of_subset_right (map_subset_map.2 hs₂)
    hdis)), sum_map, hs₁r, hjrt]
  show r + ∑ x ∈ s₂, q * x = r + q * t
  rw [← mul_sum, hs₂t]

theorem divisors_step {m q : ℕ} (hm : 0 < m) (hq : q.Prime) (e : ℕ) :
    (m * q ^ (e + 1)).divisors = m.divisors ∪ (m * q ^ e).divisors.map (mulE q hq.pos) := by
  ext d
  simp only [mem_union, mem_map, Nat.mem_divisors, mulE]
  have hne : m * q ^ (e + 1) ≠ 0 := (Nat.mul_pos hm (pow_pos hq.pos _)).ne'
  have hne' : m * q ^ e ≠ 0 := (Nat.mul_pos hm (pow_pos hq.pos _)).ne'
  constructor
  · rintro ⟨hd, -⟩
    by_cases hqd : q ∣ d
    · obtain ⟨x, rfl⟩ := hqd
      right
      refine ⟨x, ⟨?_, hne'⟩, rfl⟩
      have : q * x ∣ q * (m * q ^ e) := by rw [show q * (m * q ^ e) = m * q ^ (e + 1) by ring]; exact hd
      exact Nat.dvd_of_mul_dvd_mul_left hq.pos this
    · left
      have hc : Nat.Coprime d (q ^ (e + 1)) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd)))
      exact ⟨hc.dvd_of_dvd_mul_right hd, hm.ne'⟩
  · rintro (⟨hd, -⟩ | ⟨x, ⟨hx, -⟩, rfl⟩)
    · exact ⟨hd.mul_right _, hne⟩
    · refine ⟨?_, hne⟩
      rw [show m * q ^ (e + 1) = q * (m * q ^ e) by ring]
      exact mul_dvd_mul_left q hx

theorem divisors_step_disj {m q : ℕ} (hq : q.Prime) (hqm : ¬q ∣ m) (e : ℕ) :
    Disjoint m.divisors ((m * q ^ e).divisors.map (mulE q hq.pos)) := by
  rw [disjoint_left]
  intro d hd hd'
  simp only [mem_map, mulE] at hd'
  obtain ⟨x, -, rfl⟩ := hd'
  exact hqm ((dvd_mul_right q x).trans (Nat.dvd_of_mem_divisors hd))

theorem gsum_succ' (q e : ℕ) : 1 + q * gsum q e = gsum q (e + 1) := by
  rw [gsum_eq, gsum_eq, sum_range_succ' (fun k => q ^ k) (e + 1), mul_sum, add_comm, pow_zero]
  congr 1
  apply sum_congr rfl
  intro k _
  ring

theorem step {m S q : ℕ} (hm : 0 < m) (hR : RepF m.divisors) (hS : ∑ x ∈ m.divisors, x = S)
    (hq : q.Prime) (hqm : ¬q ∣ m) (hqS : q ≤ S + 1) :
    ∀ e, RepF (m * q ^ e).divisors ∧ ∑ x ∈ (m * q ^ e).divisors, x = S * gsum q e := by
  intro e
  induction e with
  | zero => simp only [pow_zero, mul_one, gsum]; exact ⟨hR, hS⟩
  | succ e ih =>
    rw [divisors_step hm hq e]
    obtain ⟨h1, h2⟩ := rep_union hq.pos hR ih.1 (by rw [hS]; exact hqS)
      (divisors_step_disj hq hqm e)
    refine ⟨h1, ?_⟩
    rw [h2, hS, ih.2, ← gsum_succ']
    ring

theorem rep_one : RepF (1 : ℕ).divisors := by
  intro j hj
  simp only [Nat.divisors_one, sum_singleton] at hj ⊢
  interval_cases j
  · exact ⟨∅, empty_subset _, rfl⟩
  · exact ⟨{1}, subset_refl _, rfl⟩

theorem practical_of_rep {m : ℕ} (h : RepF m.divisors) : Practical m := by
  intro j hj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨∅, empty_subset _, by rw [sum_empty]; omega⟩
  · exact h j (hj.trans (single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors_self m hm.ne')))

/-! ### Powers of two times numbers with small prime factors -/

theorem gsum_two (e : ℕ) : gsum 2 e + 1 = 2 ^ (e + 1) := by
  induction e with
  | zero => simp [gsum]
  | succ e ih => simp only [gsum] at ih ⊢; rw [pow_succ 2 (e + 1)]; omega

theorem rep_two_pow (e : ℕ) :
    RepF (2 ^ e).divisors ∧ ∑ x ∈ (2 ^ e).divisors, x = gsum 2 e := by
  have := step (m := 1) (S := 1) (q := 2) one_pos rep_one (by simp) Nat.prime_two
    (by norm_num) (by norm_num) e
  simpa using this

theorem ext_rep : ∀ n, 0 < n → ∀ m, 0 < m → RepF m.divisors → Nat.Coprime m n →
    (∀ q, q.Prime → q ∣ n → q ≤ ∑ x ∈ m.divisors, x + 1) → RepF (m * n).divisors := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn m hm hR hcop hsmall
  by_cases h1 : n = 1
  · subst h1; simpa using hR
  have hq := Nat.minFac_prime h1
  set q := n.minFac
  have hqn : q ∣ n := Nat.minFac_dvd n
  set e := n.factorization q
  set n' := n / q ^ e
  have hsplit : q ^ e * n' = n := Nat.ordProj_mul_ordCompl_eq_self n q
  have hn'pos : 0 < n' := Nat.ordCompl_pos q hn.ne'
  have he : 1 ≤ e := (hq.factorization_pos_of_dvd hn.ne' hqn)
  have hqe : 2 ≤ q ^ e := (hq.two_le).trans (Nat.le_self_pow (by omega) q)
  have hlt : n' < n := by nlinarith
  have hn'dvd : n' ∣ n := ⟨q ^ e, by rw [← hsplit]; ring⟩
  have hR' := ih n' hlt hn'pos m hm hR (Nat.Coprime.coprime_dvd_right hn'dvd hcop)
    (fun q' hq' hd => hsmall q' hq' (hd.trans hn'dvd))
  have hqm : ¬q ∣ m := by
    intro h
    have := Nat.dvd_gcd h hqn
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have hqn' : ¬q ∣ n' := Nat.not_dvd_ordCompl hq hn.ne'
  have hmono : ∑ x ∈ m.divisors, x ≤ ∑ x ∈ (m * n').divisors, x :=
    sum_le_sum_of_subset (Nat.divisors_subset_of_dvd (by positivity) (dvd_mul_right m n'))
  have := (step (m := m * n') (S := ∑ x ∈ (m * n').divisors, x) (q := q) (by positivity) hR' rfl hq
    (fun h => (Nat.Prime.dvd_mul hq).1 h |>.elim hqm hqn')
    ((hsmall q hq hqn).trans (by omega)) e).1
  rwa [show m * n' * q ^ e = m * n by rw [← hsplit]; ring] at this

theorem pt (n t : ℕ) (hn : 0 < n) (h : ∀ q, q.Prime → q ∣ n → q ≤ 2 ^ (t + 1)) :
    Practical (2 ^ t * n) := by
  obtain ⟨v, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hopos : 0 < o := ho.pos
  obtain ⟨hR, hS⟩ := rep_two_pow (t + v)
  have := ext_rep o hopos (2 ^ (t + v)) (by positivity) hR
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 ho)) (by
      intro q hq hqo
      have h1 := h q hq (hqo.trans (dvd_mul_left o _))
      have h2 := gsum_two (t + v)
      have h3 : 2 ^ (t + 1) ≤ 2 ^ (t + v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hS]; omega)
  apply practical_of_rep
  rwa [show 2 ^ t * (2 ^ v * o) = 2 ^ (t + v) * o by rw [pow_add]; ring]

/-! ### Certificates for primes 47 < p ≤ 840 -/

def chk : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, _, [] => true
  | m, S, (q, e) :: r => primeTD q && m % q != 0 && decide (q ≤ S + 1) &&
      chk (m * q ^ e) (S * gsum q e) r

theorem chk_sound : ∀ (l : List (ℕ × ℕ)) (m S : ℕ), chk m S l = true → 0 < m →
    RepF m.divisors → ∑ x ∈ m.divisors, x = S → RepF (m * ArithFactor.val l).divisors
  | [], m, S, _, _, hR, _ => by simpa [ArithFactor.val] using hR
  | (q, e) :: r, m, S, h, hm, hR, hS => by
    simp only [chk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hq, hqm⟩, hqS⟩, hr⟩ := h
    have hqp := prime_of_primeTD q hq
    have hqm' : ¬q ∣ m := fun hd => hqm (Nat.mod_eq_zero_of_dvd hd)
    obtain ⟨h1, h2⟩ := step hm hR hS hqp hqm' hqS e
    have := chk_sound r (m * q ^ e) (S * gsum q e) hr (by have := hqp.pos; positivity) h1 h2
    rwa [show m * q ^ e * ArithFactor.val r = m * ArithFactor.val ((q, e) :: r) by
      simp only [ArithFactor.val]; ring] at this

def table : List (ℕ × ℕ × List (ℕ × ℕ)) := [
  (53, 24, [(2, 3), (3, 1), (53, 1)]),
  (59, 24, [(2, 3), (3, 1), (59, 1)]),
  (61, 24, [(2, 3), (3, 1), (61, 1)]),
  (67, 30, [(2, 1), (3, 1), (5, 1), (67, 1)]),
  (71, 30, [(2, 1), (3, 1), (5, 1), (71, 1)]),
  (73, 30, [(2, 1), (3, 1), (5, 1), (73, 1)]),
  (79, 36, [(2, 2), (3, 2), (79, 1)]),
  (83, 36, [(2, 2), (3, 2), (83, 1)]),
  (89, 36, [(2, 2), (3, 2), (89, 1)]),
  (97, 42, [(2, 1), (3, 1), (7, 1), (97, 1)]),
  (101, 48, [(2, 4), (3, 1), (101, 1)]),
  (103, 48, [(2, 4), (3, 1), (103, 1)]),
  (107, 48, [(2, 4), (3, 1), (107, 1)]),
  (109, 48, [(2, 4), (3, 1), (109, 1)]),
  (113, 48, [(2, 4), (3, 1), (113, 1)]),
  (127, 60, [(2, 2), (3, 1), (5, 1), (127, 1)]),
  (131, 60, [(2, 2), (3, 1), (5, 1), (131, 1)]),
  (137, 60, [(2, 2), (3, 1), (5, 1), (137, 1)]),
  (139, 60, [(2, 2), (3, 1), (5, 1), (139, 1)]),
  (149, 60, [(2, 2), (3, 1), (5, 1), (149, 1)]),
  (151, 60, [(2, 2), (3, 1), (5, 1), (151, 1)]),
  (157, 60, [(2, 2), (3, 1), (5, 1), (157, 1)]),
  (163, 60, [(2, 2), (3, 1), (5, 1), (163, 1)]),
  (167, 60, [(2, 2), (3, 1), (5, 1), (167, 1)]),
  (173, 72, [(2, 3), (3, 2), (173, 1)]),
  (179, 72, [(2, 3), (3, 2), (179, 1)]),
  (181, 72, [(2, 3), (3, 2), (181, 1)]),
  (191, 72, [(2, 3), (3, 2), (191, 1)]),
  (193, 72, [(2, 3), (3, 2), (193, 1)]),
  (197, 84, [(2, 2), (3, 1), (7, 1), (197, 1)]),
  (199, 84, [(2, 2), (3, 1), (7, 1), (199, 1)]),
  (211, 84, [(2, 2), (3, 1), (7, 1), (211, 1)]),
  (223, 84, [(2, 2), (3, 1), (7, 1), (223, 1)]),
  (227, 90, [(2, 1), (3, 2), (5, 1), (227, 1)]),
  (229, 90, [(2, 1), (3, 2), (5, 1), (229, 1)]),
  (233, 90, [(2, 1), (3, 2), (5, 1), (233, 1)]),
  (239, 96, [(2, 5), (3, 1), (239, 1)]),
  (241, 96, [(2, 5), (3, 1), (241, 1)]),
  (251, 96, [(2, 5), (3, 1), (251, 1)]),
  (257, 108, [(2, 2), (3, 3), (257, 1)]),
  (263, 108, [(2, 2), (3, 3), (263, 1)]),
  (269, 108, [(2, 2), (3, 3), (269, 1)]),
  (271, 108, [(2, 2), (3, 3), (271, 1)]),
  (277, 108, [(2, 2), (3, 3), (277, 1)]),
  (281, 108, [(2, 2), (3, 3), (281, 1)]),
  (283, 120, [(2, 3), (3, 1), (5, 1), (283, 1)]),
  (293, 120, [(2, 3), (3, 1), (5, 1), (293, 1)]),
  (307, 120, [(2, 3), (3, 1), (5, 1), (307, 1)]),
  (311, 120, [(2, 3), (3, 1), (5, 1), (311, 1)]),
  (313, 120, [(2, 3), (3, 1), (5, 1), (313, 1)]),
  (317, 120, [(2, 3), (3, 1), (5, 1), (317, 1)]),
  (331, 120, [(2, 3), (3, 1), (5, 1), (331, 1)]),
  (337, 120, [(2, 3), (3, 1), (5, 1), (337, 1)]),
  (347, 120, [(2, 3), (3, 1), (5, 1), (347, 1)]),
  (349, 120, [(2, 3), (3, 1), (5, 1), (349, 1)]),
  (353, 120, [(2, 3), (3, 1), (5, 1), (353, 1)]),
  (359, 120, [(2, 3), (3, 1), (5, 1), (359, 1)]),
  (367, 144, [(2, 4), (3, 2), (367, 1)]),
  (373, 144, [(2, 4), (3, 2), (373, 1)]),
  (379, 144, [(2, 4), (3, 2), (379, 1)]),
  (383, 144, [(2, 4), (3, 2), (383, 1)]),
  (389, 144, [(2, 4), (3, 2), (389, 1)]),
  (397, 144, [(2, 4), (3, 2), (397, 1)]),
  (401, 144, [(2, 4), (3, 2), (401, 1)]),
  (409, 168, [(2, 3), (3, 1), (7, 1), (409, 1)]),
  (419, 168, [(2, 3), (3, 1), (7, 1), (419, 1)]),
  (421, 168, [(2, 3), (3, 1), (7, 1), (421, 1)]),
  (431, 168, [(2, 3), (3, 1), (7, 1), (431, 1)]),
  (433, 168, [(2, 3), (3, 1), (7, 1), (433, 1)]),
  (439, 168, [(2, 3), (3, 1), (7, 1), (439, 1)]),
  (443, 168, [(2, 3), (3, 1), (7, 1), (443, 1)]),
  (449, 168, [(2, 3), (3, 1), (7, 1), (449, 1)]),
  (457, 168, [(2, 3), (3, 1), (7, 1), (457, 1)]),
  (461, 168, [(2, 3), (3, 1), (7, 1), (461, 1)]),
  (463, 168, [(2, 3), (3, 1), (7, 1), (463, 1)]),
  (467, 168, [(2, 3), (3, 1), (7, 1), (467, 1)]),
  (479, 168, [(2, 3), (3, 1), (7, 1), (479, 1)]),
  (487, 180, [(2, 2), (3, 2), (5, 1), (487, 1)]),
  (491, 180, [(2, 2), (3, 2), (5, 1), (491, 1)]),
  (499, 180, [(2, 2), (3, 2), (5, 1), (499, 1)]),
  (503, 180, [(2, 2), (3, 2), (5, 1), (503, 1)]),
  (509, 180, [(2, 2), (3, 2), (5, 1), (509, 1)]),
  (521, 180, [(2, 2), (3, 2), (5, 1), (521, 1)]),
  (523, 180, [(2, 2), (3, 2), (5, 1), (523, 1)]),
  (541, 180, [(2, 2), (3, 2), (5, 1), (541, 1)]),
  (547, 180, [(2, 2), (3, 2), (5, 1), (547, 1)]),
  (557, 210, [(2, 1), (3, 1), (5, 1), (7, 1), (557, 1)]),
  (563, 210, [(2, 1), (3, 1), (5, 1), (7, 1), (563, 1)]),
  (569, 210, [(2, 1), (3, 1), (5, 1), (7, 1), (569, 1)]),
  (571, 210, [(2, 1), (3, 1), (5, 1), (7, 1), (571, 1)]),
  (577, 210, [(2, 1), (3, 1), (5, 1), (7, 1), (577, 1)]),
  (587, 216, [(2, 3), (3, 3), (587, 1)]),
  (593, 216, [(2, 3), (3, 3), (593, 1)]),
  (599, 216, [(2, 3), (3, 3), (599, 1)]),
  (601, 216, [(2, 3), (3, 3), (601, 1)]),
  (607, 240, [(2, 4), (3, 1), (5, 1), (607, 1)]),
  (613, 240, [(2, 4), (3, 1), (5, 1), (613, 1)]),
  (617, 240, [(2, 4), (3, 1), (5, 1), (617, 1)]),
  (619, 240, [(2, 4), (3, 1), (5, 1), (619, 1)]),
  (631, 240, [(2, 4), (3, 1), (5, 1), (631, 1)]),
  (641, 240, [(2, 4), (3, 1), (5, 1), (641, 1)]),
  (643, 240, [(2, 4), (3, 1), (5, 1), (643, 1)]),
  (647, 240, [(2, 4), (3, 1), (5, 1), (647, 1)]),
  (653, 240, [(2, 4), (3, 1), (5, 1), (653, 1)]),
  (659, 240, [(2, 4), (3, 1), (5, 1), (659, 1)]),
  (661, 240, [(2, 4), (3, 1), (5, 1), (661, 1)]),
  (673, 240, [(2, 4), (3, 1), (5, 1), (673, 1)]),
  (677, 240, [(2, 4), (3, 1), (5, 1), (677, 1)]),
  (683, 240, [(2, 4), (3, 1), (5, 1), (683, 1)]),
  (691, 240, [(2, 4), (3, 1), (5, 1), (691, 1)]),
  (701, 240, [(2, 4), (3, 1), (5, 1), (701, 1)]),
  (709, 240, [(2, 4), (3, 1), (5, 1), (709, 1)]),
  (719, 240, [(2, 4), (3, 1), (5, 1), (719, 1)]),
  (727, 240, [(2, 4), (3, 1), (5, 1), (727, 1)]),
  (733, 240, [(2, 4), (3, 1), (5, 1), (733, 1)]),
  (739, 240, [(2, 4), (3, 1), (5, 1), (739, 1)]),
  (743, 240, [(2, 4), (3, 1), (5, 1), (743, 1)]),
  (751, 288, [(2, 5), (3, 2), (751, 1)]),
  (757, 288, [(2, 5), (3, 2), (757, 1)]),
  (761, 288, [(2, 5), (3, 2), (761, 1)]),
  (769, 288, [(2, 5), (3, 2), (769, 1)]),
  (773, 288, [(2, 5), (3, 2), (773, 1)]),
  (787, 288, [(2, 5), (3, 2), (787, 1)]),
  (797, 288, [(2, 5), (3, 2), (797, 1)]),
  (809, 288, [(2, 5), (3, 2), (809, 1)]),
  (811, 288, [(2, 5), (3, 2), (811, 1)]),
  (821, 300, [(2, 2), (3, 1), (5, 2), (821, 1)]),
  (823, 300, [(2, 2), (3, 1), (5, 2), (823, 1)]),
  (827, 300, [(2, 2), (3, 1), (5, 2), (827, 1)]),
  (829, 300, [(2, 2), (3, 1), (5, 2), (829, 1)]),
  (839, 300, [(2, 2), (3, 1), (5, 2), (839, 1)])]

def tableOK : Bool :=
  table.all fun x => ArithFactor.val x.2.2 == x.2.1 * x.1 && decide (0 < x.2.1) && decide (2 * x.2.1 < x.1) &&
    chk 1 1 x.2.2

def coverOK : Bool :=
  (List.range 841).all fun n => decide (n ≤ 47) || table.any (fun x => x.1 == n) ||
    (List.range 30).any fun d => decide (2 ≤ d) && decide (d < n) && n % d == 0

theorem tableOK_true : tableOK = true := by decide +kernel
theorem coverOK_true : coverOK = true := by decide +kernel

theorem small_prime (p : ℕ) (hp : p.Prime) (h47 : 47 < p) (h840 : p ≤ 840) :
    ∃ k, 0 < k ∧ 2 * k < p ∧ Practical (k * p) := by
  have hc := coverOK_true
  simp only [coverOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at hc
  rcases hc p (by omega) with (h | ⟨x, hx, hxp⟩) | ⟨d, -, ⟨⟨hd2, hdp⟩, hdiv⟩⟩
  · omega
  · have ht := tableOK_true
    simp only [tableOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨hval, hk⟩, h2k⟩, hchk⟩ := ht x hx
    refine ⟨x.2.1, hk, hxp ▸ h2k, ?_⟩
    have := chk_sound x.2.2 1 1 hchk one_pos rep_one (by simp)
    rw [one_mul, hval, hxp] at this
    exact practical_of_rep this
  · exfalso
    have := (Nat.Prime.eq_one_or_self_of_dvd hp d (Nat.dvd_of_mod_eq_zero hdiv))
    omega

/-! ### Primes p > 840: the family 2^(a+2)·105, 2^(a+2)·165 -/

def fam (i : ℕ) : ℕ := 2 ^ (i / 2 + 2) * (if i % 2 = 0 then 105 else 165)
def famS (i : ℕ) : ℕ := (2 ^ (i / 2 + 3) - 1) * (if i % 2 = 0 then 192 else 288)

theorem step1 {m S q : ℕ} (hm : 0 < m) (hR : RepF m.divisors) (hS : ∑ x ∈ m.divisors, x = S)
    (hq : q.Prime) (hqm : ¬q ∣ m) (hqS : q ≤ S + 1) :
    RepF (m * q).divisors ∧ ∑ x ∈ (m * q).divisors, x = S * (1 + q) := by
  have := step hm hR hS hq hqm hqS 1
  simpa [gsum] using this

theorem fam_practical (i p : ℕ) (hp : p.Prime) (h11 : 11 < p) (hpS : p ≤ famS i + 1) :
    Practical (fam i * p) := by
  set a := i / 2 + 2
  obtain ⟨R0, S0⟩ := rep_two_pow a
  have hg := gsum_two a
  have ha : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hg7 : 7 ≤ gsum 2 a := by rw [pow_succ] at hg; omega
  have hG : 2 ^ (i / 2 + 3) - 1 = gsum 2 a := by
    rw [show i / 2 + 3 = a + 1 by omega]; omega
  have hpow : ∀ r, r.Prime → r ≠ 2 → ¬r ∣ 2 ^ a := fun r hr h2 hd =>
    h2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd))
  have hsmall : ∀ r c, r.Prime → c.Prime → r ≠ 2 → c < r → ¬r ∣ 2 ^ a * c := by
    intro r c hr hc h2 hcr hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
    · exact hpow r hr h2 h
    · have := (Nat.prime_dvd_prime_iff_eq hr hc).1 h; omega
  obtain ⟨R3, S3⟩ := step1 (by positivity) R0 S0 Nat.prime_three
    (hpow 3 Nat.prime_three (by norm_num)) (by omega)
  have h5 : ¬5 ∣ 2 ^ a * 3 := hsmall 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨R5, S5⟩ := step1 (by positivity) R3 S3 (by norm_num) h5 (by omega)
  have hthree : ∀ r, r.Prime → 5 < r → ¬r ∣ 2 ^ a * 3 * 5 := by
    intro r hr h5r hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
    · exact hsmall r 3 hr Nat.prime_three (by omega) (by omega) h
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h; omega
  have hfour : ∀ c, c.Prime → c < p → ¬c ∣ 2 ^ a * 3 * 5 → ¬p ∣ 2 ^ a * 3 * 5 * c := by
    intro c hc hcp _ hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact hthree p hp (by omega) h
    · have := (Nat.prime_dvd_prime_iff_eq hp hc).1 h; omega
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have hF : famS i = gsum 2 a * 192 := by simp only [famS, hi, ↓reduceIte, hG]
    have h7 := hthree 7 (by norm_num) (by norm_num)
    obtain ⟨R7, S7⟩ := step1 (by positivity) R5 S5 (by norm_num) h7 (by omega)
    obtain ⟨Rp, -⟩ := step1 (by positivity) R7 S7 hp (hfour 7 (by norm_num) (by omega) h7)
      (by omega)
    apply practical_of_rep
    rwa [show fam i * p = 2 ^ a * 3 * 5 * 7 * p by simp only [fam, hi, ↓reduceIte]; ring]
  · have hF : famS i = gsum 2 a * 288 := by
      simp only [famS, hi, one_ne_zero, ↓reduceIte, hG]
    have h11' := hthree 11 (by norm_num) (by norm_num)
    obtain ⟨R11, S11⟩ := step1 (by positivity) R5 S5 (by norm_num) h11' (by omega)
    obtain ⟨Rp, -⟩ := step1 (by positivity) R11 S11 hp (hfour 11 (by norm_num) (by omega) h11')
      (by omega)
    apply practical_of_rep
    rwa [show fam i * p = 2 ^ a * 3 * 5 * 11 * p by
      simp only [fam, hi, one_ne_zero, ↓reduceIte]; ring]

theorem fam_bound (i : ℕ) (hi : 1 ≤ i) : 2 * fam i ≤ famS (i - 1) := by
  obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' i
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    simp only [fam, famS]
    rw [show 2 * (c + 1) / 2 + 2 = c + 3 by omega, show 2 * (c + 1) % 2 = 0 by omega,
      show (2 * (c + 1) - 1) / 2 + 3 = c + 3 by omega, show (2 * (c + 1) - 1) % 2 = 1 by omega]
    simp only [↓reduceIte, one_ne_zero]
    have : 8 ≤ 2 ^ (c + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (c + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · simp only [fam, famS]
    rw [show (2 * b + 1) / 2 + 2 = b + 2 by omega, show (2 * b + 1) % 2 = 1 by omega,
      show (2 * b + 1 - 1) / 2 + 3 = b + 3 by omega, show (2 * b + 1 - 1) % 2 = 0 by omega]
    simp only [↓reduceIte, one_ne_zero]
    have h4 : 4 ≤ 2 ^ (b + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (b + 3) = 2 * 2 ^ (b + 2) := by rw [pow_succ]; ring
    omega

theorem big_prime (p : ℕ) (hp : p.Prime) (h840 : 840 < p) :
    ∃ k, 0 < k ∧ 2 * k < p ∧ Practical (k * p) := by
  have hex : ∃ i, p ≤ famS i + 1 := by
    refine ⟨p, ?_⟩
    have h1 : p / 2 + 3 < 2 ^ (p / 2 + 3) := Nat.lt_two_pow_self
    have h2 : 192 ≤ (if p % 2 = 0 then 192 else 288) := by split_ifs <;> norm_num
    have h3 : (2 ^ (p / 2 + 3) - 1) * 192 ≤ famS p := Nat.mul_le_mul_left _ h2
    omega
  classical
  set i₁ := Nat.find hex with hi₁
  have hspec : p ≤ famS i₁ + 1 := Nat.find_spec hex
  refine ⟨fam i₁, by simp only [fam]; split_ifs <;> positivity, ?_,
    fam_practical i₁ p hp (by omega) hspec⟩
  rcases Nat.eq_zero_or_pos i₁ with h0 | hpos
  · rw [h0]; simp only [fam]; norm_num; omega
  · have hmin := Nat.find_min hex (show i₁ - 1 < Nat.find hex by omega)
    have := fam_bound i₁ hpos
    omega

/-! ### Main theorem -/

theorem A210445_main :
    (∀ n, 1 < n → ∃ k, 0 < k ∧ k < n ∧ Practical (k * n)) ∧
    (∀ n, 47 < n → ∃ k, 0 < k ∧ 2 * k < n ∧ Practical (k * n)) := by
  constructor
  · intro n hn
    set t := Nat.log 2 (n - 1)
    have h1 : 2 ^ t ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
    have h2 : n - 1 < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    refine ⟨2 ^ t, by positivity, by omega, ?_⟩
    exact pt n t (by omega) fun q _ hq => (Nat.le_of_dvd (by omega) hq).trans (by omega)
  · intro n hn
    by_cases hp : n.Prime
    · rcases Nat.lt_or_ge 840 n with h | h
      · exact big_prime n hp h
      · exact small_prime n hp hn h
    · set t := Nat.log 2 ((n - 1) / 2)
      have h1 : 2 ^ t ≤ (n - 1) / 2 := Nat.pow_log_le_self 2 (by omega)
      have h2 : (n - 1) / 2 < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      refine ⟨2 ^ t, by positivity, by omega, ?_⟩
      apply pt n t (by omega)
      intro q hq hqn
      obtain ⟨c, rfl⟩ := hqn
      have hc : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with hc | hc
        · interval_cases c
          · omega
          · simp at hp; exact absurd hq hp
        · exact hc
      have : q * 2 ≤ q * c := Nat.mul_le_mul_left q hc
      omega
