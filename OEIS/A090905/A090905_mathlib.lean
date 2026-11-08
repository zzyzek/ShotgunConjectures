/-
OEIS A090904-A090907 (Murthy's triangle: rows of consecutive integers (1), (2), (3,4), (5..8), ...,
each row the shortest block after the previous one whose product is a multiple of the previous
row's product). Conjecture: for n > 4 the last entry of row n is 2p, p the largest prime of row n-1.

Proved here, unconditionally. The proof is written against the hypothesis `NaguraNat` (for every
integer x >= 25 there is a prime p with x < p < 6x/5; J. Nagura, Proc. Japan Acad. 28 (1952)
177-181), and `naguraNat_holds` discharges it with the library theorem
`OpenProblemsLib.Nagura.nagura_nat_lt` (lib/OpenProblemsLib/Nagura.lean, proved from Chebyshev's
bounds plus a Pratt-certified prime chain):

  `A090905_main (n) (hn : 5 ≤ n)`: there is a prime p with e(n-2) < p ≤ e(n-1),
  every prime of (e(n-2), e(n-1)] is at most p, and e n = 2 p.
  `A090905_of_nagura (hN : NaguraNat) (n) (hn : 5 ≤ n)`: the same statement from the hypothesis.

Definitions: `P a b` = product of (a, b]; `st 0 = (1, 2)`, `st (k+1) = ((st k).2, least E > (st k).2
with P (st k).1 (st k).2 ∣ P (st k).2 E)` (existence `exists_next`); `e n = (st (n-1)).1` is the
last entry of row n.

Route: `core_dvd` ((2q)!^2 ∣ (2p)!(2r)! for consecutive Bertrand primes r < q < p with
5q < 3p and q > 72), via Legendre's formula (`Nat.factorization_factorial`) and the level
analysis `N_nonneg`, `N_ge1`, `N_ge_neg1`, `sum_levels` (the only negative level is one prime power
in (p, 2q), compensated at the first level); `step` (then the next row is (2q, 2p]); rows up to
(86, 166] by kernel computation (`st1`..`st7`); `nagura_p`, `inv_step`, `inv_all` (induction).

Checked: everything above, including Nagura's theorem (library module `OpenProblemsLib.Nagura`).
-/
import Mathlib
import OpenProblemsLib.Nagura

open Finset Nat

/-! ### Floor-sum lemmas: `N(x) = A/x + B/x - 2 (C/x)` -/

lemma fl_ge_neg1 {A B C x : ℕ} (hx : 0 < x) (h : 2 * C ≤ A + B) :
    2 * (C / x) ≤ A / x + B / x + 1 := by
  have hA := Nat.div_add_mod A x; have hA' := Nat.mod_lt A hx
  have hB := Nat.div_add_mod B x; have hB' := Nat.mod_lt B hx
  have hC := Nat.div_add_mod C x
  by_contra hcon
  push Not at hcon
  have : x * (A / x + B / x + 2) ≤ x * (2 * (C / x)) := Nat.mul_le_mul_left x hcon
  generalize A / x = a at *; generalize B / x = b at *; generalize C / x = c at *
  have := Nat.zero_le (C % x)
  ring_nf at this hA hB hC
  linarith

lemma fl_ge0 {A B C x : ℕ} (hx : 0 < x) (h : x + 2 * C ≤ A + B) :
    2 * (C / x) ≤ A / x + B / x := by
  have hA := Nat.div_add_mod A x; have hA' := Nat.mod_lt A hx
  have hB := Nat.div_add_mod B x; have hB' := Nat.mod_lt B hx
  have hC := Nat.div_add_mod C x
  by_contra hcon
  push Not at hcon
  have : x * (A / x + B / x + 1) ≤ x * (2 * (C / x)) := Nat.mul_le_mul_left x hcon
  generalize A / x = a at *; generalize B / x = b at *; generalize C / x = c at *
  have := Nat.zero_le (C % x)
  ring_nf at this hA hB hC
  linarith

lemma fl_ge1 {A B C x : ℕ} (hx : 0 < x) (h : 2 * x + 2 * C ≤ A + B) :
    2 * (C / x) + 1 ≤ A / x + B / x := by
  have hA := Nat.div_add_mod A x; have hA' := Nat.mod_lt A hx
  have hB := Nat.div_add_mod B x; have hB' := Nat.mod_lt B hx
  have hC := Nat.div_add_mod C x
  by_contra hcon
  push Not at hcon
  have : x * (A / x + B / x) ≤ x * (2 * (C / x)) := Nat.mul_le_mul_left x (by omega)
  generalize A / x = a at *; generalize B / x = b at *; generalize C / x = c at *
  have := Nat.zero_le (C % x)
  ring_nf at this hA hB hC
  linarith

/-- Hypotheses on three consecutive Bertrand-chain primes r < q < p. -/
structure Chain (r q p : ℕ) : Prop where
  hrq : r < q
  hq2r : q < 2 * r
  hpq : 5 * q < 3 * p
  hp2q : p < 2 * q
  gap : ∀ m, p < m → m < 2 * q → ¬ m.Prime

lemma divk {m x k : ℕ} (hx : 0 < x) (h : k * x ≤ m) : k ≤ m / x := (Nat.le_div_iff_mul_le hx).mpr h

lemma diveq {m x k : ℕ} (h1 : k * x ≤ m) (h2 : m < (k + 1) * x) : m / x = k :=
  Nat.div_eq_of_lt_le h1 h2

/-- N(x) ≥ 0 unless p < x ≤ 2q. -/
lemma N_nonneg {r q p x : ℕ} (c : Chain r q p) (hx : 0 < x) (hgood : ¬ (p < x ∧ x ≤ 2 * q)) :
    2 * (2 * q / x) ≤ 2 * p / x + 2 * r / x := by
  have hrq := c.hrq; have hq2r := c.hq2r; have hpq := c.hpq; have hp2q := c.hp2q
  by_cases h3 : 3 * x ≤ q
  · exact fl_ge0 hx (by omega)
  by_cases hA : 2 * q < x
  · simp [Nat.div_eq_of_lt hA]
  by_cases hB : q < x
  · have hxp : x ≤ p := by
      by_contra hh; exact hgood ⟨by omega, by omega⟩
    have e1 : 1 * x ≤ 2 * q := by omega
    have e2 : 2 * q < (1 + 1) * x := by omega
    rw [diveq e1 e2]
    have ha := divk (m := 2 * p) (k := 2) hx (by omega)
    generalize 2 * p / x = a at *; generalize 2 * r / x = b at *; omega
  by_cases hC : 2 * q < 3 * x
  · have e1 : 2 * x ≤ 2 * q := by omega
    have e2 : 2 * q < (2 + 1) * x := by omega
    rw [diveq e1 e2]
    have ha := divk (m := 2 * p) (k := 3) hx (by omega)
    have hb := divk (m := 2 * r) (k := 1) hx (by omega)
    generalize 2 * p / x = a at *; generalize 2 * r / x = b at *; omega
  by_cases hD : q < 2 * x
  · have e1 : 3 * x ≤ 2 * q := by omega
    have e2 : 2 * q < (3 + 1) * x := by omega
    rw [diveq e1 e2]
    have ha := divk (m := 2 * p) (k := 5) hx (by omega)
    have hb := divk (m := 2 * r) (k := 1) hx (by omega)
    generalize 2 * p / x = a at *; generalize 2 * r / x = b at *; omega
  by_cases hE : 2 * q < 5 * x
  · have e1 : 4 * x ≤ 2 * q := by omega
    have e2 : 2 * q < (4 + 1) * x := by omega
    rw [diveq e1 e2]
    have ha := divk (m := 2 * p) (k := 6) hx (by omega)
    have hb := divk (m := 2 * r) (k := 2) hx (by omega)
    generalize 2 * p / x = a at *; generalize 2 * r / x = b at *; omega
  · have e1 : 5 * x ≤ 2 * q := by omega
    have e2 : 2 * q < (5 + 1) * x := by omega
    rw [diveq e1 e2]
    have ha := divk (m := 2 * p) (k := 8) hx (by omega)
    have hb := divk (m := 2 * r) (k := 2) hx (by omega)
    generalize 2 * p / x = a at *; generalize 2 * r / x = b at *; omega

lemma N_ge1 {r q p x : ℕ} (c : Chain r q p) (hx : 0 < x) (h6 : 6 * x ≤ q) :
    2 * (2 * q / x) + 1 ≤ 2 * p / x + 2 * r / x := by
  have hq2r := c.hq2r; have hpq := c.hpq
  exact fl_ge1 hx (by omega)

lemma N_ge_neg1 {r q p x : ℕ} (c : Chain r q p) (hx : 0 < x) :
    2 * (2 * q / x) ≤ 2 * p / x + 2 * r / x + 1 := by
  have hq2r := c.hq2r; have hpq := c.hpq
  exact fl_ge_neg1 hx (by omega)
lemma sum_levels {r q p ℓ : ℕ} (c : Chain r q p) (hq72 : 72 < q) (hqp : q.Prime) (hℓ : ℓ.Prime)
    (Bd : ℕ) (hBd : 2 ≤ Bd) :
    ∑ i ∈ Ico 1 Bd, 2 * (2 * q / ℓ ^ i) ≤ ∑ i ∈ Ico 1 Bd, (2 * p / ℓ ^ i + 2 * r / ℓ ^ i) := by
  have hl2 := hℓ.two_le
  have hpos : ∀ i, 0 < ℓ ^ i := fun i => Nat.pow_pos (by omega)
  have hpq := c.hpq; have hp2q := c.hp2q
  by_cases hbad : ∃ j ∈ Ico 1 Bd, p < ℓ ^ j ∧ ℓ ^ j ≤ 2 * q
  · obtain ⟨j, hj, hj1, hj2⟩ := hbad
    have hj1' : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hne : ℓ ^ j ≠ 2 * q := by
      intro heq
      have h2 : 2 ∣ ℓ ^ j := ⟨q, heq⟩
      have hl : ℓ = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).mp
        (Nat.prime_two.dvd_of_dvd_pow h2)).symm
      subst hl
      have : 2 ^ j = 2 * 2 ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hq2 : q = 2 ^ (j - 1) := by omega
      have : q ∣ 2 := hqp.dvd_of_dvd_pow (show q ∣ 2 ^ (j - 1) from hq2 ▸ dvd_refl q)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hlt : ℓ ^ j < 2 * q := lt_of_le_of_ne hj2 hne
    have hj2' : 2 ≤ j := by
      by_contra hcon
      have : j = 1 := by omega
      subst this
      exact c.gap ℓ (by simpa using hj1) (by simpa using hlt) hℓ
    have hsq : ℓ ^ 2 ≤ ℓ ^ j := Nat.pow_le_pow_right (by omega) hj2'
    have h6 : 6 * ℓ ≤ q := by
      by_contra hcon
      push Not at hcon
      have : ℓ * ℓ < 2 * q := by nlinarith
      nlinarith
    have h1mem : 1 ∈ (Ico 1 Bd).erase j := Finset.mem_erase.mpr ⟨by omega, by simp; omega⟩
    have hgood : ∀ i ∈ ((Ico 1 Bd).erase j).erase 1,
        2 * (2 * q / ℓ ^ i) ≤ 2 * p / ℓ ^ i + 2 * r / ℓ ^ i := by
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      apply N_nonneg c (hpos i)
      rintro ⟨hi1, hi2⟩
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · have : ℓ ^ (i + 1) ≤ ℓ ^ j := Nat.pow_le_pow_right (by omega) h
        rw [pow_succ] at this
        nlinarith
      · have : ℓ ^ (j + 1) ≤ ℓ ^ i := Nat.pow_le_pow_right (by omega) h
        rw [pow_succ] at this
        nlinarith
    have hg1 := N_ge1 c (hpos 1) (by simpa using h6)
    have hgj := N_ge_neg1 c (hpos j) (x := ℓ ^ j)
    rw [← Finset.add_sum_erase _ _ hj, ← Finset.add_sum_erase _ _ hj,
      ← Finset.add_sum_erase _ _ h1mem, ← Finset.add_sum_erase _ _ h1mem]
    have := Finset.sum_le_sum hgood
    omega
  · push Not at hbad
    apply Finset.sum_le_sum
    intro i hi
    exact N_nonneg c (hpos i) (fun ⟨h1, h2⟩ => absurd h2 (Nat.not_le.mpr (hbad i hi h1)))

theorem core_dvd {r q p : ℕ} (c : Chain r q p) (hq72 : 72 < q) (hqp : q.Prime) :
    (2 * q)! ^ 2 ∣ (2 * p)! * (2 * r)! := by
  have hpq := c.hpq; have hrq := c.hrq
  rw [← Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)]
  intro ℓ hℓ
  have hB : ∀ n, n ≤ 2 * p → Nat.log ℓ n < 2 * p + 1 := fun n hn =>
    Nat.lt_succ_of_le ((Nat.log_le_self ℓ n).trans hn)
  rw [Nat.factorization_pow, Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply]
  rw [Nat.factorization_factorial hℓ (hB (2 * q) (by omega)),
    Nat.factorization_factorial hℓ (hB (2 * p) le_rfl),
    Nat.factorization_factorial hℓ (hB (2 * r) (by omega)),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact sum_levels c hq72 hqp hℓ (2 * p + 1) (by omega)

/-! ### The triangle -/

/-- Product of the integers in (a, b]. -/
def P (a b : ℕ) : ℕ := ∏ j ∈ Ioc a b, j

lemma P_mul_fact {a b : ℕ} (h : a ≤ b) : P a b * a ! = b ! := by
  induction b, h using Nat.le_induction with
  | base => simp [P]
  | succ b hab ih =>
    rw [P, Finset.prod_Ioc_succ_top (by omega), Nat.factorial_succ, ← ih, P]
    ring

lemma P_pos (a b : ℕ) : 0 < P a b :=
  Finset.prod_pos (fun j hj => by simp at hj; omega)

lemma exists_next (x a : ℕ) : ∃ E, a < E ∧ P x a ∣ P a E := by
  set M := P x a
  have hM : 0 < M := P_pos x a
  refine ⟨a + M, by omega, ?_⟩
  have h1 : P a (a + M) * a ! = (a + M) ! := P_mul_fact (by omega)
  have h2 : a ! * (a + M).descFactorial M = (a + M) ! := by
    have := Nat.factorial_mul_descFactorial (show M ≤ a + M by omega)
    simpa using this
  have h3 : P a (a + M) = (a + M).descFactorial M := by
    have : P a (a + M) * a ! = (a + M).descFactorial M * a ! := by rw [h1, ← h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos a) this
  rw [h3]
  exact (Nat.dvd_factorial hM le_rfl).trans (Nat.factorial_dvd_descFactorial _ _)

/-- `st k = (e (k+1), e (k+2))`: ends of rows k+1 and k+2 (rows (1), (2), (3,4), (5..8), ...). -/
noncomputable def st : ℕ → ℕ × ℕ
  | 0 => (1, 2)
  | k + 1 => ((st k).2, Nat.find (exists_next (st k).1 (st k).2))

/-- `e n`: last entry of row n (n ≥ 1); row n is (e (n-1), e n]. -/
noncomputable def e (n : ℕ) : ℕ := (st (n - 1)).1

lemma st_succ (k : ℕ) : st (k + 1) = ((st k).2, Nat.find (exists_next (st k).1 (st k).2)) := rfl

lemma find_eq {x a m : ℕ} (hm : a < m ∧ P x a ∣ P a m)
    (hmin : ∀ E, a < E → E < m → ¬ P x a ∣ P a E) :
    Nat.find (exists_next x a) = m := by
  rw [Nat.find_eq_iff]
  exact ⟨hm, fun E hE ⟨h1, h2⟩ => hmin E h1 hE h2⟩

lemma st1 : st 1 = (2, 4) := by
  rw [st_succ]; simp only [st]
  rw [find_eq (m := 4) (by decide) (by intro E h1 h2; interval_cases E; decide)]

lemma st2 : st 2 = (4, 8) := by
  rw [st_succ, st1]
  rw [find_eq (m := 8) (by decide) (by intro E h1 h2; interval_cases E <;> decide)]

lemma st3 : st 3 = (8, 14) := by
  rw [st_succ, st2]
  rw [find_eq (m := 14) (by decide) (by intro E h1 h2; interval_cases E <;> decide)]

lemma st4 : st 4 = (14, 26) := by
  rw [st_succ, st3]
  rw [find_eq (m := 26) (by decide) (by intro E h1 h2; interval_cases E <;> decide)]

lemma step {k r q p : ℕ} (hst : st k = (2 * r, 2 * q)) (hp : p.Prime) (h2r : 2 * r < p)
    (hpq : q < p) (hp2q : p < 2 * q) (hrq : r ≤ q)
    (hdiv : (2 * q)! ^ 2 ∣ (2 * p)! * (2 * r)!) : st (k + 1) = (2 * q, 2 * p) := by
  rw [st_succ, hst]
  simp only [Prod.mk.injEq, true_and]
  have hA := P_mul_fact (show 2 * r ≤ 2 * q by omega)
  have hB := P_mul_fact (show 2 * q ≤ 2 * p by omega)
  apply find_eq
  · refine ⟨by omega, ?_⟩
    have hpos : 0 < (2 * q)! * (2 * r)! := by positivity
    apply Nat.dvd_of_mul_dvd_mul_right hpos
    have : P (2 * r) (2 * q) * ((2 * q)! * (2 * r)!) = (2 * q)! ^ 2 := by rw [← hA]; ring
    have h2 : P (2 * q) (2 * p) * ((2 * q)! * (2 * r)!) = (2 * p)! * (2 * r)! := by rw [← hB]; ring
    rw [this, h2]; exact hdiv
  · intro E hE1 hE2 hdvd
    have hpmem : p ∣ P (2 * r) (2 * q) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_Ioc.mpr ⟨h2r, by omega⟩)
    obtain ⟨j, hj, hpj⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp (hpmem.trans hdvd)
    rw [Finset.mem_Ioc] at hj
    obtain ⟨t, rfl⟩ := hpj
    rcases t with _ | _ | t
    · omega
    · omega
    · nlinarith

lemma row_largest {q p : ℕ} (hq : 2 ≤ q) (gap : ∀ m, p < m → m < 2 * q → ¬ m.Prime) :
    ∀ p', p'.Prime → p' ≤ 2 * q → p' ≤ p := by
  intro p' hp' hle
  by_contra hcon
  push Not at hcon
  rcases Nat.lt_or_ge p' (2 * q) with h | h
  · exact gap p' hcon h hp'
  · have : p' = 2 * q := by omega
    subst this
    have := hp'.eq_one_or_self_of_dvd 2 (dvd_mul_right 2 q)
    omega

/-- Nagura (1952) in the form used: for every integer x ≥ 25 there is a prime p with x < p < 6x/5. -/
def NaguraNat : Prop := ∀ x : ℕ, 25 ≤ x → ∃ p, p.Prime ∧ x < p ∧ 5 * p < 6 * x

lemma nagura_p (hN : NaguraNat) {q : ℕ} (hq : 15 ≤ q) :
    ∃ p, p.Prime ∧ p < 2 * q ∧ 5 * q < 3 * p ∧ ∀ m, p < m → m < 2 * q → ¬ m.Prime := by
  obtain ⟨p', hp', h1, h2⟩ := hN ((5 * q + 2) / 3) (by omega)
  have hp'2q : p' < 2 * q := by
    rcases Nat.lt_or_ge p' (2 * q) with h | h
    · exact h
    · have : p' = 2 * q := by omega
      subst this
      have := hp'.eq_one_or_self_of_dvd 2 (dvd_mul_right 2 q)
      omega
  have hle : p' ≤ Nat.findGreatest Nat.Prime (2 * q - 1) := Nat.le_findGreatest (by omega) hp'
  refine ⟨Nat.findGreatest Nat.Prime (2 * q - 1), ?_, ?_, by omega, ?_⟩
  · exact Nat.findGreatest_spec (P := Nat.Prime) (m := p') (by omega) hp'
  · have := Nat.findGreatest_le (P := Nat.Prime) (2 * q - 1); omega
  · intro m hm1 hm2
    exact Nat.findGreatest_is_greatest hm1 (by omega)

/-- Invariant from row 8 on: st k = (2r, 2q), consecutive Bertrand primes with q > 72. -/
def ChainInv (k : ℕ) : Prop :=
  ∃ r q, st k = (2 * r, 2 * q) ∧ r.Prime ∧ q.Prime ∧ r < q ∧ q < 2 * r ∧ 5 * r < 3 * q ∧ 72 < q

lemma st5 : st 5 = (26, 46) := by
  have := step (k := 4) (r := 7) (q := 13) (p := 23) (by rw [st4]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)
  simpa using this

set_option maxRecDepth 100000 in
lemma st6 : st 6 = (46, 86) := by
  have := step (k := 5) (r := 13) (q := 23) (p := 43) (by rw [st5]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)
  simpa using this

set_option maxRecDepth 100000 in
lemma st7 : st 7 = (86, 166) := by
  have := step (k := 6) (r := 23) (q := 43) (p := 83) (by rw [st6]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)
  simpa using this

lemma inv7 : ChainInv 7 := ⟨43, 83, by rw [st7], by norm_num, by norm_num, by norm_num, by norm_num,
  by norm_num, by norm_num⟩

/-- One step of the chain from row 8 on, with the largest prime of the row. -/
lemma inv_step (hN : NaguraNat) {k : ℕ} (hk : ChainInv k) :
    ∃ r q p, st k = (2 * r, 2 * q) ∧ st (k + 1) = (2 * q, 2 * p) ∧ p.Prime ∧ 2 * r < p ∧
      p ≤ 2 * q ∧ (∀ p', p'.Prime → p' ≤ 2 * q → p' ≤ p) ∧ ChainInv (k + 1) := by
  obtain ⟨r, q, hst, hr, hq, hrq, hq2r, h53, h72⟩ := hk
  obtain ⟨p, hp, hp2q, hpq, gap⟩ := nagura_p hN (q := q) (by omega)
  have c : Chain r q p := ⟨hrq, hq2r, hpq, hp2q, gap⟩
  have hdiv := core_dvd c h72 hq
  have h2r : 2 * r < p := by omega
  have hst' := step hst hp h2r (by omega) hp2q hrq.le hdiv
  exact ⟨r, q, p, hst, hst', hp, h2r, by omega, row_largest (by omega) gap,
    ⟨q, p, hst', hq, hp, by omega, hp2q, hpq, by omega⟩⟩

lemma inv_all (hN : NaguraNat) : ∀ k, 7 ≤ k → ChainInv k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact inv7
  | succ k _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := inv_step hN ih
    exact h

lemma st_fst (k : ℕ) : (st (k + 1)).1 = (st k).2 := rfl

lemma concl_of {n r q p : ℕ} (h1 : e (n - 2) = 2 * r) (h2 : e (n - 1) = 2 * q) (h3 : e n = 2 * p)
    (hp : p.Prime) (h2r : 2 * r < p) (hp2q : p ≤ 2 * q)
    (hl : ∀ p', p'.Prime → p' ≤ 2 * q → p' ≤ p) :
    ∃ p, p.Prime ∧ e (n - 2) < p ∧ p ≤ e (n - 1) ∧
      (∀ p', p'.Prime → e (n - 2) < p' → p' ≤ e (n - 1) → p' ≤ p) ∧ e n = 2 * p :=
  ⟨p, hp, by omega, by omega, fun p' hp' _ h => hl p' hp' (by omega), h3⟩

/-- The A090905 conjecture from the hypothesis `NaguraNat`: for n ≥ 5 the last entry of row n is
2p, where p is the largest prime of row n - 1 = (e (n-2), e (n-1)]. -/
theorem A090905_of_nagura (hN : NaguraNat) (n : ℕ) (hn : 5 ≤ n) :
    ∃ p, p.Prime ∧ e (n - 2) < p ∧ p ≤ e (n - 1) ∧
      (∀ p', p'.Prime → e (n - 2) < p' → p' ≤ e (n - 1) → p' ≤ p) ∧ e n = 2 * p := by
  have e3 : e 3 = 4 := by simp [e, st2]
  have e4 : e 4 = 8 := by simp [e, st3]
  have e5 : e 5 = 14 := by simp [e, st4]
  have e6 : e 6 = 26 := by simp [e, st5]
  have e7 : e 7 = 46 := by simp [e, st6]
  have e8 : e 8 = 86 := by simp [e, st7]
  have e9 : e 9 = 166 := by simp only [e, show 9 - 1 = 7 + 1 from rfl, st_fst, st7]
  rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ 10 ≤ n by omega) with
    rfl | rfl | rfl | rfl | rfl | h10
  · exact concl_of (r := 2) (q := 4) (p := 7) e3 e4 e5 (by norm_num) (by norm_num) (by norm_num)
      (fun p' hp' h => by interval_cases p' <;> first | omega | (exfalso; norm_num at hp'))
  · exact concl_of (r := 4) (q := 7) (p := 13) e4 e5 e6 (by norm_num) (by norm_num) (by norm_num)
      (fun p' hp' h => by interval_cases p' <;> first | omega | (exfalso; norm_num at hp'))
  · exact concl_of (r := 7) (q := 13) (p := 23) e5 e6 e7 (by norm_num) (by norm_num) (by norm_num)
      (fun p' hp' h => by interval_cases p' <;> first | omega | (exfalso; norm_num at hp'))
  · exact concl_of (r := 13) (q := 23) (p := 43) e6 e7 e8 (by norm_num) (by norm_num) (by norm_num)
      (fun p' hp' h => by interval_cases p' <;> first | omega | (exfalso; norm_num at hp'))
  · exact concl_of (r := 23) (q := 43) (p := 83) e7 e8 e9 (by norm_num) (by norm_num) (by norm_num)
      (fun p' hp' h => by interval_cases p' <;> first | omega | (exfalso; norm_num at hp'))
  · obtain ⟨r, q, p, hst, hst', hp, h2r, hp2q, hl, -⟩ := inv_step hN (inv_all hN (n - 3) (by omega))
    have h1 : e (n - 2) = 2 * r := by
      simp only [e, show n - 2 - 1 = n - 3 by omega, hst]
    have h2 : e (n - 1) = 2 * q := by
      simp only [e, show n - 1 - 1 = n - 3 + 1 by omega, hst']
    have h3 : e n = 2 * p := by
      simp only [e, show n - 1 = (n - 3 + 1) + 1 by omega, st_fst, hst']
    exact concl_of h1 h2 h3 hp h2r hp2q hl

/-- Nagura's theorem in the form `NaguraNat`, from the library (`nagura_nat_lt`). -/
theorem naguraNat_holds : NaguraNat := fun x hx => OpenProblemsLib.Nagura.nagura_nat_lt x hx

/-- **A090905 conjecture**: for n ≥ 5 the last entry of row n is 2p, where p is the largest prime
of row n - 1 = (e (n-2), e (n-1)]. -/
theorem A090905_main (n : ℕ) (hn : 5 ≤ n) :
    ∃ p, p.Prime ∧ e (n - 2) < p ∧ p ≤ e (n - 1) ∧
      (∀ p', p'.Prime → e (n - 2) < p' → p' ≤ e (n - 1) → p' ≤ p) ∧ e n = 2 * p :=
  A090905_of_nagura naguraNat_holds n hn
