/-
OEIS A213507, Mathlib proof.

A213507: e.g.f. exp(Sum_{n>=1} Catalan(n) x^n/n). In Lean `E` is the
power series `(exp ℚ).subst L` with `L = Sum_{n>=1} catalan n X^n / n`,
and `a` is the integer sequence given by the recurrence
  a(0) = 1,  a(n+1) = Sum_{j=0..n} n!/(n-j)! Catalan(j+1) a(n-j)
(`a_eq_coeff`: a n = n! [X^n] E, from E' = L' E).

Conjecture in the entry: a(n) is never divisible by
2, 5, 13, 29, 31, 37, 41, 43, 53, 71, 97.

Main theorem `A213507_main`: for each of these p and every n, n! [X^n] E is
a natural number not divisible by p.

Method (per prime, Bala's congruence in finite form). Modulo p the terms
with j >= p vanish (p | j! | n!/(n-j)!), and n!/(n-j)! mod p is unchanged
when n grows by 2p, so for n >= p the recurrence is an order-p recurrence
with coefficients periodic in n (`rec_trunc`, `desc_shift`). Hence
a(n+2p) = a(n) mod p for all n once it holds for n < p (`periodic`).
The finite check (a(n+2p) = a(n) mod p for n < p and a(n) != 0 mod p for
n < 2p) is a kernel computation (`check`, `decide +kernel`) of a verified
evaluator of the recurrence mod p (`tab_spec`).

`A213507_antiperiodic`: for each listed p and every n, a(n+p) = -a(n) (mod p)
(same argument with shift p: `antiperiodic`, finite check `checkNeg` for n < p).

Outside Lean: none.
-/
import Mathlib

open PowerSeries Finset
open scoped Nat

namespace A213507

/-- `L = Sum_{n>=1} Catalan(n) X^n / n`. -/
noncomputable def L : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (catalan n : ℚ) / n

/-- The e.g.f. `exp(L)`. -/
noncomputable def E : ℚ⟦X⟧ := (exp ℚ).subst L

/-- The sequence, by the recurrence coming from `E' = L' E`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ j : Fin (n + 1), n.descFactorial j * catalan (j + 1) * a (n - j)

lemma a_succ (n : ℕ) :
    a (n + 1) = ∑ j ∈ range (n + 1), n.descFactorial j * catalan (j + 1) * a (n - j) := by
  rw [a, Fin.sum_univ_eq_sum_range (fun j => n.descFactorial j * catalan (j + 1) * a (n - j))]

lemma L0 : constantCoeff L = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, L, coeff_mk]; simp

lemma hL : HasSubst L := HasSubst.of_constantCoeff_zero' L0

lemma E0 : coeff 0 E = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, E]
  have := constantCoeff_subst_of_constantCoeff_zero (S := ℚ) L0 (exp ℚ)
  simp at this
  exact this

lemma dE : d⁄dX E = E * d⁄dX L := by
  rw [E, derivative_subst hL, derivative_exp]

lemma coeff_dL (j : ℕ) : coeff j (d⁄dX L) = catalan (j + 1) := by
  rw [coeff_derivative, L, coeff_mk]
  simp only [Nat.add_one_ne_zero, ite_false]
  push_cast
  field_simp

/-- The recurrence gives the coefficients of `E`. -/
theorem a_eq_coeff (n : ℕ) : (a n : ℚ) = n ! * coeff n E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · simp [a, E0]
  · have h1 : coeff (n + 1) E * (n + 1) =
        ∑ k ∈ range (n + 1), (catalan (k + 1) : ℚ) * coeff (n - k) E := by
      rw [← coeff_derivative, dE, mul_comm, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [coeff_dL]
    have h2 : ∀ k ∈ range (n + 1), (n.descFactorial k : ℚ) * catalan (k + 1) * a (n - k) =
        n ! * (catalan (k + 1) * coeff (n - k) E) := by
      intro k hk
      rw [ih (n - k) (by omega)]
      have hk' : k ≤ n := by simp at hk; omega
      have h3 : ((n - k)! : ℚ) * n.descFactorial k = n ! := by
        exact_mod_cast Nat.factorial_mul_descFactorial hk'
      rw [← h3]; ring
    rw [a_succ]; push_cast
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← h1, Nat.factorial_succ]
    push_cast; ring

/-! ### The recurrence modulo p -/

lemma desc_zero (p N j : ℕ) (hp : 0 < p) (hj : p ≤ j) :
    ((N.descFactorial j : ℕ) : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact (Nat.dvd_factorial hp hj).trans (Nat.factorial_dvd_descFactorial N j)

lemma desc_shift (p N j : ℕ) (hj : j ≤ N) :
    (((N + 2 * p).descFactorial j : ℕ) : ZMod p) = (N.descFactorial j : ZMod p) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : N + 2 * p - j = (N - j) + 2 * p := by omega
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, h]
    push_cast
    rw [ih (by omega)]
    simp

/-- For `n >= p` only the terms `j < p` survive modulo `p`. -/
lemma rec_trunc (p N : ℕ) (hp : 0 < p) (hN : p ≤ N + 1) :
    ((a (N + 1) : ℕ) : ZMod p) =
      ∑ j ∈ range p, (N.descFactorial j : ZMod p) * catalan (j + 1) * a (N - j) := by
  rw [a_succ]; push_cast
  symm
  apply Finset.sum_subset (range_subset_range.2 hN)
  intro j _ hj'
  simp only [mem_range, not_lt] at hj'
  rw [desc_zero p N j hp hj']; simp

theorem periodic (p : ℕ) (hp : 0 < p) (base : ∀ n < p, (a (n + 2 * p) : ZMod p) = a n) :
    ∀ n, (a (n + 2 * p) : ZMod p) = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hn : n < p
  · exact base n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [show N + 1 + 2 * p = (N + 2 * p) + 1 by ring, rec_trunc p _ hp (by omega),
    rec_trunc p N hp (by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mem_range] at hj
  rw [desc_shift p N j (by omega), show N + 2 * p - j = (N - j) + 2 * p by omega,
    ih (N - j) (by omega)]

lemma periodic_mod (p : ℕ) (hp : 0 < p) (base : ∀ n < p, (a (n + 2 * p) : ZMod p) = a n)
    (n : ℕ) : (a n : ZMod p) = a (n % (2 * p)) := by
  have h : ∀ q r, (a (r + 2 * p * q) : ZMod p) = a r := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      intro r
      rw [show r + 2 * p * (q + 1) = (r + 2 * p * q) + 2 * p by ring,
        periodic p hp base, ih]
  conv_lhs => rw [← Nat.mod_add_div n (2 * p)]
  exact h _ _

theorem not_dvd (p : ℕ) (hp : 0 < p) (base : ∀ n < p, (a (n + 2 * p) : ZMod p) = a n)
    (nz : ∀ n < 2 * p, (a n : ZMod p) ≠ 0) (n : ℕ) : ¬ p ∣ a n := by
  intro h
  apply nz (n % (2 * p)) (Nat.mod_lt _ (by omega))
  rw [← periodic_mod p hp base]
  exact (ZMod.natCast_eq_zero_iff _ _).2 h

/-! ### A verified evaluator of the recurrence modulo p -/

def dot3 : List ℕ → List ℕ → List ℕ → ℕ
  | x :: xs, y :: ys, z :: zs => x * y * z + dot3 xs ys zs
  | _, _, _ => 0

lemma dot3_eq : ∀ (l1 l2 l3 : List ℕ) (k : ℕ), l1.length ≤ k →
    dot3 l1 l2 l3 = ∑ j ∈ range k, l1.getD j 0 * l2.getD j 0 * l3.getD j 0
  | [], l2, l3, k, _ => by simp [dot3]
  | x :: xs, [], l3, k, _ => by simp [dot3]
  | x :: xs, y :: ys, [], k, _ => by simp [dot3]
  | x :: xs, y :: ys, z :: zs, k, h => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', dot3, dot3_eq xs ys zs k (by simp at h; omega)]
    simp [add_comm]

lemma getD_map_zero (f : ℕ → ℕ) (hf : f 0 = 0) :
    ∀ (l : List ℕ) (j : ℕ), (l.map f).getD j 0 = f (l.getD j 0)
  | [], j => by simp [hf]
  | x :: xs, 0 => by simp
  | x :: xs, j + 1 => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ, getD_map_zero f hf xs j]

/-- `catList c j k` lists `k` Catalan numbers from index `j` when `c = Catalan(j)`. -/
def catList : ℕ → ℕ → ℕ → List ℕ
  | _, _, 0 => []
  | c, j, k + 1 => c :: catList (c * (4 * j + 2) / (j + 2)) (j + 1) k

lemma catalan_succ_eq (j : ℕ) : catalan (j + 1) = catalan j * (4 * j + 2) / (j + 2) := by
  have h1 := succ_mul_catalan_eq_centralBinom (j + 1)
  have h2 := Nat.succ_mul_centralBinom_succ j
  have h3 := succ_mul_catalan_eq_centralBinom j
  have h4 : (j + 1) * (catalan (j + 1) * (j + 2)) = (j + 1) * (catalan j * (4 * j + 2)) := by
    calc (j + 1) * (catalan (j + 1) * (j + 2))
        = (j + 1) * ((j + 1 + 1) * catalan (j + 1)) := by ring
      _ = (j + 1) * (j + 1).centralBinom := by rw [h1]
      _ = 2 * (2 * j + 1) * j.centralBinom := h2
      _ = 2 * (2 * j + 1) * ((j + 1) * catalan j) := by rw [h3]
      _ = (j + 1) * (catalan j * (4 * j + 2)) := by ring
  have h5 := Nat.eq_of_mul_eq_mul_left (by omega) h4
  rw [← h5, Nat.mul_div_cancel _ (by omega)]

lemma catList_getD : ∀ (k j i : ℕ),
    (catList (catalan j) j k).getD i 0 = if i < k then catalan (j + i) else 0
  | 0, j, i => by simp [catList]
  | k + 1, j, 0 => by simp [catList]
  | k + 1, j, i + 1 => by
    rw [catList, ← catalan_succ_eq, List.getD_cons_succ, catList_getD k (j + 1) i]
    simp only [Nat.add_lt_add_iff_right]
    rw [show j + 1 + i = j + (i + 1) by ring]

/-- `tab p cs n = (row of n!/(n-j)! mod p, [a(n), ..., a(0)] mod p)`. -/
def tab (p : ℕ) (cs : List ℕ) : ℕ → List ℕ × List ℕ
  | 0 => ([1 % p], [1 % p])
  | n + 1 =>
    let t := tab p cs n
    (1 % p :: t.1.map (fun e => (n + 1) * e % p), dot3 t.1 cs t.2 % p :: t.2)

lemma tab_spec (p : ℕ) (cs : List ℕ) (M : ℕ)
    (hcs : ∀ j < M, cs.getD j 0 = catalan (j + 1) % p) :
    ∀ n < M, (tab p cs n).1.length = n + 1 ∧
      (∀ j, (tab p cs n).1.getD j 0 = n.descFactorial j % p) ∧
      (∀ j ≤ n, (tab p cs n).2.getD j 0 = a (n - j) % p) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨rfl, ?_, ?_⟩
    · intro j; rcases j with _ | j <;> simp [tab]
    · intro j hj; obtain rfl : j = 0 := by omega
      simp [tab, a]
  | succ n ih =>
    intro hn
    obtain ⟨hl, hd, hr⟩ := ih (by omega)
    refine ⟨by simp [tab, hl], ?_, ?_⟩
    · intro j
      rcases j with _ | j
      · simp [tab]
      · simp only [tab, List.getD_cons_succ]
        rw [getD_map_zero _ (by simp), hd j, Nat.mul_mod_mod, Nat.succ_descFactorial_succ]
    · intro j hj
      rcases j with _ | j
      · simp only [tab, List.getD_cons_zero, Nat.sub_zero]
        rw [dot3_eq _ _ _ (n + 1) hl.le, a_succ, ← ZMod.natCast_eq_natCast_iff']
        push_cast
        apply Finset.sum_congr rfl
        intro k hk
        simp only [mem_range] at hk
        rw [hd k, hcs k (by omega), hr k (by omega)]
        simp [ZMod.natCast_mod]
      · simp only [tab, List.getD_cons_succ]
        rw [hr j (by omega), show n + 1 - (j + 1) = n - j by omega]

/-- The finite check for one modulus `p`. -/
def check (p : ℕ) : Bool :=
  let M := 3 * p
  let cs := (catList 1 1 M).map (· % p)
  let R := (tab p cs (M - 1)).2
  (List.range p).all (fun n => R.getD (M - 1 - (n + 2 * p)) 0 == R.getD (M - 1 - n) 0) &&
  (List.range (2 * p)).all (fun n => R.getD (M - 1 - n) 0 != 0)

theorem check_sound (p : ℕ) (hp : 0 < p) (h : check p = true) (n : ℕ) : ¬ p ∣ a n := by
  have hcs : ∀ j < 3 * p, ((catList 1 1 (3 * p)).map (· % p)).getD j 0 = catalan (j + 1) % p := by
    intro j hj
    have e1 : catList 1 1 (3 * p) = catList (catalan 1) 1 (3 * p) := by rw [catalan_one]
    rw [getD_map_zero _ (by simp), e1, catList_getD]
    simp [hj, add_comm]
  have hR := fun m hm => (tab_spec p _ (3 * p) hcs (3 * p - 1) (by omega)).2.2 (3 * p - 1 - m) hm
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2⟩ := h
  apply not_dvd p hp
  · intro m hm
    have e := h1 m hm
    rw [hR _ (by omega), hR _ (by omega), show 3 * p - 1 - (3 * p - 1 - (m + 2 * p)) = m + 2 * p
      by omega, show 3 * p - 1 - (3 * p - 1 - m) = m by omega] at e
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).2 e
  · intro m hm
    have e := h2 m hm
    rw [hR _ (by omega), show 3 * p - 1 - (3 * p - 1 - m) = m by omega] at e
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => e (Nat.mod_eq_zero_of_dvd hd)

theorem check_2 : check 2 = true := by decide +kernel
theorem check_5 : check 5 = true := by decide +kernel
theorem check_13 : check 13 = true := by decide +kernel
theorem check_29 : check 29 = true := by decide +kernel
theorem check_31 : check 31 = true := by decide +kernel
theorem check_37 : check 37 = true := by decide +kernel
theorem check_41 : check 41 = true := by decide +kernel
theorem check_43 : check 43 = true := by decide +kernel
theorem check_53 : check 53 = true := by decide +kernel
theorem check_71 : check 71 = true := by decide +kernel
theorem check_97 : check 97 = true := by decide +kernel

/-- Main theorem: for each listed `p`, every term `n! [X^n] exp(L)` is a natural
number not divisible by `p`. -/
theorem A213507_main (p : ℕ) (hp : p ∈ [2, 5, 13, 29, 31, 37, 41, 43, 53, 71, 97]) (n : ℕ) :
    ∃ z : ℕ, (z : ℚ) = n ! * coeff n E ∧ ¬ p ∣ z := by
  refine ⟨a n, a_eq_coeff n, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_sound 2 (by norm_num) check_2 n
  · exact check_sound 5 (by norm_num) check_5 n
  · exact check_sound 13 (by norm_num) check_13 n
  · exact check_sound 29 (by norm_num) check_29 n
  · exact check_sound 31 (by norm_num) check_31 n
  · exact check_sound 37 (by norm_num) check_37 n
  · exact check_sound 41 (by norm_num) check_41 n
  · exact check_sound 43 (by norm_num) check_43 n
  · exact check_sound 53 (by norm_num) check_53 n
  · exact check_sound 71 (by norm_num) check_71 n
  · exact check_sound 97 (by norm_num) check_97 n


/-! ### The antiperiodicity a(n+p) = -a(n) mod p -/

lemma desc_shift_p (p N j : ℕ) (hj : j ≤ N) :
    (((N + p).descFactorial j : ℕ) : ZMod p) = (N.descFactorial j : ZMod p) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : N + p - j = (N - j) + p := by omega
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, h]
    push_cast
    rw [ih (by omega)]
    simp

theorem antiperiodic (p : ℕ) (hp : 0 < p) (base : ∀ n < p, (a (n + p) : ZMod p) = -a n) :
    ∀ n, (a (n + p) : ZMod p) = -a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hn : n < p
  · exact base n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [show N + 1 + p = (N + p) + 1 by ring, rec_trunc p _ hp (by omega),
    rec_trunc p N hp (by omega), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mem_range] at hj
  rw [desc_shift_p p N j (by omega), show N + p - j = (N - j) + p by omega,
    ih (N - j) (by omega)]
  ring

/-- The finite check of `a(n+p) + a(n) = 0 mod p` for `n < p`. -/
def checkNeg (p : ℕ) : Bool :=
  let M := 3 * p
  let cs := (catList 1 1 M).map (· % p)
  let R := (tab p cs (M - 1)).2
  (List.range p).all (fun n => (R.getD (M - 1 - (n + p)) 0 + R.getD (M - 1 - n) 0) % p == 0)

theorem checkNeg_sound (p : ℕ) (hp : 0 < p) (h : checkNeg p = true) (n : ℕ) :
    (a (n + p) : ZMod p) = -a n := by
  have hcs : ∀ j < 3 * p, ((catList 1 1 (3 * p)).map (· % p)).getD j 0 = catalan (j + 1) % p := by
    intro j hj
    have e1 : catList 1 1 (3 * p) = catList (catalan 1) 1 (3 * p) := by rw [catalan_one]
    rw [getD_map_zero _ (by simp), e1, catList_getD]
    simp [hj, add_comm]
  have hR := fun m hm => (tab_spec p _ (3 * p) hcs (3 * p - 1) (by omega)).2.2 (3 * p - 1 - m) hm
  simp only [checkNeg, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  apply antiperiodic p hp _ n
  intro m hm
  have e := h m hm
  rw [hR _ (by omega), hR _ (by omega), show 3 * p - 1 - (3 * p - 1 - (m + p)) = m + p
    by omega, show 3 * p - 1 - (3 * p - 1 - m) = m by omega] at e
  have e2 : ((a (m + p) % p + a m % p : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero e
  push_cast [ZMod.natCast_mod] at e2
  exact eq_neg_of_add_eq_zero_left e2

theorem checkNeg_2 : checkNeg 2 = true := by decide +kernel
theorem checkNeg_5 : checkNeg 5 = true := by decide +kernel
theorem checkNeg_13 : checkNeg 13 = true := by decide +kernel
theorem checkNeg_29 : checkNeg 29 = true := by decide +kernel
theorem checkNeg_31 : checkNeg 31 = true := by decide +kernel
theorem checkNeg_37 : checkNeg 37 = true := by decide +kernel
theorem checkNeg_41 : checkNeg 41 = true := by decide +kernel
theorem checkNeg_43 : checkNeg 43 = true := by decide +kernel
theorem checkNeg_53 : checkNeg 53 = true := by decide +kernel
theorem checkNeg_71 : checkNeg 71 = true := by decide +kernel
theorem checkNeg_97 : checkNeg 97 = true := by decide +kernel

/-- For each listed `p` and every `n`, `a(n+p) = -a(n) (mod p)`. -/
theorem A213507_antiperiodic (p : ℕ) (hp : p ∈ [2, 5, 13, 29, 31, 37, 41, 43, 53, 71, 97])
    (n : ℕ) : (a (n + p) : ZMod p) = -a n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkNeg_sound 2 (by norm_num) checkNeg_2 n
  · exact checkNeg_sound 5 (by norm_num) checkNeg_5 n
  · exact checkNeg_sound 13 (by norm_num) checkNeg_13 n
  · exact checkNeg_sound 29 (by norm_num) checkNeg_29 n
  · exact checkNeg_sound 31 (by norm_num) checkNeg_31 n
  · exact checkNeg_sound 37 (by norm_num) checkNeg_37 n
  · exact checkNeg_sound 41 (by norm_num) checkNeg_41 n
  · exact checkNeg_sound 43 (by norm_num) checkNeg_43 n
  · exact checkNeg_sound 53 (by norm_num) checkNeg_53 n
  · exact checkNeg_sound 71 (by norm_num) checkNeg_71 n
  · exact checkNeg_sound 97 (by norm_num) checkNeg_97 n
