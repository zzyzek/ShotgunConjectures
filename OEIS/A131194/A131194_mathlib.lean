import Mathlib
import OpenProblemsLib.PNTApps

/-
OEIS A131194 and A133835.  For a prime p, next_s(p) is the least prime q > p whose decimal digit
multiset shares at least s elements with that of p (s = 3: A131194, seed 101; s = 2: A133835,
seed 11).  Both entries conjecture: for any initial seed the sequence eventually merges with
the main one.

Checked here: the conjecture, for every seed a with at least s digits (a ≥ 10^(s-1); a need not
be prime).
* `A131194_merge`: for every a ≥ 100 there are i, j with next_3^[i] a = next_3^[j] 101.
* `A133835_merge`: for every a ≥ 10 there are i, j with next_2^[i] a = next_2^[j] 11.
* `merge_general`: the same for any 1 ≤ s ≤ 3 and any two seeds with at least s digits.
Argument.  Write a number p with j + 8 digits as p = k·10^j + (low part), 10^7 ≤ k < 10^8 (the
block of p is k).  By the prime number theorem (short-interval form, `exists_prime_block` of
OpenProblemsLib.PNTApps, from PNT+'s `prime_between`), every block contains a prime once j ≥ J.
Then for j ≥ J every p with j + 8 digits below L j (the largest prime below 10^(j+8)) has
next(p) < 10^(j+8): a later prime of the same block shares the 8 digits of k; else, if k does not
end in 99999, a prime of block k + 1 shares the 3 leading digits of k; else a prime of the top
block 99999999 shares three 9s.  So the orbit walks up to L j, and next(L j) lies below
L (j + 1) (a prime of the next top block shares three 9s).  Hence every orbit contains L j for
all large j, and any two orbits meet.
Axioms propext, Classical.choice, Quot.sound.  Nothing is outside Lean; the PNT input is
the vendored PNT+ (lib/PNTPlus), checked with the library.
-/

namespace A131194

/-- Number of decimal digits shared by `p` and `q`, counted with multiplicity. -/
def share (p q : ℕ) : ℕ :=
  ((Nat.digits 10 p : Multiset ℕ) ∩ (Nat.digits 10 q : Multiset ℕ)).card

/-- `q` is a candidate successor of `p`: a larger prime sharing at least `s` digits. -/
def IsNext (s p q : ℕ) : Prop := p < q ∧ q.Prime ∧ s ≤ share p q

open Classical in
/-- The least candidate successor (0 if there is none). -/
noncomputable def next (s p : ℕ) : ℕ := if h : ∃ q, IsNext s p q then Nat.find h else 0

/-- The largest prime below `10^(j+8)`. -/
noncomputable def L (j : ℕ) : ℕ := Nat.findGreatest Nat.Prime (10 ^ (j + 8) - 1)

/-- Every block `(k 10^j, (k+1) 10^j)`, `10^7 ≤ k < 10^8`, `j ≥ J`, contains a prime. -/
def Blocks (J : ℕ) : Prop :=
  ∀ j, J ≤ j → ∀ k, 10 ^ 7 ≤ k → k < 10 ^ 8 →
    ∃ q, q.Prime ∧ k * 10 ^ j < q ∧ q < (k + 1) * 10 ^ j

end A131194

open A131194 OpenProblemsLib.PNTApps

theorem next_spec {s p : ℕ} (h : ∃ q, IsNext s p q) : IsNext s p (next s p) := by
  classical
  simp only [next, h, ↓reduceDIte]; exact Nat.find_spec h

theorem next_le {s p q : ℕ} (hq : IsNext s p q) : next s p ≤ q := by
  classical
  have h : ∃ q, IsNext s p q := ⟨q, hq⟩
  simp only [next, h, ↓reduceDIte]; exact Nat.find_min' h hq

theorem blocks_exist : ∃ J, Blocks J := by
  obtain ⟨X, hX⟩ := exists_prime_block (10 ^ 8)
  refine ⟨X, fun j hj k hk1 hk2 => hX k (10 ^ j) hk2 ?_⟩
  have h1 : j < 10 ^ j := Nat.lt_pow_self (by norm_num)
  have h2 : 10 ^ j ≤ k * 10 ^ j := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-! ## Digits -/

theorem digits_div_pow_le (n i : ℕ) :
    (Nat.digits 10 (n / 10 ^ i) : Multiset ℕ) ≤ Nat.digits 10 n := by
  induction i with
  | zero => simp
  | succ i ih =>
    refine le_trans ?_ ih
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    rcases Nat.eq_zero_or_pos (n / 10 ^ i) with h | h
    · simp [h]
    · conv_rhs => rw [Nat.digits_def' (by norm_num : 1 < 10) h]
      exact Multiset.coe_le.mpr (List.sublist_cons_self _ _).subperm

theorem share_ge_of_le {p q : ℕ} (M : Multiset ℕ) (hp : M ≤ Nat.digits 10 p)
    (hq : M ≤ Nat.digits 10 q) : M.card ≤ share p q :=
  Multiset.card_le_card (Multiset.le_inter hp hq)

theorem share_ge_common {p q i i' x : ℕ} (hp : p / 10 ^ i = x) (hq : q / 10 ^ i' = x) :
    (Nat.digits 10 x).length ≤ share p q := by
  have h1 : (Nat.digits 10 x : Multiset ℕ) ≤ Nat.digits 10 p := by
    rw [← hp]; exact digits_div_pow_le p i
  have h2 : (Nat.digits 10 x : Multiset ℕ) ≤ Nat.digits 10 q := by
    rw [← hq]; exact digits_div_pow_le q i'
  simpa using share_ge_of_le _ h1 h2

theorem nines_le {y : ℕ} (h : y % 1000 = 999) :
    ((([9, 9, 9] : List ℕ)) : Multiset ℕ) ≤ Nat.digits 10 y := by
  have hy : 0 < y := by omega
  rw [Nat.digits_def' (by norm_num) hy]
  have hy1 : 0 < y / 10 := by omega
  rw [Nat.digits_def' (by norm_num) hy1]
  have hy2 : 0 < y / 10 / 10 := by omega
  rw [Nat.digits_def' (by norm_num) hy2]
  have e0 : y % 10 = 9 := by omega
  have e1 : y / 10 % 10 = 9 := by omega
  have e2 : y / 10 / 10 % 10 = 9 := by omega
  rw [e0, e1, e2]
  exact Multiset.coe_le.mpr ((((List.nil_sublist _).cons_cons 9).cons_cons 9).cons_cons 9).subperm

theorem share_ge_three_of_nines {p q i i' : ℕ} (hp : p / 10 ^ i % 1000 = 999)
    (hq : q / 10 ^ i' % 1000 = 999) : 3 ≤ share p q := by
  have := share_ge_of_le _ ((nines_le hp).trans (digits_div_pow_le p i))
    ((nines_le hq).trans (digits_div_pow_le q i'))
  simpa using this

theorem three_le_share_of_hundred {p q i i' x : ℕ} (hp : p / 10 ^ i = x) (hq : q / 10 ^ i' = x)
    (hx : 100 ≤ x) : 3 ≤ share p q :=
  le_trans ((Nat.lt_digits_length_iff (by norm_num) x).mpr (by simpa using hx))
    (share_ge_common hp hq)

/-! ## The largest prime below `10^(j+8)` -/

theorem L_props {J j : ℕ} (hB : Blocks J) (hj : J ≤ j) :
    (L j).Prime ∧ (10 ^ 8 - 1) * 10 ^ j < L j ∧ L j < 10 ^ (j + 8) ∧
      ∀ r, r.Prime → r < 10 ^ (j + 8) → r ≤ L j := by
  have hpow : 10 ^ (j + 8) = 10 ^ 8 * 10 ^ j := by rw [pow_add, mul_comm]
  obtain ⟨q, hq, hq1, hq2⟩ := hB j hj (10 ^ 8 - 1) (by norm_num) (by norm_num)
  have hq2' : q < 10 ^ (j + 8) := by rw [hpow]; simpa using hq2
  have hqle : q ≤ 10 ^ (j + 8) - 1 := by omega
  have hpos : 0 < 10 ^ (j + 8) := by positivity
  refine ⟨Nat.findGreatest_spec hqle hq, lt_of_lt_of_le hq1 (Nat.le_findGreatest hqle hq), ?_,
    fun r hr hr2 => Nat.le_findGreatest (by omega) hr⟩
  have := Nat.findGreatest_le (P := Nat.Prime) (10 ^ (j + 8) - 1)
  simp only [L]; omega

/-! ## One step inside the `(j+8)`-digit range -/

theorem step {J j s p : ℕ} (hB : Blocks J) (hj : J ≤ j) (hs : s ≤ 3)
    (hp1 : 10 ^ (j + 7) ≤ p) (hp2 : p < L j) :
    ∃ q, IsNext s p q ∧ q < 10 ^ (j + 8) := by
  obtain ⟨hLp, hL1, hL2, hLmax⟩ := L_props hB hj
  set m := 10 ^ j with hm
  have hmpos : 0 < m := by positivity
  have hpow8 : 10 ^ (j + 8) = 10 ^ 8 * m := by rw [pow_add, mul_comm]
  have hpow7 : 10 ^ (j + 7) = 10 ^ 7 * m := by rw [pow_add, mul_comm]
  have hpow5 : 10 ^ (j + 5) = m * 10 ^ 5 := by rw [pow_add]
  set k := p / m with hk
  have hk1 : 10 ^ 7 ≤ k := (Nat.le_div_iff_mul_le hmpos).mpr (by rw [← hpow7]; exact hp1)
  have hk2 : k < 10 ^ 8 := (Nat.div_lt_iff_lt_mul hmpos).mpr (by rw [← hpow8]; omega)
  have hkm1 : k * m ≤ p := Nat.div_mul_le_self p m
  have hkm2 : p < (k + 1) * m := by
    have := Nat.lt_mul_div_succ p hmpos; rw [mul_comm] at this; exact this
  by_cases hA : ∃ q, q.Prime ∧ p < q ∧ q < (k + 1) * m
  · obtain ⟨q, hq, hpq, hqk⟩ := hA
    have hqdiv : q / m = k := Nat.div_eq_of_lt_le (by omega) hqk
    refine ⟨q, ⟨hpq, hq, hs.trans (three_le_share_of_hundred hk.symm hqdiv (by omega))⟩, ?_⟩
    rw [hpow8]; calc q < (k + 1) * m := hqk
      _ ≤ 10 ^ 8 * m := Nat.mul_le_mul_right _ (by omega)
  push Not at hA
  by_cases hbad : k % 100000 = 99999
  · -- `k` ends in 99999: use the top block.
    have hktop : k + 1 < 10 ^ 8 := by
      by_contra hc
      have hk' : k + 1 = 10 ^ 8 := by omega
      have := hA (L j) hLp hp2
      rw [hk', ← hpow8] at this
      omega
    obtain ⟨q, hq, hq1, hq2⟩ := hB j hj (10 ^ 8 - 1) (by norm_num) (by norm_num)
    have hpq : p < q := by
      have : (k + 1) * m ≤ (10 ^ 8 - 1) * m := Nat.mul_le_mul_right _ (by omega)
      exact lt_of_lt_of_le hkm2 (this.trans hq1.le)
    have hqdiv : q / m = 10 ^ 8 - 1 := Nat.div_eq_of_lt_le hq1.le (by simpa using hq2)
    have hsh : 3 ≤ share p q :=
      share_ge_three_of_nines (i := j) (i' := j) (by rw [← hm, ← hk]; omega)
        (by rw [← hm, hqdiv]; norm_num)
    refine ⟨q, ⟨hpq, hq, hs.trans hsh⟩, ?_⟩
    rw [hpow8]; simpa using hq2
  · -- Otherwise block `k + 1` shares the leading three digits of `k`.
    have hk3 : k + 1 < 10 ^ 8 := by omega
    obtain ⟨q, hq, hq1, hq2⟩ := hB j hj (k + 1) (by omega) hk3
    have hpq : p < q := lt_trans hkm2 hq1
    have hqdiv : q / m = k + 1 := Nat.div_eq_of_lt_le hq1.le hq2
    have e1 : p / 10 ^ (j + 5) = k / 100000 := by
      rw [hpow5, ← Nat.div_div_eq_div_mul, ← hk]; norm_num
    have e2 : q / 10 ^ (j + 5) = k / 100000 := by
      rw [hpow5, ← Nat.div_div_eq_div_mul, hqdiv]; norm_num; omega
    have hsh : 3 ≤ share p q := three_le_share_of_hundred e1 e2 (by omega)
    refine ⟨q, ⟨hpq, hq, hs.trans hsh⟩, ?_⟩
    rw [hpow8]
    calc q < (k + 1 + 1) * m := hq2
      _ ≤ 10 ^ 8 * m := Nat.mul_le_mul_right _ (by omega)

/-! ## Walking to `L j` and jumping to `L (j+1)` -/

theorem walk {J j s : ℕ} (hB : Blocks J) (hj : J ≤ j) (hs : s ≤ 3) :
    ∀ p, 10 ^ (j + 7) ≤ p → p ≤ L j → ∃ i, (next s)^[i] p = L j := by
  obtain ⟨hLp, hL1, hL2, hLmax⟩ := L_props hB hj
  suffices H : ∀ n p, L j - p = n → 10 ^ (j + 7) ≤ p → p ≤ L j → ∃ i, (next s)^[i] p = L j from
    fun p h1 h2 => H _ p rfl h1 h2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn hp1 hp2
    rcases eq_or_lt_of_le hp2 with h | h
    · exact ⟨0, h⟩
    obtain ⟨q, hq, hq2⟩ := step hB hj hs hp1 h
    have hspec := next_spec ⟨q, hq⟩
    have hle := next_le hq
    have hp'L : next s p ≤ L j := hLmax _ hspec.2.1 (by omega)
    have hlt : p < next s p := hspec.1
    obtain ⟨i, hi⟩ := ih (L j - next s p) (by omega) (next s p) rfl (by have := hspec.1; omega)
      hp'L
    exact ⟨i + 1, by rw [Function.iterate_succ_apply]; exact hi⟩

theorem jump {J j s : ℕ} (hB : Blocks J) (hj : J ≤ j) (hs : s ≤ 3) :
    10 ^ ((j + 1) + 7) ≤ next s (L j) ∧ next s (L j) ≤ L (j + 1) := by
  obtain ⟨hLp, hL1, hL2, hLmax⟩ := L_props hB hj
  obtain ⟨hLp', hL1', hL2', hLmax'⟩ := L_props hB (show J ≤ j + 1 by omega)
  have hpow8 : 10 ^ (j + 8) = 10 ^ 8 * 10 ^ j := by rw [pow_add, mul_comm]
  have hpow9 : 10 ^ (j + 1 + 8) = 10 ^ 8 * 10 ^ (j + 1) := by rw [pow_add, mul_comm]
  obtain ⟨q, hq, hq1, hq2⟩ := hB (j + 1) (by omega) (10 ^ 8 - 1) (by norm_num) (by norm_num)
  have hLdiv : L j / 10 ^ j = 10 ^ 8 - 1 :=
    Nat.div_eq_of_lt_le hL1.le (by rw [show 10 ^ 8 - 1 + 1 = 10 ^ 8 by norm_num, ← hpow8]; exact hL2)
  have hqdiv : q / 10 ^ (j + 1) = 10 ^ 8 - 1 := Nat.div_eq_of_lt_le hq1.le (by simpa using hq2)
  have hsh : 3 ≤ share (L j) q :=
    share_ge_three_of_nines (by rw [hLdiv]; norm_num) (by rw [hqdiv]; norm_num)
  have h10 : 10 ^ (j + 8) ≤ (10 ^ 8 - 1) * 10 ^ (j + 1) := by
    have e : 10 ^ (j + 8) = 10 ^ 7 * 10 ^ (j + 1) := by rw [← pow_add]; ring_nf
    rw [e]; exact Nat.mul_le_mul_right _ (by norm_num)
  have hLq : L j < q := by omega
  have hnext : IsNext s (L j) q := ⟨hLq, hq, hs.trans hsh⟩
  have hspec := next_spec ⟨q, hnext⟩
  have hle := next_le hnext
  have hq9 : q < 10 ^ (j + 1 + 8) := by rw [hpow9]; simpa using hq2
  refine ⟨?_, hLmax' _ hspec.2.1 (by omega)⟩
  by_contra hc
  have : next s (L j) ≤ L j := hLmax _ hspec.2.1 (by
    have : 10 ^ (j + 1 + 7) = 10 ^ (j + 8) := by ring_nf
    omega)
  have := hspec.1
  omega

theorem reach_all {J j s a : ℕ} (hB : Blocks J) (hj : J ≤ j) (hs : s ≤ 3)
    (h : ∃ i, (next s)^[i] a = L j) : ∀ j', j ≤ j' → ∃ i, (next s)^[i] a = L j' := by
  intro j' hj'
  induction j', hj' using Nat.le_induction with
  | base => exact h
  | succ j' hjj' ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨h1, h2⟩ := jump hB (le_trans hj hjj') hs
    obtain ⟨i', hi'⟩ := walk hB (le_trans hj (Nat.le_succ_of_le hjj')) hs _ h1 h2
    refine ⟨i' + (1 + i), ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_add_apply, hi]
    simpa using hi'

/-! ## Every orbit is defined and unbounded -/

theorem exists_next {J s p : ℕ} (hB : Blocks J) (hs1 : 1 ≤ s) (hs : s ≤ 3)
    (hp : 10 ^ (s - 1) ≤ p) : ∃ q, IsNext s p q := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hp
  have hp0 : p ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by positivity) hp)
  set l := (Nat.digits 10 p).length
  have hl1 : s' < l := (Nat.lt_digits_length_iff (by norm_num) p).mpr hp
  have hl2 : p < 10 ^ l := Nat.lt_base_pow_length_digits (by norm_num)
  have hl3 : 10 ^ l ≤ 10 * p := Nat.base_pow_length_digits_le 10 p (by norm_num) hp0
  obtain ⟨d, hd⟩ : ∃ d, l = s' + 1 + d := ⟨l - (s' + 1), by omega⟩
  set t := p / 10 ^ d
  have hpd : 0 < 10 ^ d := by positivity
  have ht1 : t < 10 ^ (s' + 1) := (Nat.div_lt_iff_lt_mul hpd).mpr (by
    rw [← pow_add]; rw [hd] at hl2; exact hl2)
  have ht2 : 10 ^ s' ≤ t := (Nat.le_div_iff_mul_le hpd).mpr (by
    rw [← pow_add]; rw [hd] at hl3
    have : 10 ^ (s' + 1 + d) = 10 * 10 ^ (s' + d) := by ring
    omega)
  set c := 7 - s'
  have hsc : s' + c = 7 := by omega
  set k := t * 10 ^ c
  have hk1 : 10 ^ 7 ≤ k := by
    rw [← hsc, pow_add]; exact Nat.mul_le_mul_right _ ht2
  have hk2 : k < 10 ^ 8 := by
    have : 10 ^ 8 = 10 ^ (s' + 1) * 10 ^ c := by rw [← pow_add]; congr 1; omega
    rw [this]; exact Nat.mul_lt_mul_of_pos_right ht1 (by positivity)
  set j := max J p
  have hjp : p < 10 ^ j := lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) (Nat.pow_le_pow_right
    (by norm_num) (le_max_right _ _))
  obtain ⟨q, hq, hq1, hq2⟩ := hB j (le_max_left _ _) k hk1 hk2
  have hpq : p < q := by
    have : 10 ^ j ≤ k * 10 ^ j := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hqdiv : q / 10 ^ j = k := Nat.div_eq_of_lt_le hq1.le hq2
  have hqt : q / 10 ^ (j + c) = t := by
    rw [pow_add, ← Nat.div_div_eq_div_mul, hqdiv]
    exact Nat.mul_div_cancel _ (by positivity)
  have hsh : s' + 1 ≤ share p q :=
    le_trans ((Nat.lt_digits_length_iff (by norm_num) t).mpr ht2) (share_ge_common rfl hqt)
  exact ⟨q, hpq, hq, hsh⟩

theorem orbit_step {J s a : ℕ} (hB : Blocks J) (hs1 : 1 ≤ s) (hs : s ≤ 3)
    (ha : 10 ^ (s - 1) ≤ a) :
    ∀ i, 10 ^ (s - 1) ≤ (next s)^[i] a ∧ IsNext s ((next s)^[i] a) ((next s)^[i + 1] a) := by
  intro i
  induction i with
  | zero =>
    exact ⟨ha, by simpa using next_spec (exists_next hB hs1 hs ha)⟩
  | succ i ih =>
    have h1 : 10 ^ (s - 1) ≤ (next s)^[i + 1] a := le_trans ih.1 ih.2.1.le
    refine ⟨h1, ?_⟩
    rw [Function.iterate_succ_apply' (next s) (i + 1)]
    exact next_spec (exists_next hB hs1 hs h1)

theorem reaches_some_L {J s a : ℕ} (hB : Blocks J) (hs1 : 1 ≤ s) (hs : s ≤ 3)
    (ha : 10 ^ (s - 1) ≤ a) : ∃ j, J ≤ j ∧ ∃ i, (next s)^[i] a = L j := by
  have hstep := orbit_step hB hs1 hs ha
  have hgrow : ∀ i, i ≤ (next s)^[i] a := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := (hstep i).2.1; omega
  set i := 10 ^ (J + 7) + 1
  set t := (next s)^[i] a
  have ht : 10 ^ (J + 7) ≤ t := by have := hgrow i; omega
  have htprime : t.Prime := by
    have := (hstep (10 ^ (J + 7))).2.2.1; simpa [i, t] using this
  have ht0 : t ≠ 0 := htprime.ne_zero
  set e := Nat.log 10 t
  have he1 : 10 ^ e ≤ t := Nat.pow_log_le_self 10 ht0
  have he2 : t < 10 ^ (e + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
  have he3 : J + 7 ≤ e := Nat.le_log_of_pow_le (by norm_num) ht
  refine ⟨e - 7, by omega, ?_⟩
  have hj : J ≤ e - 7 := by omega
  have e7 : e - 7 + 7 = e := by omega
  have e8 : e - 7 + 8 = e + 1 := by omega
  obtain ⟨_, _, _, hLmax⟩ := L_props hB hj
  have htL : t ≤ L (e - 7) := hLmax t htprime (by rw [e8]; exact he2)
  obtain ⟨i', hi'⟩ := walk hB hj hs t (by rw [e7]; exact he1) htL
  exact ⟨i' + i, by rw [Function.iterate_add_apply]; exact hi'⟩

/-- Any two orbits of `next s` (`1 ≤ s ≤ 3`) from seeds with at least `s` digits meet. -/
theorem merge_general {s a b : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 3) (ha : 10 ^ (s - 1) ≤ a)
    (hb : 10 ^ (s - 1) ≤ b) : ∃ i j, (next s)^[i] a = (next s)^[j] b := by
  obtain ⟨J, hB⟩ := blocks_exist
  obtain ⟨ja, hja, hra⟩ := reaches_some_L hB hs1 hs ha
  obtain ⟨jb, hjb, hrb⟩ := reaches_some_L hB hs1 hs hb
  obtain ⟨i, hi⟩ := reach_all hB hja hs hra (max ja jb) (le_max_left _ _)
  obtain ⟨i', hi'⟩ := reach_all hB hjb hs hrb (max ja jb) (le_max_right _ _)
  exact ⟨i, i', hi.trans hi'.symm⟩

/-- A131194 (s = 3, main seed 101): every seed `a ≥ 100` merges with the main orbit. -/
theorem A131194_merge (a : ℕ) (ha : 100 ≤ a) : ∃ i j, (next 3)^[i] a = (next 3)^[j] 101 :=
  merge_general (by norm_num) le_rfl (by simpa using ha) (by norm_num)

/-- A133835 (s = 2, main seed 11): every seed `a ≥ 10` merges with the main orbit. -/
theorem A133835_merge (a : ℕ) (ha : 10 ≤ a) : ∃ i j, (next 2)^[i] a = (next 2)^[j] 11 :=
  merge_general (by norm_num) (by norm_num) (by simpa using ha) (by norm_num)
