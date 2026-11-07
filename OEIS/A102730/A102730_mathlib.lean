/-
OEIS A102730: number of factorials whose binary word is a contiguous substring of the binary
word of n!. Conjecture in the entry: the sequence is bounded. Checked here (Mathlib): it is
unbounded.

Definitions:
* `a n` = number of k in 0..n with `Nat.digits 2 k!` an infix (contiguous sublist) of
  `Nat.digits 2 n!`. `Nat.digits` is little-endian; a list is an infix of another iff its
  reversal is an infix of the reversal, so this is substring of the usual binary words.
* `oddPart x` = `ordCompl[2] x` (the odd part of x, Mathlib), `oddFact x` = odd part of x!.
* `Bseq N D k` = sum over j < k of 2^(N + j D).

Main theorems:
* `A102730_step`: for every m there is n with m < n and a m + 1 ≤ a n.
* `A102730_unbounded`: for every K there is n with K ≤ a n.

Route (simplified from the README, no Lemma B and no group structure of odd residues).
Fix L = bitlength of oddFact m and congruences mod 2^L.
* `lemmaA`: r 2^L ≤ 2^N implies oddFact (2^N A + r) ≡ oddFact (2^N A) oddFact r, because
  for 1 ≤ i ≤ r the odd part of 2^N A + i is ≡ the odd part of i (`oddPart_shift`).
* Pigeonhole on oddFact (Bseq N (L+1) k) mod 2^L over all k gives i < j with equal residues.
  Bseq at j is 2^(N + i(L+1)) A + Bseq at i with A > 0, and Bseq at i is small enough for
  `lemmaA`, so oddFact (2^(N + i(L+1)) A) ≡ 1 (cancel the odd factor).
* With N = m + L, n = 2^(N + i(L+1)) A + m satisfies oddFact n ≡ oddFact m by `lemmaA`.
* `infix_of_modEq`: digits of x! are v_2(x!) zeros followed by the digits of oddFact x, and
  oddFact n = oddFact m + 2^L q, so the digits of m! are an infix of those of n!
  (v_2(m!) ≤ v_2(n!)). Infix is transitive, and n itself counts, so a n ≥ a m + 1.

Not checked here: agreement of `a` with the terms listed in the OEIS entry (done numerically
in certificate/check.py for a(0..104)); any bound on the size of n.
-/
import Mathlib

/-- OEIS A102730. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun k => (Nat.digits 2 k.factorial) <:+: (Nat.digits 2 n.factorial))).card

/-- Odd part of `x` (with `oddPart 0 = 0`). -/
def oddPart (x : ℕ) : ℕ := ordCompl[2] x

/-- Odd part of `x!`. -/
def oddFact (x : ℕ) : ℕ := oddPart x.factorial

lemma oddFact_zero : oddFact 0 = 1 := by simp [oddFact, oddPart]

lemma oddFact_succ (x : ℕ) : oddFact (x + 1) = oddPart (x + 1) * oddFact x := by
  simp only [oddFact, oddPart, Nat.factorial_succ, Nat.ordCompl_mul]

lemma coprime_oddFact (x : ℕ) : Nat.Coprime 2 (oddFact x) :=
  Nat.coprime_ordCompl Nat.prime_two (Nat.factorial_ne_zero x)

/-- For `1 ≤ i` with `i 2^L ≤ 2^N`, the odd part of `2^N A + i` is `≡` the odd part of `i`. -/
lemma oddPart_shift {L N i : ℕ} (A : ℕ) (hL : 0 < L) (hi : i ≠ 0) (hiN : i * 2 ^ L ≤ 2 ^ N) :
    oddPart (2 ^ N * A + i) ≡ oddPart i [MOD 2 ^ L] := by
  unfold oddPart
  have hio : 2 ^ (i.factorization 2) * (i / 2 ^ (i.factorization 2)) = i :=
    Nat.ordProj_mul_ordCompl_eq_self i 2
  have ho : ¬ 2 ∣ i / 2 ^ (i.factorization 2) := Nat.not_dvd_ordCompl Nat.prime_two hi
  have hv : 2 ^ (i.factorization 2) ≤ i := Nat.ordProj_le 2 hi
  have hvL : i.factorization 2 + L ≤ N := by
    have : 2 ^ (i.factorization 2 + L) ≤ 2 ^ N := by
      rw [pow_add]
      exact le_trans (Nat.mul_le_mul_right _ hv) hiN
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hsplit : 2 ^ N * A + i = 2 ^ (i.factorization 2) *
      (2 ^ (N - i.factorization 2) * A + i / 2 ^ (i.factorization 2)) := by
    rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), hio]
  have hodd : ¬ 2 ∣ 2 ^ (N - i.factorization 2) * A + i / 2 ^ (i.factorization 2) := by
    intro h
    apply ho
    have h2 : 2 ∣ 2 ^ (N - i.factorization 2) * A :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) A
    exact (Nat.dvd_add_right h2).1 h
  rw [hsplit, Nat.ordCompl_pow_mul_of_not_dvd _ Nat.prime_two hodd]
  have hd : 2 ^ L ∣ 2 ^ (N - i.factorization 2) * A :=
    Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (by omega)) A
  simpa using (Nat.modEq_zero_iff_dvd.2 hd).add_right (i / 2 ^ (i.factorization 2))

/-- Lemma A. -/
lemma lemmaA {L N : ℕ} (A : ℕ) (hL : 0 < L) :
    ∀ r, r * 2 ^ L ≤ 2 ^ N → oddFact (2 ^ N * A + r) ≡ oddFact (2 ^ N * A) * oddFact r
      [MOD 2 ^ L] := by
  intro r
  induction r with
  | zero =>
    intro _
    simp only [add_zero, oddFact_zero, mul_one]
    exact Nat.ModEq.refl _
  | succ r ih =>
    intro hr
    have hr' : r * 2 ^ L ≤ 2 ^ N := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ r)) hr
    rw [← add_assoc, oddFact_succ (2 ^ N * A + r), oddFact_succ r]
    calc oddPart (2 ^ N * A + r + 1) * oddFact (2 ^ N * A + r)
        ≡ oddPart (r + 1) * (oddFact (2 ^ N * A) * oddFact r) [MOD 2 ^ L] :=
          Nat.ModEq.mul (by rw [add_assoc]; exact oddPart_shift A hL (Nat.succ_ne_zero r) hr)
            (ih hr')
      _ = oddFact (2 ^ N * A) * (oddPart (r + 1) * oddFact r) := by ring

/-- `Bseq N D k = Σ_{j<k} 2^(N + j D)`. -/
def Bseq (N D : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Bseq N D k + 2 ^ (N + k * D)

lemma Bseq_bound (N L : ℕ) : ∀ k, Bseq N (L + 1) k * 2 ^ L ≤ 2 ^ (N + k * (L + 1)) := by
  intro k
  induction k with
  | zero => simp [Bseq]
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have he : 2 ^ (N + (k + 1) * (L + 1)) = 2 ^ (N + k * (L + 1)) * 2 ^ L * 2 := by ring
    rw [Bseq, add_mul, he]
    nlinarith [ih, h1, Nat.zero_le (2 ^ (N + k * (L + 1)))]

lemma Bseq_split (N D i : ℕ) :
    ∀ d, ∃ A, 0 < A ∧ Bseq N D (i + d + 1) = 2 ^ (N + i * D) * A + Bseq N D i := by
  intro d
  induction d with
  | zero => exact ⟨1, one_pos, by rw [add_zero, Bseq]; ring⟩
  | succ d ih =>
    obtain ⟨A, hA, hB⟩ := ih
    refine ⟨A + 2 ^ ((d + 1) * D), by positivity, ?_⟩
    rw [show i + (d + 1) + 1 = (i + d + 1) + 1 by ring, Bseq, hB]
    have : 2 ^ (N + (i + d + 1) * D) = 2 ^ (N + i * D) * 2 ^ ((d + 1) * D) := by ring
    rw [this]
    ring

/-- For every `L ≥ 1` and `m` there is `n > m` with `oddFact n ≡ oddFact m (mod 2^L)`. -/
lemma core {L : ℕ} (hL : 0 < L) (m : ℕ) : ∃ n, m < n ∧ oddFact n ≡ oddFact m [MOD 2 ^ L] := by
  have hmN : m * 2 ^ L ≤ 2 ^ (m + L) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := m)).le
  have hpos : 0 < 2 ^ L := by positivity
  have key : ∀ i j, i < j →
      oddFact (Bseq (m + L) (L + 1) i) ≡ oddFact (Bseq (m + L) (L + 1) j) [MOD 2 ^ L] →
      ∃ n, m < n ∧ oddFact n ≡ oddFact m [MOD 2 ^ L] := by
    intro i j hij hs
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    obtain ⟨A, hA, hB⟩ := Bseq_split (m + L) (L + 1) i d
    have hNM : 2 ^ (m + L) ≤ 2 ^ (m + L + i * (L + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 := lemmaA A hL (Bseq (m + L) (L + 1) i) (Bseq_bound (m + L) L i)
    rw [← hB] at h1
    have hcop : Nat.gcd (2 ^ L) (oddFact (Bseq (m + L) (L + 1) i)) = 1 :=
      Nat.Coprime.pow_left L (coprime_oddFact _)
    have hC : oddFact (2 ^ (m + L + i * (L + 1)) * A) ≡ 1 [MOD 2 ^ L] := by
      apply Nat.ModEq.cancel_right_of_coprime hcop
      rw [one_mul]
      exact h1.symm.trans hs.symm
    refine ⟨2 ^ (m + L + i * (L + 1)) * A + m, ?_, ?_⟩
    · have : 0 < 2 ^ (m + L + i * (L + 1)) * A := Nat.mul_pos (by positivity) hA
      omega
    · have h2 := lemmaA A hL m (le_trans hmN hNM)
      calc oddFact (2 ^ (m + L + i * (L + 1)) * A + m)
          ≡ oddFact (2 ^ (m + L + i * (L + 1)) * A) * oddFact m [MOD 2 ^ L] := h2
        _ ≡ 1 * oddFact m [MOD 2 ^ L] := hC.mul_right _
        _ = oddFact m := one_mul _
  let f : ℕ → Fin (2 ^ L) :=
    fun k => ⟨oddFact (Bseq (m + L) (L + 1) k) % 2 ^ L, Nat.mod_lt _ hpos⟩
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hs : oddFact (Bseq (m + L) (L + 1) i) ≡ oddFact (Bseq (m + L) (L + 1) j) [MOD 2 ^ L] :=
    congrArg Fin.val hf
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hs
  · exact key j i h hs.symm

/-- Binary digits of `x!`: `v_2(x!)` zeros, then the digits of the odd part. -/
lemma digits_fact (x : ℕ) : Nat.digits 2 x.factorial =
    List.replicate (x.factorial.factorization 2) 0 ++ Nat.digits 2 (oddFact x) := by
  have h := Nat.ordProj_mul_ordCompl_eq_self x.factorial 2
  conv_lhs => rw [← h]
  exact Nat.digits_base_pow_mul (by norm_num) (Nat.ordCompl_pos 2 (Nat.factorial_ne_zero x))

lemma infix_of_modEq {m n : ℕ} (hmn : m ≤ n)
    (h : oddFact n ≡ oddFact m [MOD 2 ^ (Nat.digits 2 (oddFact m)).length]) :
    Nat.digits 2 m.factorial <:+: Nat.digits 2 n.factorial := by
  have hlt : oddFact m < 2 ^ (Nat.digits 2 (oddFact m)).length :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have h' : oddFact n % 2 ^ (Nat.digits 2 (oddFact m)).length =
      oddFact m % 2 ^ (Nat.digits 2 (oddFact m)).length := h
  have hdecomp : oddFact n = oddFact m + 2 ^ (Nat.digits 2 (oddFact m)).length *
      (oddFact n / 2 ^ (Nat.digits 2 (oddFact m)).length) := by
    have := Nat.mod_add_div (oddFact n) (2 ^ (Nat.digits 2 (oddFact m)).length)
    rw [h', Nat.mod_eq_of_lt hlt] at this
    omega
  have hdn : Nat.digits 2 (oddFact n) = Nat.digits 2 (oddFact m) ++
      Nat.digits 2 (oddFact n / 2 ^ (Nat.digits 2 (oddFact m)).length) := by
    rw [Nat.digits_append_digits (by norm_num)]
    exact congrArg (Nat.digits 2) hdecomp
  have hv : m.factorial.factorization 2 ≤ n.factorial.factorization 2 :=
    (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero n)).2
      (Nat.factorial_dvd_factorial hmn) 2
  rw [digits_fact m, digits_fact n, hdn]
  refine ⟨List.replicate (n.factorial.factorization 2 - m.factorial.factorization 2) 0,
    Nat.digits 2 (oddFact n / 2 ^ (Nat.digits 2 (oddFact m)).length), ?_⟩
  rw [show List.replicate (n.factorial.factorization 2) 0 =
      List.replicate (n.factorial.factorization 2 - m.factorial.factorization 2) 0 ++
        List.replicate (m.factorial.factorization 2) 0 by
    rw [← List.replicate_add, Nat.sub_add_cancel hv]]
  simp only [List.append_assoc]

lemma a_step_of_infix {m n : ℕ} (hmn : m < n)
    (h : Nat.digits 2 m.factorial <:+: Nat.digits 2 n.factorial) : a m + 1 ≤ a n := by
  unfold a
  have hsub : insert n ((Finset.range (m + 1)).filter
      (fun k => Nat.digits 2 k.factorial <:+: Nat.digits 2 m.factorial)) ⊆
      (Finset.range (n + 1)).filter
        (fun k => Nat.digits 2 k.factorial <:+: Nat.digits 2 n.factorial) := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_self k), List.infix_refl _⟩
    · rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2.trans h⟩
  have hnot : n ∉ (Finset.range (m + 1)).filter
      (fun k => Nat.digits 2 k.factorial <:+: Nat.digits 2 m.factorial) := by
    simp only [Finset.mem_filter, Finset.mem_range, not_and]
    intro h'
    omega
  rw [← Finset.card_insert_of_notMem hnot]
  exact Finset.card_le_card hsub

theorem A102730_step : ∀ m, ∃ n, m < n ∧ a m + 1 ≤ a n := by
  intro m
  have hL : 0 < (Nat.digits 2 (oddFact m)).length :=
    List.length_pos_iff.2
      (Nat.digits_ne_nil_iff_ne_zero.2 (Nat.ordCompl_pos 2 (Nat.factorial_ne_zero m)).ne')
  obtain ⟨n, hmn, hs⟩ := core hL m
  exact ⟨n, hmn, a_step_of_infix hmn (infix_of_modEq hmn.le hs)⟩

theorem A102730_unbounded : ∀ K, ∃ n, K ≤ a n := by
  intro K
  induction K with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ K ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨n', -, hn'⟩ := A102730_step n
    exact ⟨n', by omega⟩
