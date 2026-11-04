/-
OEIS A089758 (the primes arising in A089757), conjecture: the sequence is
infinite.  A089757: start from the string "1"; each step prepends the least
multiple of 3 larger than the previous term such that the decimal
concatenation a(n)a(n-1)...a(1)1 is prime.

Formalisation.  `chain n = (last, C)`: last is the n-th term (0 at the start)
and C the current concatenation (1 at the start).  One step takes the least
t with t > last, 3 ∣ t and `concat t C` prime, where
`concat t C = Nat.ofDigits 10 (Nat.digits 10 C ++ Nat.digits 10 t)` is the
decimal string of t followed by that of C (`concat_eq`: = t·10^L + C,
L = number of digits of C).  If no such t existed the definition would put 0.

Main theorem `A089758_conjecture`: every step succeeds — the (n+1)-th term is
the least admissible t (`IsLeast`), and the concatenations C_(n+1) are prime
and strictly increasing, so the set of primes of A089758 is infinite.  This is
the README result.  Proof: C is coprime to 30 at every stage (C = 1, then
primes ≥ 31), so gcd(C, 3·10^L) = 1 and Dirichlet's theorem (Mathlib
`Nat.forall_exists_prime_gt_and_modEq`) gives primes C + 3·10^L·y beyond any
bound.

Not checked: nothing outside Lean.  (That the greedy chain reproduces the
printed terms is checked in certificate/check.py, not here.)
-/
import Mathlib

/-- Decimal concatenation: the digits of t followed by the digits of C. -/
def concat (t C : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 C ++ Nat.digits 10 t)

lemma concat_eq (t C : ℕ) : concat t C = t * 10 ^ (Nat.digits 10 C).length + C := by
  unfold concat
  rw [Nat.ofDigits_append, Nat.ofDigits_digits, Nat.ofDigits_digits]; ring

/-- The admissible next terms after `last` with current concatenation `C`. -/
def Admissible (last C t : ℕ) : Prop := last < t ∧ 3 ∣ t ∧ (concat t C).Prime

instance (last C : ℕ) : DecidablePred (Admissible last C) := fun t => by
  unfold Admissible; infer_instance

lemma exists_admissible (last C : ℕ) (hC : Nat.Coprime C 30) :
    ∃ t, Admissible last C t := by
  set L := (Nat.digits 10 C).length
  have h3 : Nat.Coprime C 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hC
  have h10 : Nat.Coprime C 10 := Nat.Coprime.coprime_dvd_right (by norm_num) hC
  have hq : Nat.Coprime C (3 * 10 ^ L) := Nat.Coprime.mul_right h3 (h10.pow_right L)
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq ((last + 1) * 10 ^ L + C) (by positivity) hq
  have hCp : C ≤ p := by
    have : C ≤ (last + 1) * 10 ^ L + C := Nat.le_add_left _ _
    omega
  obtain ⟨y, hy⟩ := (Nat.modEq_iff_dvd' hCp).1 hmod.symm
  refine ⟨3 * y, ?_, ⟨y, rfl⟩, ?_⟩
  · have hpos : 0 < 10 ^ L := by positivity
    have : (last + 1) * 10 ^ L < 3 * y * 10 ^ L := by
      have : p = 3 * 10 ^ L * y + C := by omega
      nlinarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  · rw [concat_eq]
    have : 3 * y * 10 ^ L + C = p := by
      have : p - C = 3 * 10 ^ L * y := hy
      have : 3 * y * 10 ^ L = 3 * 10 ^ L * y := by ring
      omega
    rw [this]; exact hp

open Classical in
/-- The greedy chain: `(last term, current concatenation)`. -/
noncomputable def chain : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let s := chain n
    if h : ∃ t, Admissible s.1 s.2 t then
      (Nat.find h, concat (Nat.find h) s.2)
    else (0, 0)

lemma chain_invariant (n : ℕ) : Nat.Coprime (chain n).2 30 := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    have h := exists_admissible (chain n).1 (chain n).2 ih
    simp only [chain]
    simp only [h, ↓reduceDIte]
    obtain ⟨hlt, h3, hp⟩ := Nat.find_spec h
    have hC0 : (chain n).2 ≠ 0 := by
      intro h0; rw [h0] at ih; norm_num at ih
    have hL : 1 ≤ (Nat.digits 10 (chain n).2).length :=
      List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hC0)
    have ht : 3 ≤ Nat.find h := by
      obtain ⟨c, hc⟩ := h3; omega
    have hbig : 30 < concat (Nat.find h) (chain n).2 := by
      rw [concat_eq]
      have : 10 ≤ 10 ^ (Nat.digits 10 (chain n).2).length := by
        calc 10 = 10 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hL
      have : 30 ≤ Nat.find h * 10 ^ (Nat.digits 10 (chain n).2).length := by nlinarith
      have : 1 ≤ (chain n).2 := Nat.one_le_iff_ne_zero.mpr hC0
      omega
    show Nat.Coprime (concat (Nat.find h) (chain n).2) 30
    exact (Nat.Prime.coprime_iff_not_dvd hp).2
      (fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (by omega))

theorem A089758_conjecture :
    (∀ n, IsLeast {t | Admissible (chain n).1 (chain n).2 t} (chain (n + 1)).1) ∧
    (∀ n, (chain (n + 1)).2 = concat (chain (n + 1)).1 (chain n).2) ∧
    (∀ n, ((chain (n + 1)).2).Prime) ∧
    StrictMono (fun n => (chain (n + 1)).2) ∧
    {p | ∃ n, (chain (n + 1)).2 = p}.Infinite := by
  have hstep : ∀ n, ∃ t, Admissible (chain n).1 (chain n).2 t :=
    fun n => exists_admissible _ _ (chain_invariant n)
  have hval : ∀ n, chain (n + 1) =
      (Nat.find (hstep n), concat (Nat.find (hstep n)) (chain n).2) := by
    intro n
    simp only [chain]
    split_ifs with hh
    · rfl
    · exact absurd (hstep n) hh
  have hleast : ∀ n, IsLeast {t | Admissible (chain n).1 (chain n).2 t} (chain (n + 1)).1 := by
    intro n
    rw [hval n]
    exact ⟨Nat.find_spec (hstep n), fun t ht => Nat.find_min' (hstep n) ht⟩
  have hcat : ∀ n, (chain (n + 1)).2 = concat (chain (n + 1)).1 (chain n).2 := by
    intro n; rw [hval n]
  have hprime : ∀ n, ((chain (n + 1)).2).Prime := by
    intro n; rw [hcat n]; exact (hleast n).1.2.2
  have hinc : ∀ n, (chain n).2 < (chain (n + 1)).2 := by
    intro n
    rw [hcat n, concat_eq]
    have ht : 0 < (chain (n + 1)).1 := by
      have := (hleast n).1.1; omega
    have : 0 < (chain (n + 1)).1 * 10 ^ (Nat.digits 10 (chain n).2).length := by positivity
    omega
  have hmono : StrictMono (fun n => (chain (n + 1)).2) :=
    strictMono_nat_of_lt_succ (fun n => hinc (n + 1))
  refine ⟨hleast, hcat, hprime, hmono, ?_⟩
  have : {p | ∃ n, (chain (n + 1)).2 = p} = Set.range (fun n => (chain (n + 1)).2) := by
    ext p; simp
  rw [this]
  exact Set.infinite_range_of_injective hmono.injective
