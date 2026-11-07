import Mathlib

/-!
# OEIS A103152: a(23) = 725 is not divisible by 3

A103152(n) = smallest odd number which is 2p + q (p, q odd primes) in exactly n ways. The entry's
conjecture "except for the 2nd, 3rd and 4th terms, all terms are divisible by 3" fails at a(23) = 725
(D. S. McNeil, 2010, in the entry).

Main result.
* `A103152_23` : `reps 725 = 23` and `reps m ≠ 23` for every odd m < 725, where `reps m` counts the odd primes
  p with q = m - 2p an odd prime (q ≥ 3). Hence A103152(23) = 725, and 3 ∤ 725.

Checked: all of the above, with primality below 725 reduced to an explicit list `P` (each member proved
prime by `norm_num`; a bitmask `B` of these primes, each non-member below 726 shown to have a divisor among
2..23, and the counts `repsB` evaluated by `decide +kernel`, kernel reduction, not `native_decide`).
-/

def P : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719]

def smallP : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23]

lemma P_prime : ∀ k ∈ P, Nat.Prime k := by
  intro k hk
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Bitmask of the primes below 725. -/
def B : ℕ := 2760529851718890358268076798578308459400086460667767524382036453062798643029691111456041629571334607485359782341806658644021097812034336826194874419862978234595417052425593627301893980692263665201876798434959239555244

def isP (k : ℕ) : Bool := (B >>> k) % 2 == 1

lemma isP_mem : ∀ k < 726, isP k = true → k ∈ P := by decide +kernel

lemma isP_comp : ∀ k < 726, isP k = false → k < 2 ∨ ∃ d ∈ smallP, d ∣ k ∧ d < k := by
  decide +kernel

lemma prime_iff_isP (k : ℕ) (hk : k < 726) : Nat.Prime k ↔ isP k = true := by
  constructor
  · intro hp
    by_contra hn
    rcases isP_comp k hk (by simpa using hn) with h | ⟨d, hd, hdk, hlt⟩
    · exact absurd hp.two_le (by omega)
    · have h2 : 2 ≤ d := by
        simp only [smallP, List.mem_cons, List.not_mem_nil, or_false] at hd
        omega
      rcases hp.eq_one_or_self_of_dvd d hdk with h | h <;> omega
  · intro h; exact P_prime k (isP_mem k hk h)

/-- Number of ways to write m = 2p + q with p, q odd primes. -/
def reps (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun p => p % 2 = 1 ∧ p.Prime ∧ 2 * p + 3 ≤ m ∧
    (m - 2 * p) % 2 = 1 ∧ (m - 2 * p).Prime)).card

/-- The same count with primality read from the bitmask. -/
def repsB (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun p => p % 2 = 1 ∧ isP p = true ∧ 2 * p + 3 ≤ m ∧
    (m - 2 * p) % 2 = 1 ∧ isP (m - 2 * p) = true)).card

lemma reps_eq (m : ℕ) (hm : m ≤ 725) : reps m = repsB m := by
  unfold reps repsB
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_range] at hp
  rw [prime_iff_isP p (by omega), prime_iff_isP (m - 2 * p) (by omega)]

lemma repsB_725 : repsB 725 = 23 := by decide +kernel

lemma repsB_below : ∀ m < 725, m % 2 = 1 → repsB m ≠ 23 := by decide +kernel

theorem A103152_23 : reps 725 = 23 ∧ ∀ m < 725, m % 2 = 1 → reps m ≠ 23 := by
  refine ⟨by rw [reps_eq 725 le_rfl]; exact repsB_725, fun m hm ho => ?_⟩
  rw [reps_eq m hm.le]
  exact repsB_below m hm ho

theorem A103152_23_not_dvd_three : ¬ 3 ∣ 725 := by decide
