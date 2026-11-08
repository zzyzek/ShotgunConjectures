import OpenProblemsLib

/-
OEIS A185104 (Mathlib): primes such that every swap of two decimal digits gives a prime.
Conjecture: the terms after 3911 are R19 = (10^19-1)/9 and R23 = (10^23-1)/9.

Checked here: `R19_term`, `R23_term`: R19 and R23 are terms, with the entry's definition
(`IsTerm`: N prime and the number obtained by exchanging the digits at any two positions i, j
of `Nat.digits 10 N` is prime). A repunit is fixed by every swap, so this is primality,
proved by Pratt certificates (tools/pratt_cert.py, kernel `decide`).

Not checked in Lean: that no other term has 5 to 23 digits (certificate/sieve.c,
certificate/stage2.py, cross-checked by certificate/brute.c and certificate/xcheck.py),
and the terms below 10^6 (stage2.py, brute force).
-/

open OpenProblemsLib

/-- Exchange the digits at positions i and j (least significant digit = position 0). -/
def swapDigits (N i j : ℕ) : ℕ :=
  let l := Nat.digits 10 N
  Nat.ofDigits 10 ((l.set i (l.getD j 0)).set j (l.getD i 0))

def IsTerm (N : ℕ) : Prop :=
  N.Prime ∧ ∀ i j, i < (Nat.digits 10 N).length → j < (Nat.digits 10 N).length →
    (swapDigits N i j).Prime

def cert : List PrattStep :=
  [⟨2, 1, []⟩,
    ⟨3, 2, [(2, 1)]⟩,
    ⟨5, 2, [(2, 2)]⟩,
    ⟨7, 3, [(2, 1), (3, 1)]⟩,
    ⟨11, 2, [(2, 1), (5, 1)]⟩,
    ⟨13, 2, [(2, 2), (3, 1)]⟩,
    ⟨19, 2, [(2, 1), (3, 2)]⟩,
    ⟨37, 2, [(2, 2), (3, 2)]⟩,
    ⟨23, 5, [(2, 1), (11, 1)]⟩,
    ⟨127, 3, [(2, 1), (3, 2), (7, 1)]⟩,
    ⟨52579, 2, [(2, 1), (3, 2), (23, 1), (127, 1)]⟩,
    ⟨41, 6, [(2, 3), (5, 1)]⟩,
    ⟨83, 2, [(2, 1), (41, 1)]⟩,
    ⟨167, 5, [(2, 1), (83, 1)]⟩,
    ⟨333667, 2, [(2, 1), (3, 3), (37, 1), (167, 1)]⟩,
    ⟨1111111111111111111, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (19, 1), (37, 1), (52579, 1), (333667, 1)]⟩,
    ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
    ⟨4093, 2, [(2, 2), (3, 1), (11, 1), (31, 1)]⟩,
    ⟨8779, 11, [(2, 1), (3, 1), (7, 1), (11, 1), (19, 1)]⟩,
    ⟨21649, 14, [(2, 4), (3, 1), (11, 1), (41, 1)]⟩,
    ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩,
    ⟨569, 3, [(2, 3), (71, 1)]⟩,
    ⟨513239, 11, [(2, 1), (11, 1), (41, 1), (569, 1)]⟩,
    ⟨11111111111111111111111, 11, [(2, 1), (5, 1), (11, 2), (23, 1), (4093, 1), (8779, 1), (21649, 1), (513239, 1)]⟩]

lemma swap_replicate (k i j : ℕ) (hi : i < k) (hj : j < k) :
    ((List.replicate k 1).set i ((List.replicate k 1).getD j 0)).set j
      ((List.replicate k 1).getD i 0) = List.replicate k 1 := by
  simp [hi, hj]

theorem repunit_term (k N : ℕ) (hd : Nat.digits 10 N = List.replicate k 1) (hp : N.Prime) :
    IsTerm N := by
  refine ⟨hp, fun i j hi hj => ?_⟩
  rw [hd, List.length_replicate] at hi hj
  have : swapDigits N i j = N := by
    unfold swapDigits
    simp only [hd, swap_replicate k i j hi hj]
    rw [← hd, Nat.ofDigits_digits]
  rw [this]; exact hp

theorem R19_term : IsTerm 1111111111111111111 :=
  repunit_term 19 _ (by norm_num) (prime_of_prattCertifies _ cert (by decide +kernel))

theorem R23_term : IsTerm 11111111111111111111111 :=
  repunit_term 23 _ (by norm_num) (prime_of_prattCertifies _ cert (by decide +kernel))
