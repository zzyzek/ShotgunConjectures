/-
OEIS A047926, Z. Seidov's comment (2012): a(n) = (3^(n+1) + 2n + 1)/4 counts the
representations of 3^(2n) as a^2 + b^2 + c^2 with 0 < a ≤ b ≤ c.

`A047926_C N` = #{(a, b, c) : 0 < a ≤ b ≤ c, a^2 + b^2 + c^2 = N}.
`A047926_P n` = the same count for N = 9^n restricted to triples with not all of a, b, c
divisible by 3 ("primitive"; mod 3 these have all of a, b, c prime to 3).

Checked here:
* `A047926_misindexed`: C(9) = 1 while a(1) = 3, and C(81) = 3 = a(1), C(729) = 8 = a(2).
  The comment is off by one: the correct statement is a(n) = C(3^(2n+2)) = C(9^(n+1)).
* `A047926_desc`: C(9M) = C(M) + #(primitive solutions of 9M) (all-divisible-by-3 solutions of
  9M are 3·(solutions of M)).
* `A047926_iff` (main): the corrected conjecture ∀ n, C(9^(n+1)) = a(n) holds if and only if
  ∀ n, 2·P(n+1) = 3^n + 1, i.e. 9^(n+1) has exactly (3^n + 1)/2 primitive sorted representations.
* `A047926_P_small`: P(1) = 1, P(2) = 2, P(3) = 5 (so the corrected statement holds for n ≤ 2).

Not checked in Lean (missing piece): P(n) = (3^(n-1) + 1)/2 for all n ≥ 1. It is equivalent
(by orbit counting under signs and permutations, done in the README, outside Lean) to the
classical Gauss–Hurwitz value r_3(9^n) = 6(2·3^n − 1) for the number of integer
representations of 9^n as a sum of three squares; Mathlib has neither this formula nor any
r_3 counting result.
-/
import Mathlib

open Finset

/-- Sorted positive triples below B with squares summing to N. -/
def A047926_box (B N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range B ×ˢ range B ×ˢ range B).filter
    (fun t => 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = N)

/-- All sorted positive representations of N (the bound N + 1 is never reached). -/
def A047926_sol (N : ℕ) : Finset (ℕ × ℕ × ℕ) := A047926_box (N + 1) N

/-- C(N) = #{0 < a ≤ b ≤ c : a^2 + b^2 + c^2 = N}. -/
def A047926_C (N : ℕ) : ℕ := (A047926_sol N).card

/-- Primitive (not all coordinates divisible by 3) sorted representations of 9^n. -/
def A047926_P (n : ℕ) : ℕ :=
  ((A047926_sol (9 ^ n)).filter (fun t => ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2))).card

/-- The sequence A047926 (offset 0). -/
def A047926_a (n : ℕ) : ℕ := (3 ^ (n + 1) + 2 * n + 1) / 4

theorem A047926_lt {c N B : ℕ} (h : c ^ 2 ≤ N) (hB : N < B * B) : c < B := by
  by_contra h'
  have := Nat.mul_le_mul (not_lt.mp h') (not_lt.mp h')
  nlinarith

theorem A047926_mem {B N : ℕ} (hB : N < B * B) (t : ℕ × ℕ × ℕ) :
    t ∈ A047926_box B N ↔
      (0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = N) := by
  unfold A047926_box
  rw [mem_filter, mem_product, mem_product, mem_range, mem_range, mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨A047926_lt (by nlinarith) hB, A047926_lt (by nlinarith) hB,
      A047926_lt (by nlinarith) hB⟩, h1, h2, h3, h4⟩

theorem A047926_sol_mem {N : ℕ} (t : ℕ × ℕ × ℕ) :
    t ∈ A047926_sol N ↔
      (0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = N) :=
  A047926_mem (by nlinarith) t

theorem A047926_sol_eq {B N : ℕ} (hB : N < B * B) : A047926_sol N = A047926_box B N := by
  ext t
  rw [A047926_sol_mem, A047926_mem hB]

/-- Descent: solutions of 9M with 3 dividing every coordinate are 3·(solutions of M). -/
theorem A047926_desc (M : ℕ) :
    A047926_C (9 * M) = A047926_C M +
      ((A047926_sol (9 * M)).filter (fun t => ¬ (3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2))).card := by
  unfold A047926_C
  rw [← card_filter_add_card_filter_not (s := A047926_sol (9 * M))
    (p := fun t => 3 ∣ t.1 ∧ 3 ∣ t.2.1 ∧ 3 ∣ t.2.2)]
  congr 1
  symm
  apply card_bij (fun t _ => (3 * t.1, 3 * t.2.1, 3 * t.2.2))
  · intro t ht
    rw [A047926_sol_mem] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    rw [mem_filter, A047926_sol_mem]
    refine ⟨⟨by simp only; omega, by simp only; omega, by simp only; omega, ?_⟩,
      ⟨t.1, rfl⟩, ⟨t.2.1, rfl⟩, ⟨t.2.2, rfl⟩⟩
    simp only
    rw [← h4]
    ring
  · intro t _ s _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3⟩ := h
    ext <;> omega
  · rintro ⟨a, b, c⟩ h
    rw [mem_filter, A047926_sol_mem] at h
    obtain ⟨⟨h1, h2, h3, h4⟩, ⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := h
    refine ⟨(a', b', c'), ?_, rfl⟩
    rw [A047926_sol_mem]
    simp only at h1 h2 h3 h4 ⊢
    refine ⟨by omega, by omega, by omega, ?_⟩
    nlinarith

theorem A047926_C1 : A047926_C 1 = 0 := by decide

theorem A047926_step (n : ℕ) : A047926_C (9 ^ (n + 1)) = A047926_C (9 ^ n) + A047926_P (n + 1) := by
  unfold A047926_P
  rw [pow_succ, mul_comm, A047926_desc]

/-- Main: the corrected conjecture is equivalent to the primitive count 2P(n+1) = 3^n + 1. -/
theorem A047926_iff :
    (∀ n, A047926_C (9 ^ (n + 1)) = A047926_a n) ↔ (∀ n, 2 * A047926_P (n + 1) = 3 ^ n + 1) := by
  have key : ∀ n, (A047926_C (9 ^ (n + 1)) = A047926_a n) ↔
      4 * A047926_C (9 ^ (n + 1)) + 1 = 3 ^ (n + 1) + 2 * (n + 1) := by
    intro n
    unfold A047926_a
    have h4 : (3 ^ (n + 1) + 2 * n + 1) % 4 = 0 := by
      induction n with
      | zero => norm_num
      | succ k ih =>
        rw [pow_succ]
        omega
    omega
  constructor
  · intro h n
    have hn := (key n).mp (h n)
    have hstep := A047926_step n
    rcases n with _ | m
    · have e0 : A047926_C (9 ^ 0) = 0 := by rw [pow_zero]; exact A047926_C1
      have e1 : (3 : ℕ) ^ (0 + 1) = 3 := by norm_num
      have e2 : (3 : ℕ) ^ 0 = 1 := by norm_num
      omega
    · have hp := (key m).mp (h m)
      rw [show 3 ^ (m + 1 + 1) = 3 * 3 ^ (m + 1) by ring] at hn
      omega
  · intro h n
    rw [key n]
    induction n with
    | zero =>
      have hs := A047926_step 0
      have hp := h 0
      have e0 : A047926_C (9 ^ 0) = 0 := by rw [pow_zero]; exact A047926_C1
      have e1 : (3 : ℕ) ^ (0 + 1) = 3 := by norm_num
      have e2 : (3 : ℕ) ^ 0 = 1 := by norm_num
      omega
    | succ k ih =>
      have hs := A047926_step (k + 1)
      have hp := h (k + 1)
      rw [show 3 ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) by ring]
      omega

theorem A047926_misindexed :
    A047926_C 9 = 1 ∧ A047926_a 1 = 3 ∧ A047926_C 81 = 3 ∧ A047926_C 729 = 8 ∧
      A047926_a 0 = 1 ∧ A047926_a 2 = 8 := by
  refine ⟨?_, by decide, ?_, ?_, by decide, by decide⟩
  · rw [A047926_C, A047926_sol_eq (B := 4) (by norm_num)]
    decide +kernel
  · rw [A047926_C, A047926_sol_eq (B := 10) (by norm_num)]
    decide +kernel
  · rw [A047926_C, A047926_sol_eq (B := 28) (by norm_num)]
    decide +kernel

theorem A047926_P_small : A047926_P 1 = 1 ∧ A047926_P 2 = 2 ∧ A047926_P 3 = 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [A047926_P, A047926_sol_eq (B := 4) (by norm_num)]
    decide +kernel
  · rw [A047926_P, A047926_sol_eq (B := 10) (by norm_num)]
    decide +kernel
  · rw [A047926_P, A047926_sol_eq (B := 28) (by norm_num)]
    decide +kernel
