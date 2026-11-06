/-
OEIS A058347: T(n,k), total number of checks of the "double-support" algorithm over all
n x k zero-one matrices. Conjecture (entry text): T(n,k) = T(k,n).

Definition (the entry's formula, from van Dongen's report): T(0,k) = T(n,0) = 0 and
  T(n,k) = (2^(k+1) - 2) 2^((n-1)k) + 2^((n-1)(k-1)) ((k-2) 2^k + 2)
           + (n-1)(2^k - 1) 2^((n-2)k+1) + T(n-1,k) + 2^(n-1) (2^k - 1) T(n-1,k-1)
for n, k > 0; below with n, k replaced by n+1, k+1. Over ℤ because (k-2) can be negative.

Main theorem.
* `A058347_symm`: T n k = T k n for all n, k.
* `T_data`: T(2,2) = 54, T(2,3) = 302, T(3,3) = 3094 (OEIS data), by `rfl`.

Route.
* `S` is defined by S(n,0) = S(0,k) = 0 and
  S(n+1,k+1) = S(n,k+1) + (2^(k+1) - 1) (2^(n(k+1)) + 2^n S(n,k)).
  (S(n,k) is the sum of the GF(2)-ranks of all n x k matrices: condition on the first row;
  this interpretation is explained in the README and is not used in the proof.)
* `S_col`: S also satisfies the column recurrence; `S_symm`: S n k = S k n.
* `C n k = 2^(nk)(2n + 2k) - n 2^((n-1)k+1) - k 2^(n(k-1)+1)`, symmetric (`C_symm`).
* `T_eq`: T n k = C n k - 2 S n k.

Not checked in this file: agreement with the other OEIS data terms (certificate/check.py) and the
derivation of the recurrence from the algorithm (taken from the entry).
-/
import Mathlib

namespace A058347

def T : ℕ → ℕ → ℤ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      (2 ^ (k + 2) - 2) * 2 ^ (n * (k + 1)) + 2 ^ (n * k) * (((k : ℤ) + 1 - 2) * 2 ^ (k + 1) + 2)
        + (n : ℤ) * (2 ^ (k + 1) - 1) * 2 ^ ((n - 1) * (k + 1) + 1)
        + T n (k + 1) + 2 ^ n * (2 ^ (k + 1) - 1) * T n k

def S : ℕ → ℕ → ℤ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => S n (k + 1) + (2 ^ (k + 1) - 1) * (2 ^ (n * (k + 1)) + 2 ^ n * S n k)

def C : ℕ → ℕ → ℤ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      2 ^ ((n + 1) * (k + 1)) * (2 * ((n : ℤ) + 1) + 2 * ((k : ℤ) + 1))
        - ((n : ℤ) + 1) * 2 ^ (n * (k + 1) + 1) - ((k : ℤ) + 1) * 2 ^ ((n + 1) * k + 1)

theorem S_zero_right (n : ℕ) : S n 0 = 0 := by
  cases n <;> rfl

theorem S_succ (n k : ℕ) :
    S (n + 1) (k + 1) = S n (k + 1) + (2 ^ (k + 1) - 1) * (2 ^ (n * (k + 1)) + 2 ^ n * S n k) := rfl

theorem S_one_left (k : ℕ) : S 1 k = 2 ^ k - 1 := by
  cases k with
  | zero => rfl
  | succ k => simp [S]

theorem S_one_right (n : ℕ) : S n 1 = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [S_succ, ih, S_zero_right]
    ring

theorem S_col (n : ℕ) : ∀ k : ℕ,
    S (n + 1) (k + 1) = S (n + 1) k + (2 ^ (n + 1) - 1) * (2 ^ ((n + 1) * k) + 2 ^ k * S n k) := by
  induction n with
  | zero =>
    intro k
    rw [S_one_left, S_one_left]
    simp [S]
    ring
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      rw [S_one_right, S_zero_right, S_zero_right]
      ring
    | succ k =>
      have r1 := S_succ (n + 1) (k + 1)
      have c1 := ih (k + 1)
      have r2 := S_succ (n + 1) k
      have rX := S_succ n k
      have cX := ih k
      have e1 : (2 : ℤ) ^ ((n + 1) * (k + 1 + 1)) = 2 ^ (n * k) * 2 ^ n * 2 ^ n * 2 ^ k * 2 ^ 2 := by
        rw [show (n + 1) * (k + 1 + 1) = n * k + n + n + k + 2 by ring]; simp only [pow_add]
      have e2 : (2 : ℤ) ^ ((n + 1) * (k + 1)) = 2 ^ (n * k) * 2 ^ n * 2 ^ k * 2 := by
        rw [show (n + 1) * (k + 1) = n * k + n + k + 1 by ring]; simp only [pow_add, pow_one]
      have e3 : (2 : ℤ) ^ ((n + 1 + 1) * (k + 1)) = 2 ^ (n * k) * 2 ^ n * 2 ^ k * 2 ^ k * 2 ^ 2 := by
        rw [show (n + 1 + 1) * (k + 1) = n * k + n + k + k + 2 by ring]; simp only [pow_add]
      have e4 : (2 : ℤ) ^ (n * (k + 1)) = 2 ^ (n * k) * 2 ^ n := by
        rw [show n * (k + 1) = n * k + n by ring, pow_add]
      have e5 : (2 : ℤ) ^ ((n + 1) * k) = 2 ^ (n * k) * 2 ^ k := by
        rw [show (n + 1) * k = n * k + k by ring, pow_add]
      rw [e1] at r1; rw [e2] at c1 r2; rw [e4] at rX; rw [e5] at cX; rw [e3]
      linear_combination r1 + c1 - r2 + (2 * 2 ^ k - 4 * 2 ^ n * 2 ^ k) * rX
        + (4 * 2 ^ n * 2 ^ k - 2 * 2 ^ n) * cX

theorem S_symm : ∀ n k : ℕ, S n k = S k n := by
  intro n k
  induction h : n + k using Nat.strong_induction_on generalizing n k with
  | _ s ih =>
    cases n with
    | zero =>
      cases k with
      | zero => rfl
      | succ k => simp [S]
    | succ n =>
      cases k with
      | zero => simp [S]
      | succ k =>
        rw [S_succ, S_col k n]
        have h1 : S n (k + 1) = S (k + 1) n := ih (n + k + 1) (by omega) n (k + 1) rfl
        have h2 : S n k = S k n := ih (n + k) (by omega) n k rfl
        rw [h1, h2]
        ring

theorem C_symm (n k : ℕ) : C n k = C k n := by
  cases n with
  | zero => cases k <;> rfl
  | succ n =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [C]
      rw [show (k + 1) * (n + 1) = (n + 1) * (k + 1) by ring,
        show k * (n + 1) = (n + 1) * k by ring, show (k + 1) * n = n * (k + 1) by ring]
      ring

theorem T_eq (n : ℕ) : ∀ k : ℕ, T n k = C n k - 2 * S n k := by
  induction n with
  | zero => intro k; simp [T, C, S]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [T, C, S]
    | succ k =>
      have hT : T (n + 1) (k + 1) =
          (2 ^ (k + 2) - 2) * 2 ^ (n * (k + 1)) + 2 ^ (n * k) * (((k : ℤ) + 1 - 2) * 2 ^ (k + 1) + 2)
            + (n : ℤ) * (2 ^ (k + 1) - 1) * 2 ^ ((n - 1) * (k + 1) + 1)
            + T n (k + 1) + 2 ^ n * (2 ^ (k + 1) - 1) * T n k := rfl
      rw [hT, ih (k + 1), ih k, S_succ]
      cases n with
      | zero =>
        cases k with
        | zero => simp [C, S]
        | succ k => simp [C, S]; ring
      | succ n =>
        cases k with
        | zero =>
          simp only [C, S_zero_right]
          rw [S_one_right, show n + 1 - 1 = n by omega]
          push_cast
          ring_nf
        | succ k =>
          simp only [C]
          rw [show n + 1 - 1 = n by omega]
          push_cast
          ring_nf

theorem A058347_symm (n k : ℕ) : T n k = T k n := by
  rw [T_eq, T_eq, C_symm, S_symm]


/-- Spot checks against the OEIS data: T(2,2) = 54, T(2,3) = 302, T(3,3) = 3094. -/
theorem T_data : T 2 2 = 54 ∧ T 2 3 = 302 ∧ T 3 3 = 3094 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl
