/-
OEIS A133212: a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) for n > 3, a(0..3) = 1, 4, 12, 32.
Conjecture (Mathar 2007): a(n) = 2*A038503(n+3) for n > 0, where
A038503(m) = sum_k C(m, 4k).

Argument (C-finite, METHODS §6). A038503(m) = (2^m + (1+i)^m + (1-i)^m + 0^m)/4,
so for m ≥ 1 it is annihilated by (x-2)(x^2-2x+2) = x^3 - 4x^2 + 6x - 4, i.e.
b(m) = 4b(m-1) - 6b(m-2) + 4b(m-3) for m ≥ 4. Both sides of the conjecture
satisfy the same order-3 recurrence for n ≥ 2 (a from n ≥ 4, b(n+3) from
n ≥ 2), so agreement at n = 1, 2, 3 proves it for all n ≥ 1.

Checked here (core Lean, `decide`): agreement for 1 ≤ n ≤ 40 (n = 1, 2, 3 suffice).
Not checked here: the order-3 recurrence for A038503 (roots-of-unity filter
of (1+x)^m), which is the step that turns the finite check into a proof.
-/

def a : Nat → Int
  | 0 => 1 | 1 => 4 | 2 => 12 | 3 => 32
  | n + 4 => 4 * a (n + 3) - 6 * a (n + 2) + 4 * a (n + 1)

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

def b (m : Nat) : Int := ((List.range (m / 4 + 1)).map (fun k => (choose m (4 * k) : Int))).foldl (· + ·) 0

theorem base : (List.range 3).all (fun i => a (i + 1) == 2 * b (i + 4)) = true := by decide
theorem upto40 : (List.range 40).all (fun i => a (i + 1) == 2 * b (i + 4)) = true := by decide
theorem n0_excluded : a 0 ≠ 2 * b 3 := by decide
