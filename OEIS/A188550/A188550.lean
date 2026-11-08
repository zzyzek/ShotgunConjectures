/-
OEIS A188550: a(n) = max over k = 2 .. floor(sqrt n) of the number of
divisors d > 1 of n - k with k | n - d.
Conjecture (Shevelev, Apr 10 2011): if k runs through 2 .. floor((n-2)/2)
instead, the sequence is unchanged from n = 6 on.
False at n = 208: a(208) = 4, but k = 16 (16 <= 103 = (208-2)/2) gives
the six divisors 16, 32, 48, 64, 96, 192 of 192 = 208 - 16.

Checked here: the definitions below (sqrt range written as k * k <= n)
and the values a 208 = 4, cnt 208 16 = 6, aExt 208 = 6, by kernel evaluation.
Also checked: Shevelev's further conjectures (Jan 21 2013) 1) "a(p) = 1 only
for the primes 5, 7, 13" and 2) "a(p) = 2 only for the primes 11, 19" fail
at p = 61 (a 61 = 1) and p = 1321 (a 1321 = 2). Primality of 61 and 1321
is checked by trial division (`isPrimeTD`).
Not checked here: nothing beyond reading the OEIS definition.
-/

/-- Number of d in [2, n - k] with d | n - k and k | n - d. -/
def cnt (n k : Nat) : Nat :=
  ((List.range (n - k + 1)).filter
    (fun d => 2 ≤ d && (n - k) % d == 0 && (n - d) % k == 0)).length

/-- Maximum of `cnt n k` over k in [2, n] with `ok k`. -/
def maxOver (n : Nat) (ok : Nat → Bool) : Nat :=
  ((List.range (n + 1)).filter (fun k => 2 ≤ k && ok k)).foldl
    (fun m k => max m (cnt n k)) 0

/-- A188550: k from 2 to floor(sqrt n). -/
def a (n : Nat) : Nat := maxOver n (fun k => k * k ≤ n)

/-- Shevelev's variant: k from 2 to floor((n - 2)/2). -/
def aExt (n : Nat) : Nat := maxOver n (fun k => k ≤ (n - 2) / 2)

theorem a_208 : a 208 = 4 := by decide
theorem cnt_208_16 : cnt 208 16 = 6 := by decide
set_option maxRecDepth 8000 in
theorem aExt_208 : aExt 208 = 6 := by decide

theorem A188550_conjecture_false : ¬ (∀ n, 6 ≤ n → aExt n = a n) := by
  intro h
  have h1 := h 208 (by decide)
  rw [a_208, aExt_208] at h1
  exact absurd h1 (by decide)

/-- Trial-division primality test. -/
def isPrimeTD (p : Nat) : Bool :=
  2 ≤ p && (List.range p).all (fun d => d < 2 || p % d != 0)

theorem prime_61 : isPrimeTD 61 = true := by decide
theorem a_61 : a 61 = 1 := by decide

set_option maxRecDepth 20000 in
theorem prime_1321 : isPrimeTD 1321 = true := by decide

set_option maxRecDepth 20000 in
theorem a_1321 : a 1321 = 2 := by decide
