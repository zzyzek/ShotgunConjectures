/-
NT-F6.2 (Guy, UPINT 3rd ed., F6): Q(1,6,7) = ∞, and likewise for the other
four-element subpatterns (1,6,10), (1,7,10), (5,6,9), (6,7,10) of
{0,1,6,7,10}: for every R, infinitely many primes p have no r ≤ R with
r, r+a, r+b, r+c all quadratic residues mod p.

Checked here (core Lean, no Mathlib): the finite obstructions.
* `chi4_016_7`, `chi4_0_1_7_10`: for every r ≥ 1 the pattern contains two
  odd numbers differing by 2 mod 4, hence an odd number ≡ 3 (mod 4).
  With f(n) = χ₋₄(odd part of n), that element has f = −1.
* `leg_*`: for the stated prime q, every translate t + pattern (mod q)
  contains a nonzero quadratic non-residue class mod q.
Not checked here: the transfer to primes p.  For any completely
multiplicative f : ℕ → {±1}, quadratic reciprocity plus Dirichlet's theorem
give infinitely many primes p with (ℓ/p) = f(ℓ) for all primes ℓ ≤ R + 10,
hence (n/p) = f(n) for n ≤ R + 10 (needs Mathlib).
-/

theorem chi4_0_1_6_7 (r : Nat) :
    (r % 2 = 1 ∧ (r % 4 = 3 ∨ (r + 6) % 4 = 3)) ∨
    (r % 2 = 0 ∧ ((r + 1) % 4 = 3 ∨ (r + 7) % 4 = 3)) := by omega

theorem chi4_0_1_7_10 (r : Nat) :
    (r % 2 = 1 ∧ (r % 4 = 3 ∨ (r + 10) % 4 = 3)) ∨
    (r % 2 = 0 ∧ ((r + 1) % 4 = 3 ∨ (r + 7) % 4 = 3)) := by omega

def isNR (q c : Nat) : Bool := c != 0 && (List.range q).all (fun x => x * x % q != c)

def blocked (q : Nat) (pat : List Nat) : Bool :=
  (List.range q).all (fun t => pat.any (fun s => isNR q ((t + s) % q)))

theorem leg_0_1_6_7 : blocked 11 [0, 1, 6, 7] = true ∧ blocked 17 [0, 1, 6, 7] = true := by decide
theorem leg_0_1_6_10 : blocked 11 [0, 1, 6, 10] = true ∧ blocked 19 [0, 1, 6, 10] = true := by decide
theorem leg_0_5_6_9 : blocked 11 [0, 5, 6, 9] = true ∧ blocked 17 [0, 5, 6, 9] = true ∧
    blocked 31 [0, 5, 6, 9] = true := by decide
theorem leg_0_6_7_10 : blocked 19 [0, 6, 7, 10] = true := by decide
theorem no_leg_0_1_7_10 : ∀ q ∈ [3, 5, 7, 11, 13, 17, 19, 23, 29, 31], blocked q [0, 1, 7, 10] = false := by
  decide
