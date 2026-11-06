# OEIS A068991: squarefree members k divide the denominator of B_{2k}

**Source.** [A068991](https://oeis.org/A068991) (Benoit Cloitre, Apr 06 2002): "Numbers k such that
Sum_{d divides k} sigma(d)/phi(d) is an integer." Comment: "Conjecture: if k is in the sequence and k is
squarefree then the denominator of the 2k-th Bernoulli's number contains k." (OEIS text, CC BY-SA 4.0,
revision #35 of Sep 08 2022, checked 2026-11-06.)

**Reading.** "Contains k" means k divides the denominator of B_{2k} (the entry's example uses A002445(2310),
the denominator of B_{4620}).

**Result.** True.

**Argument.** For squarefree k with prime set P, multiplicativity gives
f(k) = Sum_{d|k} σ(d)/φ(d) = Π_{p∈P} 2p/(p−1) = 2^|P| k / D, with D = Π(p−1). By von Staudt–Clausen, k divides
den(B_{2k}) iff (p−1) | 2k for all p ∈ P. Remove the largest prime M of k, k = k'M. Since M divides neither D(k')
nor M−1, the integer F = f(k) is a multiple of M, and k' is again a member, with precisely
F·h = M·F(k') where M = 2h+1 (M = 2 forces k = 2). Induction on the number of prime factors carries three facts:
(i) (p−1) | 2k for every p | k; (ii) k odd ⇒ F odd; (iii) 4 | F ⇒ (k, F) ∈ {(2, 4), (6, 12), (42, 28)}.
For (i) at M one needs h | k' with h | F(k'): write h = 2^a u, u odd; u | k' because F(k') | 2^n k'; a = 0 if k'
is odd (F(k') odd by (ii)); a ≤ 1 ≤ v2(k') if k' is even and 4 ∤ F(k'); otherwise (iii) leaves three explicit
cases, checked by listing the divisors h of 4, 12, 28 with 2h+1 prime. (ii) and (iii) follow from F·h = M·F(k')
in the same way (in (iii), M = 3 for k' = 2, M = 7 for k' = 6, none for k' = 42).

**Evidence.**
- Lean (Mathlib): [`A068991_mathlib.lean`](A068991_mathlib.lean). Main theorem `A068991_conjecture`: for squarefree
  k with Sum_{d ∈ k.divisors} σ₁(d)/φ(d) (in ℚ) an integer, k ∣ (bernoulli (2k)).den. Also `A068991_closed_form`
  and `A068991_core` (the induction over finite sets of primes, `Finset.induction_on_max`). Uses Mathlib's
  `Bernoulli.dvd_den_bernoulli` (von Staudt–Clausen). Axioms propext, Classical.choice, Quot.sound; no sorry, no
  native_decide, no warnings; checked with `tools/leancheck-mathlib.sh`.
- [`certificate/check.py`](certificate/check.py): members ≤ 20000 from the definition match the OEIS data; all 23
  squarefree ones satisfy (p−1) | 2k.
- Outside Lean: none.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06: OEIS entry (still "Conjecture"), related A099008, web search; no proof found.
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (trees at HEAD 2026-11-06).
