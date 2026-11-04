# OEIS A089758: the prime concatenation chain never stops

**Source.** [A089758](https://oeis.org/A089758) (primes arising in A089757), comment: "Conjecture: Sequence is
infinite." (OEIS text, CC BY-SA 4.0.) A089757: increasing multiples of 3 such that a(n)a(n−1)…a(1)1
(concatenation) is prime; each step takes the least admissible next term.

**Result.** True, by Dirichlet's theorem.

**Argument.** Let C be the current prime concatenation, with L digits. C > 5 is prime, so gcd(C, 30) = 1.
The next term is the least 3y > (last term) with 3y·10^L + C prime. The numbers C + (3·10^L)·y form an
arithmetic progression with gcd(C, 3·10^L) = 1, so it contains infinitely many primes (Dirichlet), and some
y beyond the last term works. Prepending 3y to C is exactly 3y·10^L + C. So every step succeeds and
A089758 is infinite.

**Evidence.**
- `certificate/check.py`: 40 steps of the chain (matches the A089757 data) with gcd(C, 30) = 1 at each step.
- Lean (Mathlib): [`A089758_mathlib.lean`](A089758_mathlib.lean), theorem `A089758_conjecture`: the greedy chain
  (`chain`, decimal concatenation via `Nat.digits`) is the least admissible choice at every step, the
  concatenations are prime and strictly increasing, and the set of these primes is infinite (Dirichlet via
  `Nat.forall_exists_prime_gt_and_modEq`). Nothing outside Lean; that `chain` reproduces the printed terms is
  checked by `certificate/check.py` only.

**Review level.** `lean-proof`.
**Prior art.** New as a statement; a direct consequence of Dirichlet's theorem. [A089758](https://oeis.org/A089758) still has the conjecture. Searched OEIS entry, references and history. Checked 2026-11-04.
