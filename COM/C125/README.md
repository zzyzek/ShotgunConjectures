# Coman C125: 5p + 2^n is not always prime infinitely often

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on
Fermat Pseudoprimes* (2013), Part one, conjecture 125. Paraphrase: for every odd prime
p ≠ 5 there are infinitely many n such that 5p + 2^n is prime.

**Result.** False. For the prime p = 76739471787787, 5p + 2^n is composite for every n ≥ 0.

**Argument.** Covering congruences. The nine primes q = 3, 7, 13, 17, 19, 37, 73, 109, 241
have ord_q(2) dividing 72, and p was chosen by the Chinese remainder theorem so that
q | 5p + 2^n on one class of n mod ord_q(2); the classes cover every residue mod 72.
Since 5p + 2^n > 241, each value has a proper factor.

**Evidence.**
- Lean: [`C125.lean`](C125.lean) proves, for every n, that some q in the set divides
  5p + 2^n with 1 < q < 5p + 2^n (core Lean, axioms propext and Quot.sound).
- Lean + Mathlib: [`C125_mathlib.lean`](C125_mathlib.lean), `C125_main`: `Nat.Prime 76739471787787` (Pratt
  certificate, `prime_of_prattCertifies`) and 5p + 2^n is not prime for every n (covering restated);
  `C125_conjecture_false` negates the conjecture with `Set.Infinite`. Outside Lean: nothing.
- `certificate/cover.py`: the search that found p.

**Review level.** `lean-proof`: primality of p and compositeness of every 5p + 2^n, both in [`C125_mathlib.lean`](C125_mathlib.lean).
**Prior art.** Verdict `partly-known`. Covering congruences for k + 2^n are Erdos 1950; the twist (k = 5p, p prime, covering avoiding 5) and the explicit prime 76739471787787 were not found anywhere. Sources: [P. Erdos, On integers of the form 2^k + p and some related problems, Summa Brasil. Math. 2 (1950) 113-123; construction as in C. Pomerance, covering-congruence talk slides](https://math.dartmouth.edu/~carlp/PDF/covertalkunder.pdf): covering congruences give residue classes of odd k with k + 2^n composite for all n; not for 5p with p prime. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, Google: '76739471787787', Google: 5p+2^n composite covering, Google: dual Sierpinski / k+2^n composite for all n (2026-11-04).
