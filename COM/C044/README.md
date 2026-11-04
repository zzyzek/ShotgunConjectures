# Coman C044: Carmichael numbers (30a+1)(30b+1)(30c+11) do exist

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 44. Paraphrase: Every Carmichael number = 1 (mod 10) with all prime factors = 1 (mod 10) (with any number of prime factors) is (30a+1)(30b+1)(30c+1), (30a+11)(30b+11)(30c+11) or (30a+1)(30b+11)(30c+11); in particular none is (30a+1)(30b+1)(30c+11).

**Reading.** The statement explicitly covers Carmichael numbers with more than three prime factors, so the three
factors are products of primes. If the factors had to be prime the claim would be true: a prime factor
= 1 (mod 30) forces C = 1 (mod 3), while (1)(1)(11) = 2 (mod 3).

**Result.** False as stated: 1044430736441 = 41 * 191 * 281 * 521 * 911 = (41*191)(281*521)(911) = 7831 * 146401 * 911, residues 1, 1, 11 mod 30.

**Argument.** All five primes are 11 mod 30 and 11^2 = 1 (mod 30). Below 1e13 there are 30 Carmichael numbers = 11 (mod 30)
with all prime factors = 1 (mod 10); all their prime factors are 11 mod 30; the 3-factor ones (e.g. 1909001)
fit (1)(1)(11) only with a = 0, the 5-factor ones (1044430736441, 1894509409001, 3558903712001) with
a, b >= 1.

**Evidence.**
- Lean (Mathlib): [`C044_mathlib.lean`](C044_mathlib.lean) proves the full result (`C044_false`): 1044430736441 is Carmichael, = 1 (mod 10), all prime factors = 1 (mod 10), and = (30a+1)(30b+1)(30c+11); Korselt's criterion via Mathlib `Nat.isCarmichael_iff_korselt`, primes by Pratt certificates (lib/OpenProblemsLib). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C044.lean`](C044.lean) checks factor primality, Korselt data, the grouping and residues. Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Korselt's criterion (squarefree n with p - 1 | n - 1 for every prime p | n is Carmichael).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): search of the Feitsma-Galway list; output in `certificate/check.log`.

**Second reader: disputed.** The scan calls it trivial (true) using a prime-factor reading; the statement explicitly allows more than three prime factors, and then 1044430736441 = 7831 * 146401 * 911 is a counterexample.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C044_mathlib.lean`](C044_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C044.lean`](C044.lean) checks the parts named under Evidence.

**Prior art.** Verdict `new`. Counterexample not found stated; it sits in the entry's own b-file. Sources: [OEIS A212843 (fetched 2026-11-04)](https://oeis.org/A212843): still states 'there are no numbers of the form (30a+1)(30b+1)(30c+11)'; our counterexample 1044430736441 is a(848) in its b-file but not flagged. Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, OEIS A212843 and b-file (2026-11-04).
