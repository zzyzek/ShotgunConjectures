# Coman C003: (n^(nk+k+n-1) - 1)/(n^2 - 1) is a base-n psp for infinitely many k

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 3. Paraphrase: For every integer n > 1 the expression (n^(nk+k+n-1) - 1)/(n^2 - 1) is a Fermat pseudoprime to base n for infinitely many k.

**Result.** True.

**Argument.** nk + k + n - 1 = (n+1)(k+1) - 2. Take a prime p with p = -1 (mod n+1), p not dividing n(n^2 - 1), and
k = 2(p+1)/(n+1) - 1 (a positive integer once p > n). Then the exponent is 2p and the number is
N = (n^(2p) - 1)/(n^2 - 1). Cipolla (1904): for a prime p not dividing n(n^2 - 1), N is composite
(N = ((n^p - 1)/(n - 1)) * ((n^p + 1)/(n + 1))) and n^(N-1) = 1 (mod N). Dirichlet gives infinitely many
such p (only the residue -1 mod n+1 is needed).

**Evidence.**
- Lean (Mathlib): [`C003_mathlib.lean`](C003_mathlib.lean) proves the full result (`C003_main`): for every n > 1 the set of k with (n^(nk+k+n-1) - 1)/(n^2 - 1) a base-n Fermat pseudoprime (`Nat.FermatPsp`) is infinite; Dirichlet (Mathlib `Nat.forall_exists_prime_gt_and_modEq`) + Cipolla (library `cipolla`). Outside Lean: none (this closes the steps the core-Lean file leaves outside Lean).
- Lean: [`C003.lean`](C003.lean) checks the exponent identity and three instances (n, k) = (2, 3), (3, 2), (5, 3). Core Lean, no Mathlib, no `native_decide`.
- Outside the core-Lean file (proved in the Mathlib file): Cipolla's theorem (uses Fermat's little theorem) and Dirichlet's theorem for p = -1 (mod n+1).
- `certificate/check.py` (standard-library Python, reads [`data/psp2-annot-below-1e13.txt`](../../DATA.md) where needed): numerical check of the construction for n = 2..11, p < 400; output in `certificate/check.log`.

**Review level.** `lean-proof`: the full result is proved in Lean + Mathlib ([`C003_mathlib.lean`](C003_mathlib.lean), axioms `propext`, `Classical.choice`, `Quot.sound`); the core-Lean file [`C003.lean`](C003.lean) checks the parts named under Evidence. Also recomputed on the complete table below 10^21.

**Prior art.** Verdict `known` (immediate). With exponent 2p the number is exactly Cipolla's (n^(2p)-1)/(n^2-1); the answer is Cipolla 1904 plus Dirichlet for p = -1 (mod n+1). Sources: M. Cipolla, Sui numeri composti P che verificano la congruenza di Fermat, Annali di Matematica (3) 9 (1904) 139-160: (a^(2p)-1)/(a^2-1) is a base-a psp for primes p not dividing a(a^2-1). Searched: Coman's OEIS entries (all 60), web searches on the book and the statement, Cipolla pseudoprime literature (2026-11-04).
