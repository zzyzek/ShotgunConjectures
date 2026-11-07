# Lemmas duplicated across problem files (candidates for the library)

Found 2026-11-06 during the library promotion pass; not yet moved.

- Dwork library copies (`LD_*`, `expCoeff_int_of_euler`, `dwork`, `LGp_*`): OEIS/A158110, A174470, A207969, A208034 (library: Dwork.lean).
- Twin-prime sieve block (`pairRho_*`, `pairSieve_*`): FAM/twin-primes, OEIS/A187011, A215462.
- About 45 lemmas shared by OEIS/A227370 and A227786.
- OEIS/A166103 and A166272.
- OEIS/A078128, A078130, A078537.
- `hohnK_*`: OEIS/A188644-A188646.
- OEIS/A134002 and A134003.
- `dvd_iff_zmod`: OEIS/A097406, A226661.
- `not_sq_dvd`: OEIS/A182206, A182515.
- `primeCounting_div_tendsto_zero`: OEIS/A102613, A139043.
- `cover_orders` / `pow_period`: COM/C125, OEIS/A101462.
- `powMod_eq` / `pow_period`: about 81 core-only COM files (library: PowMod.lean).

Added 2026-11-07 (round r17 candidates):
- Base-10 digits: `A077739_ds_add` (digit sum of a + 10^m b), `A077739_pow_period` (powers of 10 repeat mod n), A084043 repunit helpers `rp`, `rep`, `rep_mul`, `dvd_rep`. Candidate module Digits10.lean.
- `exists_nonsq`, `sum_squares_zero` (ZMod p) in OEIS/A176948.
- `descFactorial_mono` in OEIS/A096123.

Library issues noted while writing lib/docs (2026-11-07):
- ArithFactor: no unitary-divisor-sum function; `unitary_val` proves one direction only; header says "all three" but lists four results.
- ModularSums imports all of Mathlib; `miss` needs `R : Type`.
- R5_Quadratic: name does not describe the content (quadratic-field discriminants).
- Korselt: `carmichaelCheck` used only in lib/test.
- ShevelevFactorial `shevelev_row`: congruence for any integer equal to the row sum; integrality of the row sum is not proved.
- DworkEuler `rowB_int`: covers H = 1/(1 - tF) with F a polynomial, not the general bivariate lemma.
- QSeries `qGaussSum_mul`: only the family a = q, rho1 = q, rho2 = -1.
- BernoulliDen `vscSet 0` is empty (harmless).
