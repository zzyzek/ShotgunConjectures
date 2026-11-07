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
