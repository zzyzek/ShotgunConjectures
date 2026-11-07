# Guides to the methods in `lib/OpenProblemsLib`

Each guide states the method, says when it applies, gives a paper proof, works one repo problem
end to end, and lists the Lean declarations and the problems that use them.

| guide | modules | what the method is for |
|---|---|---|
| [certificates.md](certificates.md) | PowMod, Pratt, Fermat, Korselt, Cipolla | turning a number-theoretic witness (factorization, base, primality certificate) into a kernel check: pseudoprimes, Carmichael numbers, primes, Cipolla's infinite families |
| [arith-factor.md](arith-factor.md) | ArithFactor | evaluating σ, d, φ of a large number from its prime-power list, and enumerating its unitary divisors as sub-products |
| [modular-sums.md](modular-sums.md) | ModularSums | upper bounds on the torus ℤ/n × ℤ/n: $n - 1$ objects under injective coordinate maps miss one residue each, then sums and sums of squares give a contradiction (Monsky's modular queens) |
| [dwork.md](dwork.md) | Dwork, DworkLocal, DworkLocalPoly, DworkEuler, DworkMultinomial | proving that $\exp\bigl(\sum b(n) x^n / n\bigr)$ is an integer series, via Gauss congruences and Euler products (Dwork's lemma), globally or one prime at a time |
| [shevelev-factorial.md](shevelev-factorial.md) | ShevelevFactorial | $p$-integrality of iterated power-sum polynomials (Shevelev's generalized factorials), from von Staudt–Clausen for power sums |
| [qseries.md](qseries.md) | QSeries | q-series identities: Gaussian binomials, q-Pascal rules and the Jacobi triple product |
| [bernoulli-den.md](bernoulli-den.md) | BernoulliDen | the denominator of $B_{2k}$ as the product of primes $p$ with $p - 1 \mid 2k$ (von Staudt–Clausen) and its consequences |
| [short-interval-primes.md](short-interval-primes.md) | ShortIntervalPrimes | a prime in $(x, 1.21x]$ for every real $x \ge 25$ (Chebyshev's 1852 bounds on $\psi$ plus 85 certified primes): inductions that add one prime at a time, consecutive-prime ratios |
| [misc.md](misc.md) | R5_Quadratic | the discriminant of $\mathbb Q(\sqrt d)$: $d$ or $4d$, via the ring of integers |
| [misc.md](misc.md) | SquaredRect | exact tilings of a rectangle by squares in $\mathbb R^2$ from a column-cover certificate |
| [misc.md](misc.md) | D_CombLine | collinear $k$-subsets of $\{0,\dots,k-1\}^n$ are combinatorial lines; there are $((k+2)^n - k^n)/2$ of them |
| [misc.md](misc.md) | Digits10 | multiples of $n$ with a prescribed decimal pattern: digit sums of concatenated blocks, periodic powers of 10, base-$10^L$ repunits divisible by $m$ |
| [misc.md](misc.md) | Misc | monotonicity of descending factorials; a non-square value $a(bx^2 - C)$ mod a prime $p > 3$ |

Import a single module with `import OpenProblemsLib.<Module>` or the whole library with
`import OpenProblemsLib`. Problem files are checked with `tools/leancheck-mathlib.sh` after
`tools/buildlib.sh` has compiled `lib/`.
