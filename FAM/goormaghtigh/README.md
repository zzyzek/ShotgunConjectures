# Goormaghtigh's equation, exponent pairs (3, 5) and (3, 7) (FAM-goormaghtigh)

## Source

Goormaghtigh conjecture (Wikipedia; formal-conjectures `FormalConjectures/Wikipedia/Goormaghtigh.lean`):
(x^m - 1)/(x - 1) = (y^n - 1)/(y - 1) with x > y > 1, n > m > 2 has only the solutions
31 = 1 + 5 + 25 = 2^5 - 1 and 8191 = 1 + 90 + 90^2 = 2^13 - 1.

## Reading

Convention here (as in the request and Wikipedia): m < n, x > y. Bennett–Garbuz–Marten and others
use the swapped convention (m > n, y > x); results below are translated to this one.

## Result

Lean (`goormaghtigh_mathlib.lean`), all **known** results:
- `goor35`: over ℕ, x^2 + x + 1 = y^4 + y^3 + y^2 + y + 1 only for (x, y) = (0, 0), (5, 2).
- `goor35_repunit`: y ≥ 2 and repunit x 3 = repunit y 5 give x = 5, y = 2 (the number 31).
- `goor37`: x^2 + x + 1 = y^6 + … + y + 1 has no solution with y ≥ 2.
- `goor37_repunit`: the same in repunit form (`repunit` as defined in formal-conjectures).

The smallest pair not settled in the literature found is (m, n) = (4, 6); no result on it here.

## Argument

(3, 5): (2x + 1)^2 = 4y^4 + 4y^3 + 4y^2 + 4y + 1 = R. Then R - (2y^2 + y)^2 = 3y^2 + 4y + 1 > 0
and (2y^2 + y + 1)^2 - R = y(y - 2), positive for y ≥ 3, so 2x + 1 would lie strictly between
consecutive integers. y ≤ 2 leaves x < 40, checked by `decide`.
(3, 7): with R = 4(y^6 + … + 1) - 3 and T = 8y^3 + 4y^2 + 3y,
16R - (T + 2)^2 = 8y^3 + 39y^2 + 52y + 12 > 0 and (T + 3)^2 - 16R = 8y^3 - 31y^2 - 46y - 7 > 0
for y ≥ 6, so 4(2x + 1) lies strictly between T + 2 and T + 3. y ∈ [2, 5] leaves x < 300, checked
by `decide`. (y = 1, x = 2 is the excluded trivial solution 7.) This is Runge's method: for m = 3
and n odd, 4·(y^n - 1)/(y - 1) - 3 has even degree and square leading coefficient.

## Evidence

- `goormaghtigh_mathlib.lean`, checked with `tools/leancheck-mathlib.sh`: OK, zero warnings,
  axioms ⊆ {propext, Classical.choice, Quot.sound}, no sorry, no native_decide.
- `certificate/search46.py`: pair (4, 6), no solution with 2 ≤ y ≤ 10^6 (2.6 s). Not a new
  result (Bennett–Garbuz–Marten Theorem 3 covers both bases ≤ 10^5); evidence for the obstacle log.
- Outside Lean: nothing for the theorems above.

## Review level

lean-proof (known results).

## Prior art (checked 2026-11-05)

- Makowski–Schinzel (Mathesis 68; cited in Bennett–Garbuz–Marten as their Theorem 2): all solutions with larger exponent ≤ 5 (Runge's method),
  so (3, 4), (3, 5), (4, 5) are settled; (3, 5) is the case of 31.
- Yuan (J. Number Theory 112, 2005): m = 3 and n odd; settles (3, 7) and every (3, odd n).
  Le (Trans. AMS 1999, Crelle 2002) and He (Glasnik Mat. 44, 2009): further m = 3 results.
- Nesterenko–Shorey (Acta Arith. 83, 1998), Bugeaud–Shorey: effective when gcd(m - 1, n - 1) > 1.
- Bennett–Gherga–Kreso (Trans. AMS 373, 2020): smaller exponent 3, 4, 5 with gcd(m - 1, n - 1) > 1
  solved completely.
- Bennett–Garbuz–Marten (Publ. Math. Debrecen, 2020), Theorem 4: n = m + 1 with 3 ≤ m ≤ 17;
  gcd(m - 1, n - 1) > 1 with n ≤ 50; (3, 6) and (3, 8). Theorem 6: (n - 1)/(m - 1) = 3 has no
  solutions. Theorem 3: both bases ≤ 10^5.
- Grantham (Integers 24, 2024; arXiv 2410.03677): no new Goormaghtigh primes below 10^700.
- formal-conjectures `Wikipedia/Goormaghtigh.lean`: the conjecture (open, sorry) and tests for
  31, 8191; no fixed-pair theorem.
- ~/claude/openai-math/repo: no Goormaghtigh or repunit item.
- Status of small pairs (larger exponent ≤ 8), from the sources above: settled are (3,4), (3,5),
  (4,5), (3,6), (5,6), (3,7), (4,7), (5,7), (6,7), (3,8), (7,8). Not settled: (4,6),
  (4,8), (5,8), (6,8) (gcd(m - 1, n - 1) = 1, not consecutive, m ≠ 3). Search done with web
  search only; a later paper settling (4,6) could have been missed.

## Obstacles

(4, 6): x^3 + x^2 + x = y^5 + y^4 + y^3 + y^2 + y.
- Runge (natural route): the top-weight form x^3 - y^5 is irreducible, so the curve has one place
  at infinity and Runge's condition fails; no squeeze between consecutive polynomial values.
- Modular obstruction (alternative): none exists, since x ≡ y ≡ 0 solves the equation modulo
  every N.
- What would work: the curve has genus at most 4 (4 interior points of its Newton triangle); Chabauty-type methods on the
  Jacobian or Baker bounds plus reduction. Neither is in Mathlib.
