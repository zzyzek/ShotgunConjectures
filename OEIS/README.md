# OEIS conjectures

Conjecture comments in the On-Line Encyclopedia of Integer Sequences (list: OEIS wiki, Talk:Conjectures/List). OEIS text is quoted under CC BY-SA 4.0 with the A-number as attribution.

184 entries: 141 resolved by this project, 40 answered elsewhere, 2 disputed or partial.

Of the 141 resolutions: 132 proved in full in Lean, 4 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 5 on paper only (re-derived by a second reader; 2 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A000040](A000040/) | trivial or misstated | prime(n) = (6f + (-1)^f - 3)/2 with f = floor(prime(n)/3) + 1 | [full proof](A000040/A000040.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md) |
| [A000120](A000120/) | trivial or misstated | columns of the base-b digit-sum triangle are constant | [full proof](A000120/A000120.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md) |
| [A004050](A004050/) | proved | only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways | [witness](A004050/A004050_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A005329](A005329/) | proved | Product (2^i − 1) is the inverse binomial transform of A075272 | [full proof](A005329/A005329_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A005408](A005408/) | proved | one-coach primes and the first q odd numbers | [full proof](A005408/A005408_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A005430](A005430/) | proved | the inverse binomial transform of n·C(2n,n) is 2·A132894(n) | [full proof](A005430/A005430_mathlib.lean) | partly-known | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A008578](A008578/) | proved | 1 and the primes are exactly the k with sigma(k) > k·Omega(k) | [full proof](A008578/A008578_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A008676](A008676/) | proved | coefficients of 1/((1-x^3)(1-x^5)) as a floor formula | [full proof](A008676/A008676_mathlib.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A023402](A023402/) | disproved | T(n,3) and A023402 differ at n = 4 | [full proof](A023402/A023402_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A024187](A024187/) | proved | e\_n(3, 4, ..., n+3) is A001711 | [full proof](A024187/A024187_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A025060](A025060/) | trivial or misstated | with signs allowed, i·j + j·k + k·i takes every integer | [full proof](A025060/A025060.lean) | new (immediate) | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A025191](A025191/) | proved | row half-sums of A025177 are first differences of A027914 and of A081673/2 | [full proof](A025191/A025191_mathlib.lean) | new (immediate) | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A026002](A026002/) | proved | Bergot's array with borders n(n−1)+1 has diagonal A026002 | [full proof](A026002/A026002_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A029795](A029795/) | disproved | k and k^3 with the same digits are not eventually all integers | [full proof](A029795/A029795_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A047926](A047926/) | trivial or misstated | sorted three-square representations of 3^(2n) (misindexed; reduced to r\_3(9^n)) | [full proof](A047926/A047926_mathlib.lean) | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A051451](A051451/) | disproved | the "next twin pair above a(n)" form fails at n = 35 | [full proof](A051451/A051451_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A051924](A051924/) | disproved | a(n) ≡ n + 2 (mod n^2) also holds at n = 16843^2 | [full proof](A051924/A051924_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A054120b](A054120b/) | proved | T(n,k) = A081577(n,k) − A081577(n−2,k−1) | [full proof](A054120b/A054120b_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md) |
| [A061002](A061002/) | proved | denominator(H(p)/H(p−1)) / numerator(H(p−1)/p^2) = p^3 | [full proof](A061002/A061002_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A072901](A072901/) | trivial or misstated | composites with disc Q(√n) = 4n are squarefree | [full proof](A072901/A072901_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A074766](A074766/) | proved | p(2n) − 2p(n) < 2n for all n | needs Mathlib | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A079665](A079665/) | trivial or misstated | when is (b^s + 1)/(b^r + 1) an integer | [full proof](A079665/A079665_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A080674](A080674/) | proved | counting integers below 10^n with digits only in {6,7,8,9} | [full proof](A080674/A080674_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A081199](A081199/) | proved | collinear 4-tuples in the 4^n grid | [full proof](A081199/A081199_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081200](A081200/) | proved | collinear 5-tuples in the 5^n grid | [full proof](A081200/A081200_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081201](A081201/) | proved | collinear 6-tuples in the 6^n grid | [full proof](A081201/A081201_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081320](A081320/) | proved | 3-smooth part of Fibonacci numbers | [full proof](A081320/A081320_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081532](A081532/) | disproved | T(n,3) and A023402 differ at n = 4 | [full proof](A081532/A081532_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A083219](A083219/) | proved | roots of x^n - x^(n-1) - ... - 1 in the left half-plane | [full proof](A129756/A129756_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A083452](A083452/) | trivial or misstated | n written n times exceeds n^n | [full proof](A083452/A083452.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A087324](A087324/) | disproved | no term has a perfect-square prime signature | [full proof](A087324/A087324_mathlib.lean) | partly-known | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A088104](A088104/) | proved | an n-digit prime beginning with prime(n) always exists | needs Mathlib | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A088120](A088120/) | disproved | the common difference is 2 at n = 12 | [full proof](A088120/A088120_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A088226](A088226/) | corrected-and-proved | a(n) = \|a(n-1) − a(n-2) − a(n-3)\| is half the smallest even distance from n − 1 to a square | [full proof](A088226/A088226_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A088276](A088276/) | disproved | 10^k + 9351 is never prime, though 9351 ≡ 0 (mod 3) | [full proof](A088276/A088276_mathlib.lean) | known | [covering-congruences](../methods/covering-congruences/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A088617](A088617/) | proved | mean number of U steps in a Schröder n-path is ~ n/√2 | [checked](A088617/A088617_mathlib.lean) | new (immediate) | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A089758](A089758/) | proved | the prime concatenation chain never stops | [full proof](A089758/A089758_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A090519](A090519/) | proved | some prime p has floor(10^n/p) prime | [full proof](A090519/A090519_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A094787](A094787/) | proved | every prime is a least prime p with p + n a perfect power | [full proof](A094787/A094787_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [parametric-family](../methods/parametric-family/README.md) |
| [A097406](A097406/) | trivial or misstated | primitive prime factors of 2^n − 1 are ≡ 1 (mod n) | [full proof](A097406/A097406_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A098016](A098016/) | trivial or misstated | the mean of consecutive primes is never prime | [full proof](A098016/A098016_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A100056](A100056/) | disproved | the A054065 permutations do not maximize the sum of differences | [full proof](A100056/A100056_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A100682](A100682/) | disproved | exception list of Greathouse's formula is incomplete | [full proof](A100682/A100682_mathlib.lean) | new | [exact-arithmetic](../methods/exact-arithmetic/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A101312](A101312/) | trivial or misstated | other weekday/day pairs do not give a shifted Friday-13th sequence | — | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A101462](A101462/) | disproved | 2^k − 509203 is never prime, so a(42228) does not exist | [full proof](A101462/A101462_mathlib.lean) | known | [covering-congruences](../methods/covering-congruences/README.md) |
| [A102613](A102613/) | trivial or misstated | π(n)/(n − π(n)) → 0 | [full proof](A102613/A102613_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md) |
| [A104895](A104895/) | proved | positions of k ≥ 0 are A048724(k), positions of −k are A065621(k) | [full proof](A104895/A104895_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A104896](A104896/) | proved | counting integers below 10^n with no digit 0, 1, 2 | [full proof](A104896/A104896_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A105596](A105596/) | proved | the self-convolution with alternating signs is 1 mod 4 | [full proof](A105596/A105596_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A106249](A106249/) | proved | roots of x^n + 1 in the left half-plane (index shift by one) | [full proof](A106249/A106249_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A107363](A107363/) | proved | the nonnegative terms are exactly the Fibonacci numbers | [full proof](A107363/A107363_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md) |
| [A108863](A108863/) | proved | Motzkin transform of 0, 0, 0, A001651 | [full proof](A108863/A108863_mathlib.lean) | new | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A110034](A110034/) | corrected-and-proved | \|row sums\| of the Fibonacci–Hankel characteristic polynomials are partial sums of A061646 | [full proof](A110034/A110034_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A110320](A110320/) | proved | blocks in RNA secondary structures via Whitney numbers | [full proof](A110320/A110320_mathlib.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A110735](A110735/) | disproved | no digit insertion makes a multiple of 101 | [full proof](A110735/A110735.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A112992](A112992/) | proved | ceiling(2^r/3) is a Jacobsthal number or one more | [full proof](A112992/A112992.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A113249](A113249/) | proved | a(m, 2n+1) is a perfect square (the whole family) | [full proof](A113249/A113249.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113250](A113250/) | proved | a(m, 2n+1) is a perfect square (m = 4) | [full proof](A113250/A113250.lean) | known | [finite-identity](../methods/finite-identity/README.md) |
| [A113251](A113251/) | proved | a(m, 2n+1) is a perfect square (m = 5) | [full proof](A113251/A113251.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113252](A113252/) | proved | a(m, 2n+1) is a perfect square (m = 6) | [full proof](A113252/A113252.lean) | known | [finite-identity](../methods/finite-identity/README.md) |
| [A113253](A113253/) | proved | a(m, 2n+1) is a perfect square (m = 7) | [full proof](A113253/A113253.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113255](A113255/) | proved | a(m, 2n+1) is a perfect square (m = 9) | [full proof](A113255/A113255.lean) | known | [finite-identity](../methods/finite-identity/README.md) |
| [A113256](A113256/) | proved | a(m, 2n+1) is a perfect square (m = 10) | [full proof](A113256/A113256.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113610](A113610/) | disproved | local minima of composite digit sums do not mark twin primes | [full proof](A113610/A113610.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A114534](A114534/) | proved | the Fibonacci matrix has rank 2 | [full proof](A114534/A114534_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A115038](A115038/) | proved | every prime is y^k − x^2 | [full proof](A115038/A115038.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A123722](A123722/) | proved | multiples of 3 in the list are 3 and 3p (p prime), and every odd prime occurs | [full proof](A123722/A123722_mathlib.lean) | new (immediate) | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A123723](A123723/) | proved | multiples of 4 in the list, other than 4, are 4p with p prime | [full proof](A123723/A123723_mathlib.lean) | new (immediate) | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A124431](A124431/) | proved | Mathar's recurrence for Σ 2^k C(⌊(n+k)/2⌋, k) C(⌊(n+k+1)/2⌋, k) | [full proof](A124431/A124431_mathlib.lean) | new (immediate) | [creative-telescoping](../methods/creative-telescoping/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A125148](A125148/) | proved | every x coprime to 10 has a prime x + 10m | [full proof](A125148/A125148_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md) |
| [A126142](A126142/) | trivial or misstated | squares of the terms are 6k+1 (trivial) | [full proof](A126142/A126142_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A129454](A129454/) | proved | p-adic valuation of a triple gcd product (true after an index shift) | [full proof](A129454/A129454_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A129756](A129756/) | proved | roots of x^n − x^(n−1) − … − x − 1 in the right half-plane | [full proof](A129756/A129756_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A133212](A133212/) | proved | a(n) = 2\*A038503(n+3) for n > 0 | [full proof](A133212/A133212_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md) |
| [A134002](A134002/) | proved | n(n+5) = a(a+5) + b(b+5) is solvable iff n^2 + (n+5)^2 is composite | [full proof](A134002/A134002_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A134003](A134003/) | proved | n(n+5) = a(a+5) + b(b+5) has no positive solution when n^2 + (n+5)^2 is prime | [full proof](A134003/A134003_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A135499](A135499/) | trivial or misstated | equal digit sums at odd and even positions implies 11 \| n (trivial) | [full proof](A135499/A135499.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A135571](A135571/) | proved | differences of two positive triangular numbers in an odd number of ways | [full proof](A135571/A135571_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A135659](A135659/) | proved | every Mersenne prime > 3 is ≡ 7 (mod 24) | [full proof](A135659/A135659.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A137328](A137328/) | disproved | the prime 2 never occurs | [full proof](A137328/A137328_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A139043](A139043/) | proved | sum of composites ≤ 10^n versus 10^n(10^n+1)/2 - 1 - (10^n)^2/(2 log 10^n - 1) | [witness](A139043/A139043_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md) |
| [A140869](A140869/) | proved | if h is not a term, then 4h + 5 is prime | [full proof](A140869/A140869.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A144652](A144652/) | proved | if h is not a term, then 4h + 1 is prime (h ≥ 1) | [full proof](A144652/A144652.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A152718](A152718/) | proved | inverse Motzkin transform of A054393 | [full proof](A152718/A152718_mathlib.lean) | new | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A164754](A164754/) | proved | a(n) = 4n^2 - 11n + 5 for n >= 3 | [full proof](A164754/A164754_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A165300](A165300/) | proved | Layman's four rules for the 1,2-path sequence | [full proof](A165300/A165300_mathlib.lean) | new (immediate) | [greedy-invariant](../methods/greedy-invariant/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A165640](A165640/) | proved | a(n) = floor(4(n+4)/5) - floor(2(n+4)/3) | [full proof](A165640/A165640_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A167230](A167230/) | proved | entries of exp(Sierpiński triangle)/e are Bell numbers | [full proof](A167230/A167230_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A170941](A170941/) | proved | involutions without adjacent transpositions, proportion → 1/e | [full proof](A170941/A170941_mathlib.lean) | new | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [creative-telescoping](../methods/creative-telescoping/README.md) |
| [A176494](A176494/) | disproved | an odd prime p with \|2^m - p\| composite for every m ≥ 1 | [full proof](A176494/A176494.lean) | known | [covering-congruences](../methods/covering-congruences/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A182085](A182085/) | proved | (30k+7)(60k+13)(150k+31) is Carmichael whenever its factors are prime | [full proof](A182085/A182085_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182088](A182088/) | proved | (30n-29)(60n-59)(90n-89)(180n-179) is Carmichael whenever its factors are prime | [full proof](A182088/A182088_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182089](A182089/) | proved | (330k+7)(660k+13)(990k+19)(1980k+37) is Carmichael whenever its factors are prime | [full proof](A182089/A182089_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182132](A182132/) | proved | (30n-7)(90n-23)(300n-79) is Carmichael whenever its factors are prime | [full proof](A182132/A182132_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182133](A182133/) | proved | (30n+13)(90n+37)(150n+61) is Carmichael whenever its factors are prime | [full proof](A182133/A182133_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182151](A182151/) | proved | Carmichael numbers divisible by 31 lie in three classes mod 2790 | [full proof](A182151/A182151_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182206](A182206/) | proved | Carmichael numbers divisible by 37 and 73 are 37·73·(18n+91) | [full proof](A182206/A182206_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182207](A182207/) | proved | Carmichael numbers divisible by p and 2p - 1 are p(2p-1)(n(2p-2)+p) | [full proof](A182207/A182207_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182208](A182208/) | proved | Carmichael numbers divisible by 7 are never 7(6m+1)(6n-1) | [full proof](A182208/A182208_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A182334](A182334/) | disproved | the order-9 recurrence fails at n = 10, 11 (holds from n = 12) | [full proof](A182334/A182334_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [units-pell](../methods/units-pell/README.md) |
| [A182336](A182336/) | proved | n + 1 ≤ a(n) ≤ 9n/8 + 1 for n > 96 | [full proof](A182336/A182336_mathlib.lean) | new (immediate) | [parametric-family](../methods/parametric-family/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A182381](A182381/) | proved | Carmichael numbers divisible by 17 and 29 are 952n + 561 | [full proof](A182381/A182381_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182416](A182416/) | proved | (60k+13)(180k+37)(300k+61) is Carmichael whenever its factors are prime | [full proof](A182416/A182416_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182515](A182515/) | proved | Carmichael numbers divisible by 23 and 67 are 23·67·(66n+23) | [full proof](A182515/A182515_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182532](A182532/) | proved | Carmichael numbers divisible by 7 and 17: the four residue classes mod 120 | [full proof](A182532/A182532_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A187011](A187011/) | proved | det(\|p\_i − p\_j\|) over the first n primes | [full proof](A187011/A187011_growth_mathlib.lean) | partly-known | [selberg-sieve-polynomial](../methods/selberg-sieve-polynomial/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188644](A188644/) | proved | (k^n + k^(-n))/2 is an integer for k = (√(x²-1) + x)² | [full proof](A188644/A188644_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188645](A188645/) | proved | (k^n + k^(-n))/2 is an integer for k = (√(x²+1) + x)² | [full proof](A188645/A188645_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188646](A188646/) | proved | a(n) = k a(n-1) - (k-1)/k^n is an integer sequence | [full proof](A188646/A188646_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188647](A188647/) | proved | a(n) = k a(n-1) - (k-1)/k^n is an integer sequence | [full proof](A188647/A188647_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A192205](A192205/) | proved | a(n)^(1/n) → 16√3/9 for the coefficient sum of (1-x-x^2+x^3)^n | [full proof](A192205/A192205_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A195507](A195507/) | proved | the recurrence a(n+1) = d a(n) - (d-1) n + 1 | [full proof](A195507/A195507_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A195538](A195538/) | proved | denominators of Pythagorean approximations to √8 satisfy a(n) = 35a(n−2) − 35a(n−4) + a(n−6) | [full proof](A195538/A195538_mathlib.lean) | new (immediate) | [units-pell](../methods/units-pell/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A195539](A195539/) | proved | numerators of Pythagorean approximations to √8 satisfy b(n) = 34b(n−2) − b(n−4) | [full proof](A195539/A195539_mathlib.lean) | new (immediate) | [units-pell](../methods/units-pell/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A195608](A195608/) | proved | first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts | [full proof](A195608/A195608_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [A195609](A195609/) | proved | first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts | [full proof](A195608/A195608_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [A197521](A197521/) | proved | the constant 3.52133782... is 3 plus the constant of A197383 | [full proof](A197521/A197521_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A197702](A197702/) | proved | least k with n = ±1 ±3 ± … ±(2k−1) | [full proof](A197702/A197702_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A210445](A210445/) | proved | a(n) < n for n > 1 and a(n) < n/2 for n > 47 (least k with kn practical) | [full proof](A210445/A210445_mathlib.lean) | new | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A210529](A210529/) | proved | a(n) is defined for every n (Dirichlet) | [full proof](A210529/A210529_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md) |
| [A210826](A210826/) | proved | multiplicative with Dirichlet g.f. ζ(3s)/ζ(s) | [full proof](A210826/A210826_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A212843](A212843/) | proved | Carmichael numbers with prime factors ≡ 1 (mod 10) | [full proof](A212843/A212843_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A214305](A214305/) | disproved | Coman's residue conjecture for Poulet numbers fails | [full proof](A214305/A214305_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A214449](A214449/) | disproved | A214449 is not A118168 with two 1s deleted (first mismatch n = 188) | [full proof](A214449/A214449_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A214900](A214900/) | proved | every n is a sum of three squares and a fourth power | [witness](A214900/A214900.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A214970](A214970/) | proved | L(2k-1) and L(2k)+1 divide their base-φ → base-φ² images | [full proof](A214970/A214970_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A215461](A215461/) | proved | 2n is a prime plus an odd nonprime for every n > 5 | [full proof](A215461/A215461.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A215462](A215462/) | proved | 2n is a sum of two odd nonprimes for n > 19; eventual ordering | [full proof](A215462/A215462_conj2_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [selberg-sieve-polynomial](../methods/selberg-sieve-polynomial/README.md) |
| [A217448](A217448/) | proved | a(n) exists for every n (CRT) | [full proof](A217448/A217448_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A217876](A217876/) | proved | adjacent transpositions in a random involution are asymptotically Poisson(1) | [checked](A217876/A217876_mathlib.lean) | new (immediate) | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A221650](A221650/) | proved | P(n,j,k) = [k \| j] p(n-j) counts partitions with at least j/k parts k | [full proof](A221650/A221650_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A225001](A225001/) | proved | floor(1/frac(e^(4/(5n)))) = A047203(n) for n > 1 | [full proof](A225001/A225001_mathlib.lean) | partly-known | [exact-arithmetic](../methods/exact-arithmetic/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226661](A226661/) | proved | 3x+k cycles with exactly n odd elements exist for every n | [full proof](A226661/A226661_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226676](A226676/) | proved | 3x-k cycles of every length N ≥ 3 exist | [full proof](A226676/A226676_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226677](A226677/) | proved | 3x-k cycles with exactly n odd elements exist for every n | [full proof](A226677/A226677_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A227500](A227500/) | proved | (b(n) - a(n))/c(n) is 0, 0 followed by the Fibonacci numbers | [full proof](A227500/A227500_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A227553](A227553/) | proved | number of solutions of x^2 - y^2 - z^2 ≡ 1 (mod p^s) | [full proof](A227553/A227553_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228931](A228931/) | proved | the optimal ascending continued fraction of √2 - 1 follows a(k+1) = a(k)^2 - 2 | [full proof](A228931/A228931_mathlib.lean) | known | [units-pell](../methods/units-pell/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228933](A228933/) | proved | the optimal ascending continued fraction of 1/φ follows a(n) = a(n-1)^2 - 2 from the fourth term | [full proof](A228933/A228933_mathlib.lean) | partly-known | [units-pell](../methods/units-pell/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228934](A228934/) | proved | the optimal ascending continued fraction of √44 − 6 follows a two-step recurrence | [full proof](A228934/A228934_mathlib.lean) | new (immediate) | [units-pell](../methods/units-pell/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A229910](A229910/) | proved | primitive roots g with g + g⁻¹ primitive (proved); the finite-field version fails at q = 25, 121 | [witness](A229910/A229910.lean) | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A024812](A024812/) | proved | A024812(k) = (A024813(k) + k − 1)/2 | [full proof](A024812/A024812_mathlib.lean) | — | [exact-arithmetic](../methods/exact-arithmetic/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A030210](A030210/) | proved | coefficients of (η(q)η(q^5))^4 satisfy \|a(p)\| < 2p^(3/2) | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A063289b](A063289b/) | trivial or misstated | newform dimension formula for Gamma\_1(16) (9n/4 is a typo for 9n/2) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A063305](A063305/) | trivial or misstated | newform dimension formula for Gamma\_1(32) (18n is missing the constant -41) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A063321](A063321/) | trivial or misstated | newform dimension formula for Gamma\_1(48) (the constant -72 was dropped) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A063337](A063337/) | trivial or misstated | newform dimension formula for Gamma\_1(64) (72n is missing the constant -155) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A071010](A071010/) | proved | if n is not a sum of two squares then 4 \| sigma(n) | [full proof](A071010/A071010_mathlib.lean) | — | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A085765b](A085765b/) | proved | a(n) mod 2 has period 7 | [witness](A085765b/A085765b.lean) | — | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A086449](A086449/) | proved | parity of a(n) and a(2^k − 2) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A088982](A088982/) | trivial or misstated | a prime between consecutive prime-indexed primes | — | — | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A088987](A088987/) | trivial or misstated | the number of primes between consecutive prime-indexed primes is odd | — | — | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A094913](A094913/) | proved | maximal number of distinct nonempty factors of a binary word of length n equals A006697(n) − 1 | — | known | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A095380](A095380/) | proved | the proportion of non-values of σ up to 2^n tends to 1 | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A097602](A097602/) | proved | the squares hit are exactly m² with 3 ∤ m | [full proof](A097602/A097602_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A098021](A098021/) | proved | former and current definitions agree | [full proof](A098021/A098021_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A113599](A113599/) | proved | no term is zero (pigeonhole) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A115509](A115509/) | proved | a(n) = 0 for 2^(k+1) ≤ n < 3·2^k | [full proof](A115509/A115509_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A117414](A117414/) | trivial or misstated | an Euler triangle without a definition (row sums, columns 1 and 2) | needs Mathlib | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A118990](A118990/) | proved | A118990(n) = 2^n A086906(n-1) | [full proof](A118990/A118990_mathlib.lean) | known | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A121627](A121627/) | proved | divisibility of the "complex factorial" real parts | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A131439](A131439/) | proved | 1, 7, then 4k + 14, and its inverse binomial transform | [full proof](A131439/A131439_mathlib.lean) | known | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A138904](A138904/) | proved | rotational symmetries of a binary expansion | [full proof](A138904/A138904.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A145878](A145878/) | proved | polynomial formulas for T(r+k, k), r = 3..7 (previous conjectures) | [witness](A145878/A145878.lean) | — | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A164848](A164848/) | proved | a(n) = A026741(n)/A051712(n+1) has period 24 | [full proof](A164848/A164848.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A168295](A168295/) | trivial or misstated | "Conjecture: Worpitzky forms" states no claim | — | misstated | [reading-the-statement](../methods/reading-the-statement/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A173989](A173989/) | proved | 2-adic valuations of A173300 follow A, A, A+1, A with A odd | [full proof](A173989/A173989_mathlib.lean) | known | [exact-arithmetic](../methods/exact-arithmetic/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A192023](A192023/) | trivial or misstated | the determinant-2n matrix count does not match; a linear count does | [full proof](A192023/A192023_mathlib.lean) | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A206912](A206912/) | proved | the differences of A206912 are 1s and 2s | [full proof](A206912/A206912_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A209260](A209260/) | proved | Jeffery's two conjectures (both proved in the entry's references) | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [A212916](A212916/) | proved | standard Young tableaux of height ≤ 10, a(n) ~ 10^n π^(−5) (10/n)^(45/2) ∏ Γ(j/2) | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A213257](A213257/) | proved | the excluded integers are the positions of 2 in a morphic word | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A213258](A213258/) | proved | terms are the positions of 2 in a morphic word (n = 2^(3t+2)·odd) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A217319](A217319/) | proved | the P-positions of Mark-4 are 0 and the numbers with odd 4-adic valuation | [full proof](A217319/A217319.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A223577](A223577/) | proved | A223578(n) = 2·A223577(n) − n + 1 | [full proof](A223577/A223577_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A223578](A223578/) | proved | A223578(k) = 2·A223577(k) − k + 1 | [full proof](A223577/A223577_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A225003](A225003/) | proved | a(n) = A047332(n) for n ≥ 2 | [full proof](A225003/A225003_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A226160](A226160/) | proved | a(n+1)/a(n) → exp(1/φ) = 1.855276958... (harmonic-number threshold) | [full proof](A226160/A226160_mathlib.lean) | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A226187](A226187/) | proved | a(n+1)/a(n) → exp(1/3) | [full proof](A226187/A226187_mathlib.lean) | known | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A226188](A226188/) | proved | a(n+1)/a(n) → exp(2/3) = 1.947734... (harmonic-number threshold) | [full proof](A226188/A226188_mathlib.lean) | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A229068](A229068/) | proved | standard Young tableaux of height ≤ 12, a(n) ~ 12^n π^(−6) (12/n)^33 ∏ Γ(j/2) | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |

## Disputed or only partly answered (not counted as resolutions)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A029766](A029766/) | partial | a(n) = n!·A040039(n−1) holds on the data; the entry's name does not determine the sequence | [full proof](A029766/A029766_mathlib.lean) | new (immediate) | [reading-the-statement](../methods/reading-the-statement/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A123365](A123365/) | partial | cubes mod n, partial result (two prime factors) | [checked](A123365/A123365_mathlib.lean) | new | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [elementary-proof](../methods/elementary-proof/README.md) |

## Bounds improved (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A010101](A010101/) | bound improved | a(10) ≤ 116 (upper bound improved from 117) | — | new | [interval-layer-lp](../methods/interval-layer-lp/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [A000040](A000040/): prime(n) = (6f + (-1)^f - 3)/2 with f = floor(prime(n)/3) + 1

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A000040](https://oeis.org/A000040) (line 16):
"Conjecture: a(n) = (6*f(n)+(-1)^f(n)-3)/2, n>2, where f(n) = floor(ithprime(n)/3)+1. See A181709."
(OEIS text, CC BY-SA 4.0.) The current A000040 entry no longer carries this comment.

**Result.** True; trivial.

**Argument.** A prime p ≥ 5 is 6m+1 or 6m+5. For p = 6m+1, f = 2m+1 (odd) and
(6(2m+1) − 1 − 3)/2 = 6m+1. For p = 6m+5, f = 2m+2 (even) and (6(2m+2) + 1 − 3)/2 = 6m+5.

Lean: [full proof](A000040/A000040.lean).

### [A000120](A000120/): columns of the base-b digit-sum triangle are constant

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A000120](https://oeis.org/A000120) (line 19):
"Conjecture: The sequence where a(n) is the sum of digits of (n written in base b), can be written as a
triangle T(r,k) in which all positive terms in column k are equal. Row 0 is a(0)=0 and row r lists
a(b^(r-1)) .. a(b^r - 1), for r>=1 and b>=2." (OEIS text, CC BY-SA 4.0.) The current entry shows the
b = 2 triangle (G. W. Adamson) but not this conjecture.

**Reading.** Column k (k ≥ 0) of row r ≥ 1 is s_b(b^(r−1) + k), present when k < (b−1)·b^(r−1).

**Result.** True; trivial. Every entry of column k equals 1 + s_b(k).

**Argument.** Write k = b^(r−1)·t + k' with k' < b^(r−1); then t < b − 1, so
b^(r−1) + k = b^(r−1)·(t+1) + k' with t + 1 a single digit. Digit sums split across a power of b:
s_b(b^j·t + k') = s_b(t) + s_b(k') for k' < b^j. Hence s_b(b^(r−1)+k) = (t+1) + s_b(k') = 1 + s_b(k).

Lean: [full proof](A000120/A000120.lean).

### [A004050](A004050/): only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A004050](https://oeis.org/A004050) (line 46):
"Conjecture: Only 5, 11, 17, 35, and 259 can be expressed in two different ways. See A085634."
(OEIS text, CC BY-SA 4.0.) [A085634](https://oeis.org/A085634) (checked 2026-11-01) lists these five
terms with "No more terms < 10^4000" (D. Wasserman, 2005) and no proof.

**Result.** True, given Ellison's 1971 bound on |2^x − 3^y|.

**Argument.** Let 2^a + 3^b = 2^c + 3^d with a > c. Then d > b and
2^c(2^f − 1) = 3^b(3^e − 1) with f = a − c ≥ 1, e = d − b ≥ 1. So 2^c is the exact power of 2 in
3^e − 1 and 3^b the exact power of 3 in 2^f − 1. Lifting the exponent: v_2(3^e − 1) is 1 (e odd) or
2 + v_2(e) (e even), so 2^c ≤ 4e; v_3(2^f − 1) is 0 (f odd) or 1 + v_3(f) (f even), so 3^b ≤ 3f.
From 3^d − 3^b = 2^a − 2^c < 2^a and 3^d − 3^b ≥ (2/3)·3^d we get d ≤ a, so e, f ≤ a. The equation
gives |2^a − 3^d| = |2^c − 3^b| ≤ max(2^c, 3^b) ≤ 4a.
Ellison (1971): |2^x − 3^y| > 2^x e^(−x/10) for x ≥ 12, x ∉ {13, 14, 16, 19, 27}. Since
2^x e^(−x/10) > 4x for x ≥ 12, this forces a ≤ 27. For a ≤ 27, d ≤ a, the only pairs with
|2^a − 3^d| ≤ 4a have a ≤ 8 (16 pairs), and enumerating b < d, c < a over them leaves exactly the
five values.

Lean: [witness](A004050/A004050_mathlib.lean).

### [A005329](A005329/): Product (2^i − 1) is the inverse binomial transform of A075272

**Source.** OEIS [A005329](https://oeis.org/A005329), a(n) = Product_{i=1..n} (2^i − 1). Comment
(J. W. Layman, Sep 2002): "Conjecture: this sequence is the inverse binomial transform of A075272 or,
equivalently, the inverse binomial transform of the BinomialMean transform of A075271." (OEIS text,
CC BY-SA 4.0; still a conjecture on 2026-11-06.) [A075271](https://oeis.org/A075271): a(0) = 1 and
(BM a)(n) = 2 a(n−1) for n ≥ 1, with (BM a)(n) = 2^(−n) Sum_{k=0..n} C(n,k) a(k).
[A075272](https://oeis.org/A075272) = BM(A075271).

**Result.** True.

**Argument.** Let c = A005329, so c(j+1) = (2^(j+1) − 1) c(j), and b(n) = Sum_k C(n,k) c(k). By Pascal's rule
b(k+1) = Sum_j C(k,j) (c(j) + c(j+1)) = Sum_j C(k,j) 2^(j+1) c(j). Applying the binomial transform twice,
Sum_k C(n,k) Sum_j C(k,j) d(j) = Sum_j C(n,j) 2^(n−j) d(j), so
Sum_k C(n,k) b(k+1) = Sum_j C(n,j) 2^(n−j) 2^(j+1) c(j) = 2^(n+1) b(n).
Hence a'(n) = b(n+1)/2 satisfies a'(0) = (c(0)+c(1))/2 = 1 and (BM a')(n+1) = b(n+1) = 2 a'(n). The
recurrence of A075271 determines each a(n+1) from a(0..n) (it enters with coefficient 1), so A075271 = a'
and A075272(n) = (BM a')(n) = b(n) for all n (n = 0: both are 1). So A075272 is the binomial transform
of A005329, and by binomial inversion A005329 is its inverse binomial transform. In egf terms the key
step is C(x) + C'(x) = 2 C(2x) for the egf C of c.

Lean: [full proof](A005329/A005329_mathlib.lean).

### [A005408](A005408/): one-coach primes and the first q odd numbers

**Source.** [A005408](https://oeis.org/A005408), comment by G. W. Adamson (2012): "Conjecture on primes with
one coach (A216371) relating to the odd integers: iff an integer is in A216371 (primes with one coach either
of the form 4q-1 or 4q+1, (q > 0)); the top row of its coach is composed of a permutation of the first q odd
integers." (OEIS text, CC BY-SA 4.0.)

**Reading.** The coach of an odd b (Hilton–Pedersen) has top row a_0 = 1, a_{i+1} = odd part of b − a_i,
until it returns to 1. The claim: b = 4q ± 1 is in A216371 (prime with one coach) iff the top row of the
coach of 1 is a permutation of 1, 3, …, 2q − 1.

**Result.** True; a definitional identity.

**Argument.** The map a ↦ odd part of (b − a) sends odd numbers below b/2 to odd numbers below b/2, keeps
coprimality to b, and is injective (b − a lies in (b/2, b), which holds at most one number c·2^j for a given
odd c). So it permutes the odd residues below b/2 that are coprime to b, and the coaches are its cycles.
There are exactly q odd numbers below b/2. If b is prime all of them are coprime to b, so one coach means
the coach of 1 runs through all q. Conversely, if the coach of 1 runs through all q odd numbers below b/2,
each is coprime to b; a composite odd b has an odd prime factor ≤ √b < b/2, so b is prime, and it has
one coach.

Lean: [full proof](A005408/A005408_mathlib.lean).

### [A005430](A005430/): the inverse binomial transform of n·C(2n,n) is 2·A132894(n)

**Source.** OEIS [A005430](https://oeis.org/A005430) (Apéry numbers n·C(2n,n), offset 0), comment by
R. J. Mathar (Oct 21 2012): "Conjecture: the terms of the inverse binomial transform are 2*A132894(n)."
(OEIS text, CC BY-SA 4.0; still marked "Conjecture" on 2026-11-05.)

**Reading.** Inverse binomial transform b(n) = Σ_{k=0..n} (−1)^(n−k) C(n,k) A005430(k).
A132894(n) is defined as the number of H steps in all length-n left factors of Motzkin paths; the entry's
first formula is A132894(n) = Σ_k k C(n,k) C(n−k, ⌊(n−k)/2⌋) (place the k H steps, then a left factor of a
Dyck path on the other n−k steps, of which there are C(n−k, ⌊(n−k)/2⌋)). The Lean file uses this formula.

**Result.** True for every n ≥ 0: b(n) = 2·A132894(n) (0, 2, 8, 30, 104, 350, ...).

Side finding: W. Zudilin's formula printed in A132894, "a(n) = Sum_{k=0..n} k*C(n,k)*C(2*k,k)*(-1)^(n-k)", is
exactly the inverse binomial transform above, so it equals 2·A132894(n), not A132894(n) (n = 1 gives 2, not 1).

**Argument.** For n = m+1 ≥ 1, k·C(n,k) = n·C(m,k−1) and C(2j+2,j+1) = 2·C(2j+1,j) give
b(n) = 2n Σ_j (−1)^(m−j) C(m,j) C(2j+1,j) and A132894(n) = n Σ_j C(m,j) C(j,⌊j/2⌋).
Both sums equal [x^m] (1+x)(1+x+x²)^m:
- 1+x+x² = (1+x)² − x: the term j contributes (−1)^(m−j) C(m,j) [x^j](A005430/1+x)^(2j+1) = (−1)^(m−j) C(m,j) C(2j+1,j);
- 1+x+x² = x + (1+x²): the term j contributes C(m,j)([x^j] + [x^(j−1)])(1+x²)^j = C(m,j) C(j,⌊j/2⌋).
n = 0: both sides 0.

Lean: [full proof](A005430/A005430_mathlib.lean).

### [A008578](A008578/): 1 and the primes are exactly the k with sigma(k) > k·Omega(k)

**Source.** [A008578](https://oeis.org/A008578), comment by I. Gerasimova (2013): "Conjecture: the sequence
contains exactly those k such that sigma(k) > k*BigOmega(k)." (OEIS text, CC BY-SA 4.0.) A note by
R. J. Mathar in the entry says the general case needs a proof.

**Result.** True. For composite k, σ(k) ≤ k·Ω(k), with equality only at k = 6.

**Argument.** 1 and primes satisfy the inequality (σ(p) = p + 1 > p). Let k be composite with ω(k) = m
distinct primes, and q_1 < q_2 < … the primes.
- k not squarefree (Ω ≥ m + 1): σ(k)/k < ∏_{p|k} p/(p−1) ≤ ∏_{i≤m} q_i/(q_i−1) ≤ m + 1 ≤ Ω(k). The middle
  bound is by induction: q_{i+1}/(q_{i+1}−1) ≤ (i+2)/(i+1) because q_{i+1} ≥ i + 2 (base: 2 ≤ 2).
- k squarefree (m = Ω ≥ 2): σ(k)/k = ∏(1 + 1/p) ≤ ∏_{i≤m}(1 + 1/q_i) ≤ m, by induction from
  (3/2)(4/3) = 2 using 1 + 1/q_{i+1} ≤ (i+1)/i (q_{i+1} ≥ i + 2 > i). Equality needs k = 6.

Lean: [full proof](A008578/A008578_mathlib.lean).

### [A008676](A008676/): coefficients of 1/((1-x^3)(1-x^5)) as a floor formula

**Source.** [A008676](https://oeis.org/A008676), comment by J. W. Layman (2009):
"Conjecture: a(n) = Floor(2*(n + 3)/3) - Floor(3*(n + 3)/5)." (OEIS text, CC BY-SA 4.0.)

**Result.** True for all n ≥ 0.

**Argument.** Multiplying out, (1 − x^3 − x^5 + x^8)·A(x) = 1, so a(n) = a(n−3) + a(n−5) − a(n−8) for
n ≥ 8 with a(0..7) = 1, 0, 0, 1, 0, 1, 1, 0. The floor formula R(n) satisfies the same recurrence
(R(n+15) = R(n) + 1 and the recurrence holds on each residue class mod 15) and matches the 8 initial values.

Lean: [full proof](A008676/A008676_mathlib.lean).

### [A023402](A023402/): T(n,3) and A023402 differ at n = 4

**Source.** OEIS wiki Talk:Conjectures/List. For [A023402](https://oeis.org/A023402) (line 102):
"Conjecture: a(n) = 3rd divisor of smallest number having exactly n+2 divisors, a(n)=T(n+2,3), T as defined
in A081532." For [A081532](https://oeis.org/A081532) (line 406): "Conjecture: T(n,3) = A023402(n-2) for n>2."
(OEIS text, CC BY-SA 4.0.) Neither comment is in the current entries (checked 2026-11-01).

**Result.** Both false: A023402(2) = 4 but T(4,3) = 3.

**Argument.** The smallest number with 4 divisors is 6, with divisors 1, 2, 3, 6, so T(4,3) = 3.
A023402 lists, right to left, the last digits of a power of 2 whose last k digits are all 3 or 4. The
two-digit endings drawn from {3, 4} are 33, 34, 43, 44; 33 and 43 are odd, and 34 ≡ 2 (mod 4) while
4 | 2^e for e ≥ 2; 2^18 = 262144 ends in 44. So A023402(1) = A023402(2) = 4. (The two sequences do agree
at n = 3: A023402(1) = 4 = T(3,3).)

Lean: [full proof](A023402/A023402_mathlib.lean).

### [A024187](A024187/): e_n(3, 4, ..., n+3) is A001711

**Source.** OEIS [A024187](https://oeis.org/A024187) (n-th elementary symmetric function of 3, 4, ..., n+3,
offset 1), comment by R. Stephan (Dec 30 2004): "Conjecture: essentially the same as A001711."

**Reading.** A001711 (offset 0) is "Generalized Stirling numbers, [n+4,4]_3". The entry reads this (P. Hadjicostas,
2020) as a(n) = R_{n+1}^1(−3,−1) = [x^1] Π_{r=0..n}(x+3+r) (Mitrinović numbers); this agrees with Broder's
r-Stirling numbers, Σ_k [m,k]_r x^k = x^r (x+r)(x+r+1)···(x+m−1) at m = n+4, r = 3, k = 4. "Essentially the same"
is read as A024187(n) = A001711(n) for n ≥ 1 (A001711 has the extra term a(0) = 1).

**Result.** True: A024187(n) = A001711(n) for every n ≥ 1 (and the formulas also agree at n = 0).

**Argument.** Vieta: the coefficient of x^1 in Π_{c∈S}(x+c) for |S| = n+1 is e_n(S); here S = {3, ..., n+3}.

Lean: [full proof](A024187/A024187_mathlib.lean).

### [A025060](A025060/): with signs allowed, i·j + j·k + k·i takes every integer

**Source.** [A025060](https://oeis.org/A025060), comment by J. Perry (2013): "Conjecture: If i, j and k are
allowed to be negative, but not zero, and are still distinct, then the sequence is all the integers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** (i, j) = (2, −1) gives ij + k(i + j) = k − 2, valid for k ∉ {0, 2, −1}: every integer
except −2, 0, −3. (i, j) = (4, −3) gives k − 12, valid for k ∉ {0, 4, −3}: covers −3 (k = 9), −2 (k = 10),
0 (k = 12). (The scan's note used (3, −2) as the second family, which misses −3 = k − 6 at the excluded
k = 3; the conclusion is unaffected. −3 has other representations, e.g. (4, −3, 9) above.)

Lean: [full proof](A025060/A025060.lean).

### [A025191](A025191/): row half-sums of A025177 are first differences of A027914 and of A081673/2

**Source.** OEIS [A025191](https://oeis.org/A025191) (offset 0): a(n) = Σ_{k=0..n} T(n,k), T = A025177.
Comment: "Conjectures: a(n) = A027914(n)-A027914(n-1) = (A081673(n)-A081673(n-1))/2."

**Reading.** A027907(n,k) = [x^k](A025191/1+x+x²)^n; A025177(n,k) = A027907(n,k) − A027907(n−1,k−1) (first differences in
the n,n direction; g.f. (1−yz)/(1−z(1+y+y²))); A027914(n) = Σ_{k≤n} A027907(n,k); A081673 has e.g.f.
exp(3x) − exp(x)(1 − I₀(2x)) with I₀(2x) = Σ_j x^(2j)/(j!)². Both conjectured identities for n ≥ 1
(A027914(−1) is undefined).

**Result.** True for every n ≥ 1.

**Argument.** Σ_{k≤n} A027907(n−1,k−1) = Σ_{j≤n−1} A027907(n−1,j) = A027914(n−1), which gives the first identity.
For the second: rows of A027907 are palindromic and sum to 3^n, so 2·A027914(n) = 3^n + A027907(n,n);
writing 1+x+x² = x + (1+x²) gives A027907(n,n) = Σ_{m even} C(n,m) C(m,m/2); the e.g.f. gives
A081673(n) = 3^n − 1 + Σ_{m even} C(n,m) C(m,m/2). Hence A081673(n) = 2·A027914(n) − 1.

Lean: [full proof](A025191/A025191_mathlib.lean).

### [A026002](A026002/): Bergot's array with borders n(n−1)+1 has diagonal A026002

**Source.** [A026002](https://oeis.org/A026002) (offset 1), Clark Kimberling: "a(n) = T(n,n+2), where T = Delannoy
triangle (A008288)", data 1, 7, 41, 231, 1289, ... Comment by J. M. Bergot (Apr 24 2013): "Conjecture: define an
infinite array to have m(n,1) = m(1,n) = n*(n-1)+1 in the first row and column, and
m(i,j) = m(i,j-1) + m(i-1,j-1) + m(i-1,j); then m(n,n) = a(n)." (OEIS text, CC BY-SA 4.0, revision #77 of
Sep 22 2025, checked 2026-11-06.)

**Reading.** D(i, j) (i, j ≥ 0) is the square Delannoy array of A008288: D(i,0) = D(0,j) = 1,
D(i,j) = D(i−1,j) + D(i−1,j−1) + D(i,j−1). With offset 1 the data are a(n) = D(n−1, n+1) (D(0,2) = 1, D(1,3) = 7,
D(2,4) = 41; Deutsch's formula a(n) = (1/n) Σ_k k C(n,k) C(n+k,k+1) agrees). The recurrence in the conjecture
applies for i, j ≥ 2.

**Result.** True, with the closed form 2·m(i,j) = D(i−1, j+1) + D(i+1, j−1) for all i, j ≥ 1. On the diagonal the
two terms are equal (D is symmetric), so m(n,n) = D(n−1, n+1) = a(n).

**Argument.** Both F(i,j) = D(i−1, j+1) and G(i,j) = D(i+1, j−1) satisfy the recurrence at every i, j ≥ 2 (all
indices stay in the range where the Delannoy recurrence holds). On the border j = 1: D(i−1, 2) = 2(i−1)² + 2(i−1) + 1
= 2i² − 2i + 1 and D(i+1, 0) = 1, sum 2(i(i−1) + 1); the border i = 1 is symmetric. So F + G and 2m agree on the
borders and satisfy the same recurrence, hence agree everywhere (induction on i, then j).

Lean: [full proof](A026002/A026002_mathlib.lean).

### [A029795](A029795/): k and k^3 with the same digits are not eventually all integers

**Source.** [A029795](https://oeis.org/A029795), comment by C. R. Greathouse IV (2011): "Conjecture: there
exists some m and N for which a(n) = m + n for all n >= N." (OEIS text, CC BY-SA 4.0.)

**Result.** False.

**Argument.** If a(n) = m + n for n ≥ N, every integer ≥ a(N) is a term. But for e ≥ 1, 10^e + 1 has
digits {0, 1} while (10^e + 1)^3 = 10^(3e) + 3·10^(2e) + 3·10^e + 1 has the digit 3 at position e. So
there are non-terms beyond every bound. (The same idea as M. Corneth's remark on A029797.)

Lean: [full proof](A029795/A029795_mathlib.lean).

### [A047926](A047926/): sorted three-square representations of 3^(2n) (misindexed; reduced to r_3(9^n))

**Source.** OEIS [A047926](https://oeis.org/A047926): a(n) = (3^(n+1) + 2n + 1)/4 (1, 3, 8, 22,
63, ...; offset 0). Comment (Z. Seidov, 2012): "Conjecture: Number of representations of
3^(2n) as a sum a^2 + b^2 + c^2 with 0 < a <= b <= c." It gives the examples a(1) = 3 for 3^2
and a(2) = 3 for 3^4. (OEIS text, CC BY-SA 4.0.)

**Reading.** Let C(N) = #{0 < a ≤ b ≤ c : a² + b² + c² = N}. Then C(9) = 1 and C(81) = 3, but
a(1) = 3 and a(2) = 8. The comment is off by one index, and its own examples contradict the data.
The corrected statement is C(3^(2n+2)) = a(n), or equivalently C(9^n) = (3^n + 2n − 1)/4 for
n ≥ 1. This holds numerically for n ≤ 7.

**Result.** Corrected statement: proved outside Lean from the classical Gauss–Hurwitz formula.
In Lean it is reduced exactly to one missing count (partial).

**Argument.** 1. Descent. If a² + b² + c² = 9M, the squares mod 3 are 0 or 1, so either 3 divides all of a,
   b, c or none of them. The first kind are 3·(solutions of M). So C(9^n) = C(9^(n−1)) + P(n),
   where P(n) counts the primitive sorted solutions (all coordinates prime to 3).
2. So the corrected conjecture holds if and only if P(n) = (3^(n−1) + 1)/2 for all n ≥ 1.
3. Count via r_3. The Gauss–Hurwitz formula
   r_3(m²) = 6 ∏_{p^e ∥ m, p odd} (σ(p^e) − (−1/p) σ(p^(e−1))) gives
   r_3(9^n) = 6(2·3^n − 1). The equation x² + y² = 9^n has only the solutions (±3^n, 0) and
   (0, ±3^n), by the same descent. So exactly 6 integer representations have a zero coordinate.
   3a² = 9^n is impossible, and 2a² + c² = 9^n has exactly n positive solutions. That leaves
   48D + 24n = 12·3^n − 12 for the D sorted triples with distinct entries, and
   C = D + n = (3^n + 2n − 1)/4.

Lean: [full proof](A047926/A047926_mathlib.lean).

### [A051451](A051451/): the "next twin pair above a(n)" form fails at n = 35

**Source.** OEIS wiki Talk:Conjectures/List, entry for [A051451](https://oeis.org/A051451) (line 154), by
M. Winkler (2013): "Conjecture: For every n > 2, there exists a twin prime pair [p, p+2] with p < a(n) such
that the "next" twin prime pair > a(n) is [a(n)+p, a(n)+p+2]." (OEIS text, CC BY-SA 4.0.)
a(n) = lcm(1..x), x the n-th prime power (A000961, starting at 1).

**Reading.** The current entry (checked 2026-11-01) words the conjecture without "next": some twin pair
[p, p+2] with p < a(n) has [a(n)+p, a(n)+p+2] also a twin pair (verified there for n ≤ 1000). That version
is not addressed here and stays open. This item concerns the 2013 "next" version.

**Result.** The "next" version is false at n = 35.

**Argument.** A000961(35) = 89, so L = a(35) = lcm(1..89) (39 digits). The first twin prime pair above L
is [L + 17159, L + 17161], and 17161 = 131^2 is not prime, so the offset 17159 is not the smaller member of
a twin prime pair. (Every offset m < 89^2 coprime to all primes ≤ 89 is prime, but the first twin pair
typically lies near 0.76·x^2 = 6000 or more here, so composite offsets occur.)

Lean: [full proof](A051451/A051451_mathlib.lean).

### [A051924](A051924/): a(n) ≡ n + 2 (mod n^2) also holds at n = 16843^2

**Source.** [A051924](https://oeis.org/A051924) (a(n) = C(2n,n) − C(2n−2,n−1) = (3n−2)·Catalan(n−1)),
comment by G. Detlefs (2013): "Conjecture: a(n) mod n^2 = n+2 iff n is an odd prime." (OEIS text, CC BY-SA 4.0.)

**Result.** False: n = 16843^2 = 283686649 is composite and a(n) ≡ n + 2 (mod n^2). The "if" direction
holds (Wolstenholme for p ≥ 5; a(3) = 14 ≡ 5).

**Argument.** a(n)(2n − 1) = C(2n−1, n−1)(3n − 2) and (n + 2)(2n − 1) = 2n^2 + 3n − 2 ≡ 3n − 2 (mod n^2);
2n − 1 is invertible mod n^2, so a(n) ≡ n + 2 (mod n^2) iff C(2n−1, n−1) ≡ 1 (mod n^2). Take n = p^2,
p an odd prime. In C(2n−1, n−1) = ∏_{k=1}^{n−1} (n+k)/k, the factors with p ∤ k multiply to
1 + n·Σ 1/k (mod p^4), and Σ_{k<p^2, p∤k} 1/k ≡ 0 (mod p^2) by pairing k with p^2 − k; the factors with
k = pj give ∏_{j<p} (p + j)/j = C(2p−1, p−1). So the condition at n = p^2 is C(2p−1, p−1) ≡ 1 (mod p^4):
p a Wolstenholme prime. 16843 is one (McIntosh 1995).

Lean: [full proof](A051924/A051924_mathlib.lean).

### [A054120b](A054120b/): T(n,k) = A081577(n,k) − A081577(n−2,k−1)

**Source.** OEIS [A054120](https://oeis.org/A054120): triangle with T(n,0) = T(n,n) = 1; T(n,k) is the sum of the
T(i,j) on or between vertical lines through T(n−1,k−1) and T(n−1,k), not below T(n,k). Comment by G. McGarvey
(Sep 20 2007): "Conjecture: T(n,k) = A081577(n,k) - A081577(n-2,k-1). (A081577 is Pascal-(1,2,1) array)."
The first McGarvey conjecture (T(n,k) = T(n−1,k−1) + 2T(n−2,k−1) + T(n−1,k)) was proved in the entry by
R. J. Hendel (2015).

**Reading.** In the centred layout T(i,j) sits at horizontal position 2j − i, so T(n,k) (0 < k < n) is the sum over
rows i < n and 2k−n−1 ≤ 2j−i ≤ 2k−n+1. A081577 is the square array S(a,0) = S(0,b) = 1,
S(a,b) = S(a,b−1) + 2S(a−1,b−1) + S(a−1,b), read as a triangle A081577(n,k) = S(n−k,k) (symmetric), and is 0 outside
0 ≤ k ≤ n.

**Result.** True for all n, k (both sides 0 for k > n).

**Argument.** Let G(n,x) be the sum of T(i,j), i < n, on the vertical line 2j−i = x. For n ≥ 1 and every k,
T(n,k) = G(n,2k−n−1) + G(n,2k−n) + G(n,2k−n+1) (boundary columns checked directly). T(n−2,k−1) uses the same
three lines, so T(n,k) − T(n−2,k−1) is the contribution of rows n−1 and n−2: T(n−1,k−1) + T(n−2,k−1) + T(n−1,k)
(parity kills the other three line/row pairs). This is McGarvey's first recurrence for n ≥ 3, k ≥ 1.
The zero-extended triangle A081577 satisfies the same recurrence at every (n,k) ≠ (0,0), so
D(n,k) = A081577(n,k) − A081577(n−2,k−1) satisfies it except at (0,0), (2,1). T and D agree on rows 0–2
(T(2,1) = 3 = 4 − 1), hence everywhere by induction on n.

Lean: [full proof](A054120b/A054120b_mathlib.lean).

### [A061002](A061002/): denominator(H(p)/H(p−1)) / numerator(H(p−1)/p^2) = p^3

**Source.** [A061002](https://oeis.org/A061002), comment by G. Detlefs (2013): "Conjecture: If p is the n-th
prime and H(n) is the n-th harmonic number, then denominator(H(p)/H(p-1))/numerator(H(p-1)/p^2) = p^3.
A193758(p)/a(n) = p^3, p > 3." (OEIS text, CC BY-SA 4.0.)

**Result.** True for all primes p ≥ 5.

**Argument.** Write H(p−1) = a/b in lowest terms. Wolstenholme: p^2 | a; also p ∤ b. Then
H(p)/H(p−1) = 1 + b/(pa) = (pa + b)/(pa), and gcd(pa + b, p) = gcd(b, p) = 1, gcd(pa + b, a) = gcd(b, a) = 1,
so the denominator is pa. H(p−1)/p^2 = (a/p^2)/b in lowest terms, numerator a/p^2. Ratio pa/(a/p^2) = p^3.

Lean: [full proof](A061002/A061002_mathlib.lean).

### [A072901](A072901/): composites with disc Q(√n) = 4n are squarefree

**Source.** [A072901](https://oeis.org/A072901) (composite n with discriminant of Q(√n) equal to 4n),
comment by V. Librandi and M. Marcus: "Conjecture: All terms are squarefree." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** Write n = d·s^2 with d squarefree (d > 1, as n is not a square). Q(√n) = Q(√d) has
discriminant d (d ≡ 1 mod 4) or 4d (d ≡ 2, 3 mod 4), at most 4d. If s ≥ 2 this is < 4n. So
discriminant 4n forces s = 1 (and n ≡ 2, 3 mod 4).

Lean: [full proof](A072901/A072901_mathlib.lean).

### [A074766](A074766/): p(2n) − 2p(n) < 2n for all n

**Source.** [A074766](https://oeis.org/A074766) (a(n) = prime(2n) − 2·prime(n) − n), comment:
"Conjecture: p(2n)-2p(n) < 2n for all n." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Dusart (1999): p_k ≤ k(ln k + ln ln k − 0.9484) for k ≥ 39017 and
p_k ≥ k(ln k + ln ln k − 1) for k ≥ 2. For n ≥ 19509 (so 2n ≥ 39017):
p(2n) − 2p(n) ≤ 2n·(ln 2 + 0.0516 + ln(ln 2n / ln n)) = 2n·(ln 2 + 0.0516 + ln(1 + ln 2/ln n)).
The bracket decreases in n and equals 0.8126 at n = 19509, so p(2n) − 2p(n) < 0.82·2n < 2n.
For n < 19509 the inequality is checked directly.

Lean: needs Mathlib.

### [A079665](A079665/): when is (b^s + 1)/(b^r + 1) an integer

**Source.** [A079665](https://oeis.org/A079665), comment: "Conjecture: (b^s+1)/(b^r+1) is an integer if and
only if: 1) r<s/2, 2) if s==1 (mod 2) then r is divisor of s, 3) if s=k*2^t with gcd(k,2^t)=1 then r is
2^t*u with u dividing k" (OEIS text, CC BY-SA 4.0.)

**Reading.** b ≥ 2 and 1 ≤ r < s (the rows of A079665 have r ≤ s − 1).

**Result.** True; classical.

**Argument.** Write s = qr + ρ, 0 ≤ ρ < r. Since b^r ≡ −1 (mod b^r + 1), b^s + 1 ≡ (−1)^q b^ρ + 1. For
ρ = 0 this is 0 iff q is odd. For ρ > 0 it is b^ρ + 1 or 1 − b^ρ, both nonzero with absolute value
< b^r + 1. So b^r + 1 | b^s + 1 iff r | s and s/r is odd. With s = k·2^t (k odd) that says r = 2^t·u with
u | k, which is condition 3; then s/r ≥ 3 gives condition 1, and condition 2 is the case t = 0 of 3.

Lean: [full proof](A079665/A079665_mathlib.lean).

### [A080674](A080674/): counting integers below 10^n with digits only in {6,7,8,9}

**Source.** [A080674](https://oeis.org/A080674) (a(n) = (4/3)(4^n − 1)), comment by A. Wajnberg (2005):
"Conjectured to be the number of integers from 0 to (10^n)-1 that lack 0, 1, 2, 3, 4 and 5 as a digit."
(OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** 0 has the digit 0. A positive integer below 10^n with no digit in {0..5} is a string of
length k ∈ {1..n} over {6, 7, 8, 9}: 4^k of each length, total 4 + … + 4^n = (4/3)(4^n − 1).

Lean: [full proof](A080674/A080674_mathlib.lean).

### [A081199](A081199/): collinear 4-tuples in the 4^n grid

**Source.** [A081199](https://oeis.org/A081199) (5th binomial transform of 0,1,0,1,…), comment by R. H. Hardin
(2010): "Conjecture (verified up to a(9)): Number of collinear 4-tuples of points in a 4 X 4 X ... n-dimensional
cubic grid." (OEIS text, CC BY-SA 4.0.)

**Result.** True: both equal ((6)^n − 4^n)/2.

**Argument.** The m-th binomial transform of 0,1,0,1,… is Σ_{j odd} C(n,j) m^(n−j) = ((m+1)^n − (m−1)^n)/2,
here m = 5. Now take 4 collinear points of {1..4}^n on a line x = a + t·v. In a coordinate with v_i ≠ 0
the 4 points have 4 distinct values in {1..4}, i.e. all of them; so the parameters form an arithmetic
progression and every coordinate is constant, runs 1..4, or runs 4..1 along it. These are the
combinatorial lines of the 4^n tic-tac-toe board: choose for each coordinate a constant (4 ways), up or
down, exclude all-constant, and identify a line with its reversal: ((6)^n − 4^n)/2.

Lean: [full proof](A081199/A081199_mathlib.lean).

### [A081200](A081200/): collinear 5-tuples in the 5^n grid

**Source.** [A081200](https://oeis.org/A081200) (6th binomial transform of 0,1,0,1,…), comment by R. H. Hardin
(2010): "Conjecture (verified up to a(9)): Number of collinear 5-tuples of points in a 5 X 5 X ... n-dimensional
cubic grid." (OEIS text, CC BY-SA 4.0.)

**Result.** True: both equal ((7)^n − 5^n)/2.

**Argument.** The m-th binomial transform of 0,1,0,1,… is Σ_{j odd} C(n,j) m^(n−j) = ((m+1)^n − (m−1)^n)/2,
here m = 6. Now take 5 collinear points of {1..5}^n on a line x = a + t·v. In a coordinate with v_i ≠ 0
the 5 points have 5 distinct values in {1..5}, i.e. all of them; so the parameters form an arithmetic
progression and every coordinate is constant, runs 1..5, or runs 5..1 along it. These are the
combinatorial lines of the 5^n tic-tac-toe board: choose for each coordinate a constant (5 ways), up or
down, exclude all-constant, and identify a line with its reversal: ((7)^n − 5^n)/2.

Lean: [full proof](A081200/A081200_mathlib.lean).

### [A081201](A081201/): collinear 6-tuples in the 6^n grid

**Source.** [A081201](https://oeis.org/A081201) (7th binomial transform of 0,1,0,1,…), comment by R. H. Hardin
(2010): "Conjecture (verified up to a(9)): Number of collinear 6-tuples of points in a 6 X 6 X ... n-dimensional
cubic grid." (OEIS text, CC BY-SA 4.0.)

**Result.** True: both equal ((8)^n − 6^n)/2.

**Argument.** The m-th binomial transform of 0,1,0,1,… is Σ_{j odd} C(n,j) m^(n−j) = ((m+1)^n − (m−1)^n)/2,
here m = 7. Now take 6 collinear points of {1..6}^n on a line x = a + t·v. In a coordinate with v_i ≠ 0
the 6 points have 6 distinct values in {1..6}, i.e. all of them; so the parameters form an arithmetic
progression and every coordinate is constant, runs 1..6, or runs 6..1 along it. These are the
combinatorial lines of the 6^n tic-tac-toe board: choose for each coordinate a constant (6 ways), up or
down, exclude all-constant, and identify a line with its reversal: ((8)^n − 6^n)/2.

Lean: [full proof](A081201/A081201_mathlib.lean).

### [A081320](A081320/): 3-smooth part of Fibonacci numbers

**Source.** [A081320](https://oeis.org/A081320) (largest 3-smooth divisor of F(n)), comment:
"Conjecture: for n>12 and n>0 modulo 12: a(n)=a(n-12) and a(12*k)=A065331(k)*144." (OEIS text, CC BY-SA 4.0.)
C. R. Greathouse IV notes in the entry that the first part follows from strong divisibility.

**Result.** True.

**Argument.** Classical valuations (Lengyel 1995): v_2(F_n) = 0 if 3 ∤ n, 1 if n ≡ 3 (mod 6), v_2(n) + 2
if 6 | n; v_3(F_n) = 0 if 4 ∤ n, v_3(n) + 1 if 4 | n. If 12 ∤ n then v_2(F_n) ∈ {0, 1, 3} and
v_3(F_n) ∈ {0, 1} depend only on n mod 12, so a(n) = a(n − 12). For n = 12k: v_2 = v_2(k) + 4 and
v_3 = v_3(k) + 2, so a(12k) = 2^4·3^2·2^(v_2 k)·3^(v_3 k) = 144·A065331(k).

Lean: [full proof](A081320/A081320_mathlib.lean).

### [A081532](A081532/): T(n,3) and A023402 differ at n = 4

**Source.** OEIS wiki Talk:Conjectures/List. For [A023402](https://oeis.org/A023402) (line 102):
"Conjecture: a(n) = 3rd divisor of smallest number having exactly n+2 divisors, a(n)=T(n+2,3), T as defined
in A081532." For [A081532](https://oeis.org/A081532) (line 406): "Conjecture: T(n,3) = A023402(n-2) for n>2."
(OEIS text, CC BY-SA 4.0.) Neither comment is in the current entries (checked 2026-11-01).

**Result.** Both false: A023402(2) = 4 but T(4,3) = 3.

**Argument.** The smallest number with 4 divisors is 6, with divisors 1, 2, 3, 6, so T(4,3) = 3.
A023402 lists, right to left, the last digits of a power of 2 whose last k digits are all 3 or 4. The
two-digit endings drawn from {3, 4} are 33, 34, 43, 44; 33 and 43 are odd, and 34 ≡ 2 (mod 4) while
4 | 2^e for e ≥ 2; 2^18 = 262144 ends in 44. So A023402(1) = A023402(2) = 4. (The two sequences do agree
at n = 3: A023402(1) = 4 = T(3,3).)

Lean: [full proof](A081532/A081532_mathlib.lean).

### [A083219](A083219/): roots of x^n - x^(n-1) - ... - 1 in the left half-plane

**Source.** [A083219](https://oeis.org/A083219), a(n) = n − 2⌊n/4⌋. The conjecture says a(n) counts the roots of
x^n − x^(n−1) − … − x − 1 in the left half-plane.

**Reading.** As written, the claim is off by one in its indexing. The count for degree n+1 equals a(n).

**Result.** True with the index shift. For every n, x^(n+1) − x^n − … − x − 1 has n − 2⌊n/4⌋ roots with Re < 0.

**Argument and evidence.** Proved together with A129756: see [OEIS/A129756](A129756/README.md). The Lean
theorem is `A129756.A083219_roots` in `OEIS/A129756/A129756_mathlib.lean`.

Lean: [full proof](A129756/A129756_mathlib.lean).

### [A083452](A083452/): n written n times exceeds n^n

**Source.** [A083452](https://oeis.org/A083452) (a(n) = (n concatenated n times − n^n)/n), comment:
"Conjecture: All the terms are all positive for n>1. (n times concatenation of n with itself > n^n), n>1."
(OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** Let n have d digits, so n < 10^d. The n-fold concatenation is at least n·10^(d(n−1)), while
n^n = n·n^(n−1) < n·10^(d(n−1)) for n ≥ 2.

Lean: [full proof](A083452/A083452.lean).

### [A087324](A087324/): no term has a perfect-square prime signature

**Source.** [A087324](https://oeis.org/A087324) (n such that n and its 9's complement have the same prime
signature), comment: "Conjecture: (1) Sequence is infinite. (2) For every prime signature there corresponds a
term in this sequence." (OEIS text, CC BY-SA 4.0.)

**Reading.** The 9's complement of a d-digit n is 10^d − 1 − n.

**Result.** Conjecture (2) is false: no term has an all-even signature such as p^2 or p^2·q^2.
Conjecture (1) is not addressed (open).

**Argument.** A number has an all-even signature iff it is a perfect square. If n and its complement
share such a signature, both are squares, but they sum to 10^d − 1 ≡ 3 (mod 4) for d ≥ 2, while squares
are 0 or 1 mod 4. For d = 1 the pairs (n, 9 − n) contain no two squares. (The 10's-complement analogue,
A087325, is refuted in its entry in the same way.)

Lean: [full proof](A087324/A087324_mathlib.lean).

### [A088104](A088104/): an n-digit prime beginning with prime(n) always exists

**Source.** [A088104](https://oeis.org/A088104) (smallest n-digit prime beginning with prime(n), 0 if none),
comment: "Conjecture: No term is zero." (OEIS text, CC BY-SA 4.0.) The entry notes that Legendre's conjecture
would imply it (C. W. Wu, 2019).

**Result.** True (no term is zero), given Dusart's 2010 short-interval bound.

**Argument.** Let P = prime(n) have d digits (d ≤ n). The candidates are the integers in [x, x + 10^(n−d))
with x = P·10^(n−d) ≥ 10^(n−1), i.e. [x, x + x/P). Dusart (2010): for x ≥ 396738 there is a prime in
(x, x(1 + 1/(25 ln² x))]. For n ≥ 7, x ≥ 10^6 and 25 ln² x ≥ 25(n−1)² ln² 10 > 132(n−1)² > P (as
prime(n) < n(ln n + ln ln n) for n ≥ 6), so that prime lies in [x, x + x/P). For n ≤ 14 the terms are
found directly (n = 1: a(1) = 2).

Lean: needs Mathlib.

### [A088120](A088120/): the common difference is 2 at n = 12

**Source.** [A088120](https://oeis.org/A088120) (smallest prime of the form a(a+d)···(a+(n−1)d) + d),
comment: "Conjectures: (1) Sequence is infinite. (2) The common difference arising = 1 except for n = 4 and 5
in which case it is 2." (OEIS text, CC BY-SA 4.0.)

**Result.** Conjecture (2) is false: a(12) = 1·3·5···23 + 2 = 316234143227, with d = 2 (the entry's own data
lists this value). The scan also found d ≠ 1 at n = 24 (d = 2) and n = 33, 39 (d = 3); not re-checked here.
Conjecture (1) is not addressed.

**Argument.** The values ≤ W = 316234143227 are k(k+1)···(k+11) + 1 for k = 1..4 (12!+1 = 13²·2834329,
13!+1 = 83·75024347, 14!/2+1 = 31·4289·327839, 15!/6+1 = 32009·6808889) and W itself; k = 5 (d = 1), a = 2
(d = 2) and any d ≥ 3 give larger values, as the product grows with a and d. W is prime.

Lean: [full proof](A088120/A088120_mathlib.lean).

### [A088226](A088226/): a(n) = |a(n-1) − a(n-2) − a(n-3)| is half the smallest even distance from n − 1 to a square

**Source.** OEIS [A088226](https://oeis.org/A088226) (offset 1): a(1) = 0, a(2) = 0, a(3) = 1,
a(n) = |a(n−1) − a(n−2) − a(n−3)| for n > 3: 0, 0, 1, 1, 0, 2, 1, 1, 2, 0, 3, ... Conjecture
(R. Stephan, Sep 2013): "a(n) = m/2 where m is the smallest even distance from n to a square."
(OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05, revision #30.)

**Reading.** Let f(m) = (smallest even |m − s²|, s ≥ 0)/2. As printed (a(n) = f(n)) the conjecture is
false: a(2) = 0 but f(2) = 1 (2 is at distance 2 from 0 and from 4, distance 1 from 1). It also fails at
n = 4, 5, 6, 8, ... Stephan's PARI program in the entry computes f(n), and it does not reproduce the
data either (it gives 1 at n = 2 and 0 at n = 4). The entry's own formula a(k² + 2m + 1) = m,
a(k² + 2m + 2) = k − m (0 ≤ m ≤ k) is the shifted statement a(n) = f(n − 1).

**Result.** Corrected form true: a(n) = f(n − 1) for every n ≥ 1. The printed form is a misstatement by
one index.

**Argument.** Block formula: for k ≥ 0 and 1 ≤ j ≤ 2k + 1, a(k² + j) = (j − 1)/2 if j is odd and
k − (j − 2)/2 if j is even. Induction on k (k = 0, 1 by direct computation). Inside block k ≥ 2:
for j ≥ 4 the three previous terms are in the same block, and for odd j = 2m + 1
|(k − m + 1) − (m − 1) − (k − m + 2)| = m, for even j = 2m + 2 |m − (k − m + 1) − (m − 1)| = k − m.
For j = 1, 2, 3 the previous block ends with a(k²−2), a(k²−1), a(k²) = k − 2, 1, k − 1, giving
|k − 1 − 1 − (k − 2)| = 0, |0 − (k − 1) − 1| = k, |k − 0 − (k − 1)| = 1.
Distance side: n − 1 = k² + j − 1 is at distance j − 1 from k² and 2k + 2 − j from (k + 1)²; these
sum to 2k + 1, so exactly one is even, and it is (j − 1) for odd j and 2k + 2 − j for even j, i.e.
twice the block value. Squares s² with s ≤ k − 1 or s ≥ k + 2 are at distance ≥ 2k + j − 2 resp.
≥ 4k + 5 − j, never below the even candidate (which is ≤ 2k, and 0 when j = 1). Every n ≥ 1 is
k² + j with k = ⌊√(n−1)⌋ and 1 ≤ j ≤ 2k + 1.

Lean: [full proof](A088226/A088226_mathlib.lean).

### [A088276](A088276/): 10^k + 9351 is never prime, though 9351 ≡ 0 (mod 3)

**Source.** [A088276](https://oeis.org/A088276) (smallest k with 10^k + r a prime ending in r, r the n-th
odd number not divisible by 5, offset 0; 0 if none), comment: "Conjecture: (1) The only zero entries are for
values of r == 2 (mod 3). (2) There are infinitely many values of k such that 10^k + r is a prime if r is not
== 2 (mod 3)." (OEIS text, CC BY-SA 4.0.)

**Result.** Both false at r = 9351 (index n = 3740 with the entry's offset 0; the scan's note said 3741,
which is the 1-based position). Further covered r found by the scan: 46927, 48247, 56473, 61863.

**Argument.** Covering congruences with period 6: 7 | 10^k + 9351 for k ≡ 0 (mod 6), 11 for k odd,
13 for k ≡ 2 (mod 6), 37 for k ≡ 1 (mod 3). These cover every k, and 10^k + 9351 > 37.

Lean: [full proof](A088276/A088276_mathlib.lean).

### [A088617](A088617/): mean number of U steps in a Schröder n-path is ~ n/√2

**Source.** [A088617](https://oeis.org/A088617), T(n,k) = C(n+k,n)·C(n,k)/(k+1), the number of Schröder
paths from (0,0) to (2n,0) (steps U = (1,1), D = (1,−1), H = (2,0), never below the axis) with k U steps.
Comment by David Callan (2008): "Conjecture: The expected number of U's in a Schroeder n-path is
asymptotically sqrt(1/2)*n for large n." (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05.)

**Result.** True. With r(n) = Σ_k T(n,k) (A006318) and U(n) = Σ_k k·T(n,k), exactly
4·U(n+1) = (3n+2)·r(n+1) − n·r(n), and U(n)/(n·r(n)) → √(1/2).

**Argument.** Write T(n,k) = f_k(n)/(k!(k+1)!) with f_k(n) = (n+k)(n+k−1)…(n−k+1), a polynomial in n
that vanishes for n < k. Comparing f_{k+1}(n+2), f_{k+1}(n+1), f_k(n+1), f_{k+1}(n) gives the coefficient
identity (n+3)·T(n+2,k+1) = (2n+3)·(T(n+1,k+1) + 2·T(n+1,k)) − n·T(n,k+1). Summing it with weights 1 and k:
(n+3)·r(n+2) = 3(2n+3)·r(n+1) − n·r(n) and (n+3)·U(n+2) = (2n+3)·(3U(n+1) + 2r(n+1)) − n·U(n). Induction
then gives 4U(n+1) = (3n+2)r(n+1) − n·r(n). Let α = 3+2√2, β = 3−2√2 = 1/α and x(n) = r(n+1)/r(n). Then
(n+3)·x(n+1) = 3(2n+3) − n/x(n), and by induction 2 ≤ x(n) ≤ α and (n+1)(α − x(n)) ≤ 20 (the error map
contracts by a factor β/2 and adds (3α−9)/(n+3)). So x(n) → α, and
U(n+1)/((n+1)·r(n+1)) = ((3n+2) − n/x(n))/(4(n+1)) → (3 − β)/4 = √2/2 = √(1/2).

Lean: [checked](A088617/A088617_mathlib.lean).

### [A089758](A089758/): the prime concatenation chain never stops

**Source.** [A089758](https://oeis.org/A089758) (primes arising in A089757), comment: "Conjecture: Sequence is
infinite." (OEIS text, CC BY-SA 4.0.) A089757: increasing multiples of 3 such that a(n)a(n−1)…a(1)1
(concatenation) is prime; each step takes the least admissible next term.

**Result.** True, by Dirichlet's theorem.

**Argument.** Let C be the current prime concatenation, with L digits. C > 5 is prime, so gcd(C, 30) = 1.
The next term is the least 3y > (last term) with 3y·10^L + C prime. The numbers C + (3·10^L)·y form an
arithmetic progression with gcd(C, 3·10^L) = 1, so it contains infinitely many primes (Dirichlet), and some
y beyond the last term works. Prepending 3y to C is exactly 3y·10^L + C. So every step succeeds and
A089758 is infinite.

Lean: [full proof](A089758/A089758_mathlib.lean).

### [A090519](A090519/): some prime p has floor(10^n/p) prime

**Source.** [A090519](https://oeis.org/A090519) (smallest prime p with floor(10^n/p) prime, 0 if none),
comment: "Conjecture: No term is zero." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** n = 1: floor(10/2) = 5. For n ≥ 2, m = 10^n/4 is an integer and Bertrand's postulate gives a
prime p with m < p ≤ 2m = 10^n/2. Then 2 ≤ 10^n/p < 4, so floor(10^n/p) ∈ {2, 3}, both prime.
(The scan used Nagura's theorem on (x, 6x/5] with p ∈ (10^n/3, 10^n/2]; Bertrand on (10^n/4, 10^n/2] suffices.)

Lean: [full proof](A090519/A090519_mathlib.lean).

### [A094787](A094787/): every prime is a least prime p with p + n a perfect power

**Source.** [A094787](https://oeis.org/A094787) (a(n) = smallest prime p with p + n a perfect power m^k,
k ≥ 2), comment: "Conjecture: every prime is contained in this sequence." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Fix a prime q. For m > q put n = m^2 − q ≥ 1, so q + n = m^2. For a prime p < q, p + n lies in
[m^2 − q + 2, m^2 − 1]; this window contains no square, since (m−1)^2 < m^2 − q + 2. So a(n) = q as soon as
the window holds no non-square perfect power. The windows for different m > q are disjoint, and the
non-square perfect powers up to M^2 number O(M^(2/3) log M) (cubes and higher powers), so fewer than
M − q values of m ≤ M are blocked once M is large. Hence some m works.

Lean: [full proof](A094787/A094787_mathlib.lean).

### [A097406](A097406/): primitive prime factors of 2^n − 1 are ≡ 1 (mod n)

**Source.** [A097406](https://oeis.org/A097406) (largest primitive prime factor of 2^n − 1, or 1), comment:
"Conjectures: (1) For every n the highest unique prime factor is of the form kn+1. ... (2) For each composite n
many factors of the form kn+1 occur intermittently but always singly in any cofactor pair. (3) For each prime n
every factor is of the form kn+1." (OEIS text, CC BY-SA 4.0.)

**Result.** (1) and (3) are true and standard; (2) is too vague to be a mathematical statement (misstated).

**Argument.** A primitive prime factor p of 2^n − 1 divides no 2^m − 1 with m < n, so ord_p(2) = n, and
ord_p(2) | p − 1 (Fermat), so p ≡ 1 (mod n). (When a(n) = 1, as for n = 1, 6, the value 1 = 0·n + 1 also fits.)
For prime n, any prime p | 2^n − 1 has ord_p(2) | n and ord_p(2) ≠ 1, so ord_p(2) = n and again p ≡ 1 (mod n).

Lean: [full proof](A097406/A097406_mathlib.lean).

### [A098016](A098016/): the mean of consecutive primes is never prime

**Source.** [A098016](https://oeis.org/A098016), comment: "Conjecture: (1/2)(prime(x+1) + prime(x)) is not prime
for all x." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** For x = 1 the mean is 5/2, not an integer. For x ≥ 2 the mean is an integer strictly between the
consecutive primes prime(x) and prime(x+1), so it is not prime.

Lean: [full proof](A098016/A098016_mathlib.lean).

### [A100056](A100056/): the A054065 permutations do not maximize the sum of differences

**Source.** [A100056](https://oeis.org/A100056) (sum of absolute differences of the A054065 permutation of 1..n),
comment: "Conjecture: a(n) provides the maximum sum of difference terms of any permutation of 1 through n. A054065
(or reversals) give the optimal permutations and a(n) gives the sum." (OEIS text, CC BY-SA 4.0.)

**Reading.** "Sum of difference terms" = Σ |π(i+1) − π(i)|; the entry's a(4) = 7 from (2,4,1,3) fixes this reading.

**Result.** False at n = 5: the A054065 row (5,2,4,1,3) gives 10, but (4,2,5,1,3) gives 2 + 3 + 4 + 2 = 11.
For n ≤ 9 the true maxima are 1, 3, 7, 11, 17, 23, 31, 39 = ⌊n²/2⌋ − 1 (A047838), against a(n) = 1, 3, 7, 10, 16,
22, 27, 37.

Lean: [full proof](A100056/A100056_mathlib.lean).

### [A100682](A100682/): exception list of Greathouse's formula is incomplete

**Source.** OEIS [A100682](https://oeis.org/A100682), comment by Charles R Greathouse IV (May 2012):
"Conjecture: a(n) = floor((n − 3/2)/24^(1/4)) for n not in {0, 1, 6, 17, 2403, 5318}."
(OEIS text, CC BY-SA 4.0.)

**Reading.** The entry defines a(n) = floor(C(n+3,4)^(1/4)). With that index the formula is
off by a shift of 3 almost everywhere; the reading that reproduces the stated exceptions
exactly (6, 17, 2403, 5318 below 6000) is floor(C(n,4)^(1/4)) = floor((n − 3/2)/24^(1/4)).
That is the reading used here.

**Result.** False. n = 634027531 (OEIS index 634027528) is a further exception:
floor(C(n,4)^(1/4)) = 286454272 but floor((n − 3/2)/24^(1/4)) = 286454273.
More: 1705327318, 55292025086, … (near continued-fraction convergents of 384^(1/4)).

Lean: [full proof](A100682/A100682_mathlib.lean).

### [A101312](A101312/): other weekday/day pairs do not give a shifted Friday-13th sequence

**Source.** [A101312](https://oeis.org/A101312) (number of Friday the 13ths in year n, from 1901), comment:
"Conjecture: The same basic repeating pattern results if we seek the number of "Sunday the 22nds" or "Wednesday
the 8ths" or anything else similar, with the only difference being that the sequence starts at a different point
in the repeating pattern." (OEIS text, CC BY-SA 4.0.)

**Reading.** "Weekday w on day d" counts per year, compared with the Friday-13th counts up to a shift in years.
Changing d shifts the weekday of day d in every month by the same amount, so every such sequence equals
"weekday u on the 13th" for some u. The question is whether each of these is a year-shift of the Friday sequence.

**Result.** True on 1901–2099 (where the Gregorian calendar agrees with the Julian one and the pattern has period
28: weekday u corresponds to a shift of 20, 8, 24, 12, 0, 16, 4 years for Monday..Sunday). False for the
Gregorian calendar as a whole: over the 400-year cycle no weekday other than Friday gives a cyclic shift of the
Friday sequence. Disputed relative to the scan, which called the full statement trivially true and said the
Gregorian century years "cause the same jumps"; they do not.

**Argument.** On 1901–2099 every fourth year is a leap year, so the (weekday of 1 January, leap) pattern has
period 28, and shifting the year by 12 moves every date's weekday by 12 + 3 = 15 ≡ 1 days; hence any weekday
shift is a time shift. Across a non-leap century year this correspondence breaks; the computation shows that
no shift s (mod 400) satisfies G_u(y) = F(y + s) for all y when u ≠ Friday.

Lean: —.

### [A101462](A101462/): 2^k − 509203 is never prime, so a(42228) does not exist

**Source.** [A101462](https://oeis.org/A101462) (smallest k with 2^k − prime(n) prime), comment:
"Conjecture: sequence is defined for all n. First unproved n: 286 ..." (OEIS text, CC BY-SA 4.0.)

**Result.** False: prime(42228) = 509203 and 2^k − 509203 is never prime.

**Argument.** 509203 is Riesel's number (509203·2^n − 1 is always composite); the same covering works for
2^k − 509203. Classes mod 24: 3 | 2^k − 509203 for k even, 5 for k ≡ 3 (mod 4), 7 for k ≡ 1 (mod 3),
13 for k ≡ 5 (mod 12), 17 for k ≡ 1 (mod 8), 241 for k ≡ 21 (mod 24); these cover all k. For k ≤ 18 the
value is negative, and for k ≥ 19 it is ≥ 15085 > 241.

Lean: [full proof](A101462/A101462_mathlib.lean).

### [A102613](A102613/): π(n)/(n − π(n)) → 0

**Source.** [A102613](https://oeis.org/A102613), comment: "Conjecture: The ratio Pi(x)/(n-Pi(x)) tends to 0 as n
tends to infinity. ... but unfortunately not proof." (OEIS text, CC BY-SA 4.0.)

**Result.** True; a direct consequence of π(n)/n → 0.

**Argument.** π(n)/(n − π(n)) = (π(n)/n)/(1 − π(n)/n), and π(n)/n → 0 (Chebyshev, or an elementary sieve:
the proportion of integers ≤ n coprime to the first k primes tends to ∏(1 − 1/p), which is arbitrarily small).

Lean: [full proof](A102613/A102613_mathlib.lean).

### [A104895](A104895/): positions of k ≥ 0 are A048724(k), positions of −k are A065621(k)

**Source.** [A104895](https://oeis.org/A104895), comment: "Conjecture: the positions where 0, 1, 2, 3, ...
appear are given by A048724; the positions where -1, -2, -3, ... appear are given by A065621." (OEIS text,
CC BY-SA 4.0; still stated on 2026-11-05.)

**Reading.** The %N name line reads "a(0)=0; thereafter a(2n) = -2*a(n), a(2n+1) = 2*a(n) - 1". That
recursion gives a(2) = 2, but the data, the b-file (Sloane, n ≤ 20000) and every program in the entry have
a(2) = −2. The data follow a(0) = 0, a(2n) = 2a(n), a(2n+1) = −2a(n) − 1, which is the negated A065620
recursion (the entry's %F a(n) = −A065620(n)). The name line has its two signs swapped. The result below
is for the sequence as its data define it. A048724(k) = k XOR 2k. A065621(k) = (k−1) XOR (2k−1), a formula
in A065621 equal to its k XOR 2(k − (k AND −k)).

**Result.** True. a(n) = k exactly when n = A048724(k) (k ≥ 0), a(n) = −k exactly when n = A065621(k)
(k ≥ 1), and a is a bijection from ℕ onto ℤ.

**Argument.** Write P = A048724, Q = A065621. XOR of 2x + b and 2y + c is 2(x XOR y) + (b XOR c), so
P(2m) = 2P(m), P(2m+1) = 2Q(m+1) + 1, Q(2m+1) = 2P(m) + 1, Q(2m+2) = 2Q(m+1). Strong induction on k with the
recursion gives a(P(k)) = k and a(Q(k+1)) = −(k+1); for example a(P(2m+1)) = −2a(Q(m+1)) − 1 = 2m + 1.
a is injective: a(2m) is even, a(2m+1) is odd, a(n) = 0 only for n = 0, and a(2m) = a(2m') or
a(2m+1) = a(2m'+1) forces a(m) = a(m'). So each value has exactly one position, the one found above.

Lean: [full proof](A104895/A104895_mathlib.lean).

### [A104896](A104896/): counting integers below 10^n with no digit 0, 1, 2

**Source.** [A104896](https://oeis.org/A104896) (a(0) = 0, a(n) = 7a(n−1) + 7), comment: "Conjecture: this is also
the number of integers from 0 to 10^n - 1 that lack 0, 1 and 2 as a digit." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** 0 has the digit 0; the others are strings of length 1..n over {3, …, 9}: 7 + 7² + … + 7^n,
which satisfies the recurrence.

Lean: [full proof](A104896/A104896_mathlib.lean).

### [A105596](A105596/): the self-convolution with alternating signs is 1 mod 4

**Source.** [A105596](https://oeis.org/A105596) (a(n) = Σ_k A105595(k)(−1)^k A105595(n−k), interpolated zeros
suppressed), comment: "Conjecture : a(2n)=1 mod 4 for all n, a(2n+1)=0 for all n." (OEIS text, CC BY-SA 4.0.)

**Reading.** The indices refer to the unsuppressed convolution c(m) = Σ_{k≤m} (−1)^k b(k) b(m−k), b = A105595;
the printed sequence is c(2n).

**Result.** True, given that every A105595 term is odd (proved in A105595 by B. Gao, Sep 2026).

**Argument.** For odd m the terms k and m − k carry opposite signs and cancel, so c(m) = 0. For m = 2n,
c(2n) = 2Σ_{k<n} (−1)^k b(k) b(2n−k) + (−1)^n b(n)². Each b is odd, so each term of the sum is ±2 (mod 4) and the
sum contributes 2n (mod 4); b(n)² ≡ 1 (mod 8). Hence c(2n) ≡ 2n + (−1)^n ≡ 1 (mod 4).

Lean: [full proof](A105596/A105596_mathlib.lean).

### [A106249](A106249/): roots of x^n + 1 in the left half-plane (index shift by one)

**Source.** [A106249](https://oeis.org/A106249) (expansion of (1−x+x²+x³)/((1+x)(1+x²)(1−x)²), offset 0), comment
by M. Lagneau (2012): "Conjecture: number of roots of x^n + 1 in the left half-plane for n > 0." (OEIS text, CC BY-SA 4.0.)

**Reading.** Literally a(1) = 0 while x + 1 has the root −1; the statement holds with the index shifted:
a(n) = number of roots of x^(n+1) + 1 with negative real part (n ≥ 0). "Left half-plane" is the open one
(x² + 1 has its roots on the imaginary axis and a(1) = 0).

**Result.** True after the shift by one; false as literally indexed.

**Argument.** The roots of x^m + 1 are exp(iπ(2k+1)/m), 0 ≤ k < m, with negative real part iff
m < 2(2k+1) < 3m: the odd integers in (m/2, 3m/2), of which there are 2⌊m/4⌋ + (m mod 2). The g.f. has
denominator 1 − x − x⁴ + x⁵, and a(n) = 2⌊(n+1)/4⌋ + ((n+1) mod 2) satisfies the recurrence and the five
initial values.

Lean: [full proof](A106249/A106249_mathlib.lean).

### [A107363](A107363/): the nonnegative terms are exactly the Fibonacci numbers

**Source.** [A107363](https://oeis.org/A107363) (expansion of (1−x)(1+x)²(1+x²)(1−x²+2x³+x⁴)/((1−x²−x⁴)(1+x²+2x⁴−x⁶+x⁸))),
comment by C. Dement (2005): "Conjectures: { Fib(n) | n in naturals } = { a(n) | n in naturals, a(n) >= 0 } = { a(n) |
n in naturals, n not of the form 6*n+2 } (naturals include 0)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. Also a(6j+2) = −L(3j+1) (the entry's A048876 formula, marked "conjecture").

**Argument.** The denominator multiplies out to 1 − 4x⁶ − x¹², and the numerator has degree 9, so
a(n+12) = 4a(n+6) + a(n). Since F(k+6) = 4F(k+3) + F(k) (likewise for Lucas numbers), each 6-section is fixed by
two initial values: a(6j) = F(3j+2), a(6j+1) = a(6j+3) = F(3j+1), a(6j+2) = −L(3j+1) < 0, a(6j+4) = F(3j+3),
a(6j+5) = 0. These cover every F(i) (F(0) = 0 from the last section).

Lean: [full proof](A107363/A107363_mathlib.lean).

### [A108863](A108863/): Motzkin transform of 0, 0, 0, A001651

**Source.** OEIS [A108863](https://oeis.org/A108863) (Dyck n-paths with exactly one UUUD, offset 0), comment by
R. J. Mathar (Dec 11 2008): "Conjecture: this is the Motzkin transform of the sequence of three zeros followed by
A001651."

**Reading.** Motzkin transform as Mathar describes it in A132894: substitute x → x·M(x) in the g.f., M = Motzkin g.f.
(A001006); coefficientwise a(n) = Σ_{k≤n} b_k [x^n](A108863/xM)^k. b = 0, 0, 0, 1, 2, 4, 5, 7, ... (A001651 = numbers not
divisible by 3, offset 1), with g.f. x³(1+x+x²)/((1−x)(1−x²)). A108863 is represented by the entry's g.f.
G = (x − 1 + (1−2x)M)/(x(1−3x)(1+xM)).

**Result.** True: the Motzkin transform of b has g.f. G, so equals A108863.

**Argument.** Substitution is a ring homomorphism, so with y = xM the transform A satisfies
A(1−y)(1−y²) = y³(1+y+y²). M = 1 + xM + x²M² gives y = x + xy + xy². Then
x(1−y)²·[x(1−3x)(1+y)A − (x − 1 + (1−2x)M)] = x²(1−3x)·[A(1−y)(1−y²) − y³(1+y+y²)] − q·(x + xy + xy² − y)
with q = −3x²y³ + xy³ − 3xy² + 3xy − x + y² − 2y + 1, and x(1−y)² ≠ 0 in the domain ℚ⟦x⟧.

Lean: [full proof](A108863/A108863_mathlib.lean).

### [A110034](A110034/): |row sums| of the Fibonacci–Hankel characteristic polynomials are partial sums of A061646

**Source.** OEIS [A110034](https://oeis.org/A110034) (row sums of A110033, offset 0), comment by J. M. Bergot
(Jun 10 2013): "Conjecture: |a(n)| = Sum_{k=1..n-1} A061646(k)."

**Reading.** A110033 row n: coefficients of the characteristic polynomial det(xI − H_n) of the n×n Hankel matrix
H_n = (F(i+j−1))_{1≤i,j≤n} (row 0 = 1). The row sum is the polynomial at x = 1, det(I − H_n).
A061646 has offset −1: a(−1) = a(0) = a(1) = 1, a(n) = 2a(n−1) + 2a(n−2) − a(n−3).

**Result.** True for every n ≥ 1, with a(n) = −Σ_{k=1..n−1} A061646(k) ≤ 0. False as stated at n = 0:
a(0) = 1 and the sum is empty (0). Corrected statement: n ≥ 1.

**Argument.** F(i+j+1) = F(i)F(j) + F(i+1)F(j+1), so H_n = U Uᵀ with U the n×2 matrix of rows (F(i+1), F(i)),
i = 0..n−1. Weinstein–Aronszajn: det(I − U Uᵀ) = det(I₂ − Uᵀ U)
= (1 − Σ F(i+1)²)(1 − Σ F(i)²) − (Σ F(i)F(i+1))². The sums are F(n)F(n+1), F(n−1)F(n) and F(n)² − [n odd];
A061646(k) = 2F(k)² + (−1)^k; the identity reduces to Cassini's F(m+1)² − F(m)F(m+1) − F(m)² = (−1)^m.

Lean: [full proof](A110034/A110034_mathlib.lean).

### [A110320](A110320/): blocks in RNA secondary structures via Whitney numbers

**Source.** [A110320](https://oeis.org/A110320) (number of blocks in all RNA secondary structures with n nodes),
formula by G. McGarvey (2007): "Conjecture: a(n) = (A051292(n+2)-A051286(n+1))/2." (OEIS text, CC BY-SA 4.0.)

**Result.** True (proved from the combinatorial definitions; the printed g.f.s are also confirmed): A110320 (E. Deutsch), A051286 = 1/R, A051292 = (1 − z² + R)/R with
R = √(1 − 2z − z² − 2z³ + z⁴).

**Argument.** With these g.f.s the difference between Deutsch's g.f. (1−z−z²)/(2z²R) − 1/(2z²) and
Σ_{n≥1} ½(A051292(n+2) − A051286(n+1)) z^n simplifies to 0: the parts with 1/R give
((1 − z²) − z)/(2z²R), and the polynomial parts cancel.

Lean: [full proof](A110320/A110320_mathlib.lean).

### [A110735](A110735/): no digit insertion makes a multiple of 101

**Source.** [A110735](https://oeis.org/A110735) (least multiple of n obtained by inserting one digit in each gap and
at both ends of n; 0 if none), comment: "Conjecture: no term is zero. ..." (OEIS text, CC BY-SA 4.0.)

**Result.** False: a(101) = 0.

**Argument.** The candidates are b1 1 b2 0 b3 1 b4 = b1·10⁶ + 10⁵ + b2·10⁴ + b3·10² + 10 + b4. Modulo 101,
100 ≡ −1, so this is (b2 + b4) − (b1 + b3) + 20 ∈ [2, 38], never 0. The scan's search found 8685 such n below
10^6 (101, 202, 303, 398, 404, …); not re-checked here.

Lean: [full proof](A110735/A110735.lean).

### [A112992](A112992/): ceiling(2^r/3) is a Jacobsthal number or one more

**Source.** [A112992](https://oeis.org/A112992), comment: "Conjecture: the odd values of ceiling(2^(2^k mod k)/3) are
Jacobsthal numbers (and the even values are 1 plus a Jacobsthal number)." (OEIS text, CC BY-SA 4.0.)

**Result.** True, for every exponent r (the form r = 2^k mod k plays no role).

**Argument.** With J(n) = (2^n − (−1)^n)/3: for odd r, ceiling(2^r/3) = (2^r + 1)/3 = J(r), which is odd; for even
r ≥ 2, ceiling(2^r/3) = (2^r + 2)/3 = J(r) + 1, which is even; for r = 0 the value is 1 = J(1).

Lean: [full proof](A112992/A112992.lean).

### [A113249](A113249/): a(m, 2n+1) is a perfect square (the whole family)

**Source.** [A113249](https://oeis.org/A113249) (m = 3 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). R. Israel (2017) showed the m = 3 case in the entry (b(n) = Re((2+√−5)^(n+1))); the m = 8 member A113254 has an AI-generated Lean proof cited in its entry (May 2026). The other members and the all-m statement were open.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².
(For m = 3 this is Israel's b(n).)

**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

Lean: [full proof](A113249/A113249.lean).

### [A113250](A113250/): a(m, 2n+1) is a perfect square (m = 4)

**Source.** [A113250](https://oeis.org/A113250) (m = 4 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².

**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

Lean: [full proof](A113250/A113250.lean).

### [A113251](A113251/): a(m, 2n+1) is a perfect square (m = 5)

**Source.** [A113251](https://oeis.org/A113251) (m = 5 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².

**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

Lean: [full proof](A113251/A113251.lean).

### [A113252](A113252/): a(m, 2n+1) is a perfect square (m = 6)

**Source.** [A113252](https://oeis.org/A113252) (m = 6 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².

**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

Lean: [full proof](A113252/A113252.lean).

### [A113253](A113253/): a(m, 2n+1) is a perfect square (m = 7)

**Source.** [A113253](https://oeis.org/A113253) (m = 7 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².

**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

Lean: [full proof](A113253/A113253.lean).

### [A113255](A113255/): a(m, 2n+1) is a perfect square (m = 9)

**Source.** [A113255](https://oeis.org/A113255) (m = 9 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².

**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

Lean: [full proof](A113255/A113255.lean).

### [A113256](A113256/): a(m, 2n+1) is a perfect square (m = 10)

**Source.** [A113256](https://oeis.org/A113256) (m = 10 member of C. Dement's family a(m,n) = m⁴a(n−4) + (2m)²a(n−3) − 4a(n−1),
a(0) = −1, a(1) = 4, a(2) = −13 + 6(m−1) + 3(m−1)², a(3) = (m² − 8)²), comment: "Conjecture: a(m, 2*n+1) is a perfect
square for all m, n" (OEIS text, CC BY-SA 4.0). The entry points to A113249 for the family.

**Result.** True for every integer m: a(m, 2n+1) = y(m, n)² with y(n) = 4y(n−1) − m²y(n−2), y(0) = 2, y(1) = 8 − m².

**Argument.** The characteristic polynomial of a is (x² − m²)(x² + 4x + m²). The odd-index subsequence
s(n) = a(2n+1) satisfies the recurrence with characteristic polynomial (X − m²)²(X² + (2m² − 16)X + m⁴) (the roots
squared). y has roots u, v with u + v = 4, uv = m², so y² satisfies (X − m²)(X² + (2m² − 16)X + m⁴), a divisor of the
first polynomial, hence the same order-4 recurrence. The first four values agree as polynomials in m, so
s(n) = y(n)² for all n, uniformly in m.

Lean: [full proof](A113256/A113256.lean).

### [A113610](A113610/): local minima of composite digit sums do not mark twin primes

**Source.** [A113610](https://oeis.org/A113610) (sum of the digits of all composites strictly between prime(n) and
prime(n+1)), comment: "Conjecture: For n > 9 if a(n) > a(n+1) < a(n+2) then prime(n) and prime(n+1) form a twin
prime pair." (OEIS text, CC BY-SA 4.0.)

**Result.** False, in the literal reading and in the variant where the local minimum a(n+1) belongs to a twin gap.

**Argument.** n = 12: a(12) = 27 > a(13) = 6 < a(14) = 27 (composites 38, 39, 40 | 42 | 44, 45, 46), but
prime(12) = 37, prime(13) = 41 are not twins. Variant (prime(n+1), prime(n+2) twins): n = 21 has
a(21) = 65 > a(22) = 27 < a(23) = 70, with prime(22) = 79, prime(23) = 83. Below 10^5 there are 3194 literal and
1981 variant failures.

Lean: [full proof](A113610/A113610.lean).

### [A114534](A114534/): the Fibonacci matrix has rank 2

**Source.** [A114534](https://oeis.org/A114534) (permanent of the n × n matrix M filled row by row with Fibonacci
numbers), comment: "Conjecture: The rank of the matrix M is 2 for every n." (OEIS text, CC BY-SA 4.0.)

**Reading.** The entries are F(0), F(1), …, F(n² − 1) (this reproduces a(2) = 1 and a(3) = 132), and n ≥ 2 (the
offset).

**Result.** True.

**Argument.** M(r, c) = F(rn + c). The addition formula gives F(a + c) = F(a)·(F(c+1) − F(c)) + F(a+1)·F(c), so
every row is a combination of the two rows (F(c+1) − F(c))_c and (F(c))_c: rank ≤ 2. The minor on rows 0, 1 and
columns 0, 1 is F(0)F(n+1) − F(1)F(n) = −F(n) ≠ 0: rank ≥ 2.

Lean: [full proof](A114534/A114534_mathlib.lean).

### [A115038](A115038/): every prime is y^k − x^2

**Source.** [A115038](https://oeis.org/A115038) (smallest x with x² + prime(n) a perfect power), comment:
"Conjecture: There will always be an x,y,n such that x^2 + p = y^n for all primes p. ..." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial (squares count as perfect powers, as the entry's data shows).

**Argument.** For odd p, ((p−1)/2)² + p = ((p+1)/2)²; for p = 2, 5² + 2 = 3³.

Lean: [full proof](A115038/A115038.lean).

### [A123722](A123722/): multiples of 3 in the list are 3 and 3p (p prime), and every odd prime occurs

**Source.** OEIS [A123722](https://oeis.org/A123722) (J. W. Layman, 2006): values of n with
A000224(n) = ⌈(n+1)/3⌉, where A000224(n) is the number of squares mod n (1, 3, 4, 8, 9, 15, 21,
33, ...; offset 1). Comment: "If n>2 and a(n) is a multiple of 3, then a(n)/3 is a prime;
further, all odd primes are given as a(n)/3 for some n." (OEIS text, CC BY-SA 4.0.)

**Reading.** ⌈(n+1)/3⌉ = ⌊n/3⌋ + 1. Since a(1) = 1 and a(2) = 3, "n > 2" means a(n) > 3.

**Result.** Proved, both parts.

**Argument.** Let S(n) = A000224(n).
1. S is multiplicative on coprime arguments (Chinese remainder theorem).
2. S(m) ≤ ⌊m/2⌋ + 1 because x and m − x have the same square. If d² | m with d ≥ 2, then 0 and
   m/d also share a square (both square to 0), so S(m) ≤ ⌊m/2⌋.
3. For an odd prime p, x² ≡ y² (mod p) with 0 ≤ x, y ≤ (p−1)/2 forces x = y, so 2S(p) = p + 1.
4. Take m odd with 2S(m) = m + 1. Then m = 1 or m is prime. Otherwise let p = minFac(m). If
   p² | m, step 2 gives a contradiction. If not, m = p·b with b ≥ 2 coprime to p, and
   4S(p)S(b) ≤ (p+1)(b+1) < 2(pb+1).
5. If M | N then S(N) ≤ S(M)·N/M, since every square mod N reduces to a square mod M. With
   S(9) = 4 this gives S(3^k) ≤ 4·3^(k−2).
6. For k ≥ 3, squaring is injective on {3j+1 : j < 3^(k−1)} mod 3^k: 3^k divides
   3(i−j)(3(i+j)+2) and the last factor is prime to 3. Adding the squares 0 and 9 gives
   S(3^k) ≥ 3^(k−1) + 2.
7. Classification. Write N = 3^k·r with 3 ∤ r and S(N) = N/3 + 1.
   - k = 1: 2S(r) = r + 1. So r is odd (by parity), and step 4 gives r = 1 (N = 3) or r prime.
   - k ≥ 2 and r ≥ 4: steps 2 and 5 give 2S(N) ≤ 4·3^(k−2)(r+2) < 2·3^(k−1)r + 2.
   - k ≥ 2 and r = 2: S(N) = 2S(3^k) is even, but 2·3^(k−1) + 1 is odd.
   - k ≥ 2 and r = 1: step 6 rules out k ≥ 3, leaving N = 9 = 3·3.
8. Every odd prime occurs: S(9) = 4, and S(3p) = 2·(p+1)/2 = p + 1 for primes p ≥ 5.

The c(q^e) = q^e trap from the sibling OEIS-A123365 does not arise. Steps 5 and 6 use only
bounds valid for every exponent, never exact prime-power values.

Lean: [full proof](A123722/A123722_mathlib.lean).

### [A123723](A123723/): multiples of 4 in the list, other than 4, are 4p with p prime

**Source.** OEIS [A123723](https://oeis.org/A123723) (J. W. Layman, 2006): values of n with
A000224(n) = ⌈(n+1)/4⌉ (1, 4, 8, 12, 20, 28, 44, 45, ...; offset 1). Comment: "If n>4 and a(n)
is a multiple of 4, then a(n)/4 is a prime." (OEIS text, CC BY-SA 4.0.)

**Reading.** ⌈(n+1)/4⌉ = ⌊n/4⌋ + 1. Since a(4) = 12, "n > 4" means a(n) > 12. The proof covers
every multiple N ≠ 4, including N = 8 = 4·2.

**Result.** Proved.

**Argument.** The general lemmas are those of [A123722](A123722/README.md): S is
multiplicative, S(m) ≤ ⌊m/2⌋ + 1, odd m with 2S(m) = m + 1 is 1 or prime, and S(N) ≤ S(M)·N/M
for M | N. Write N = 2^j·r with r odd and j ≥ 2, and S(N) = N/4 + 1.
- j = 2: 2S(r) = r + 1, so r is prime (r = 1 gives N = 4).
- j = 3: 3S(r) = 2r + 1 and 2S(r) ≤ r + 1 force r = 1, so N = 8 and N/4 = 2.
- j ≥ 4 and r ≥ 3: squares mod 8 are 0, 1, 4, so S(2^j) ≤ 3·2^(j−3). That makes
  2S(N) ≤ 3·2^(j−3)(r+1), which is less than 2^(j−1)r + 2.
- j ≥ 4 and r = 1: S(16) = 4 ≠ 5. For j ≥ 5, mod 32 has 7 squares, so
  S(2^j) ≤ 7·2^(j−5) < 2^(j−2) + 1.

Lean: [full proof](A123723/A123723_mathlib.lean).

### [A124431](A124431/): Mathar's recurrence for Σ 2^k C(⌊(n+k)/2⌋, k) C(⌊(n+k+1)/2⌋, k)

**Source.** OEIS [A124431](https://oeis.org/A124431) (offset 0): a(n) = Sum_{k=0..n}
2^k*C([(n+k)/2],k)*C([(n+k+1)/2],k): 1, 3, 9, 29, 97, 331, 1145, ... Conjecture (R. J. Mathar, Aug 2012,
repeated Jun 2016): "(n+1)*a(n) -2*(2*n+1)*a(n-1) +2*(n-1)*a(n-2) +2*(5-2*n)*a(n-3) +(n-3)*a(n-4) =0."
(OEIS text, CC BY-SA 4.0; both copies still marked "Conjecture" on 2026-11-05, revision #41.)

**Result.** True for every n ≥ 4.

**Argument.** Group the summands k = n − 2i (n + k even) and k = n + 1 − 2i (n + k odd). With
C(p, n−2i) = C(p, i) this gives a(n) = Σ_{i=0}^{n+1} w(n, i),
w(n, i) = 2^(n−2i) (C(n−i, i)² + 2 C(n−i, i−1) C(n−i+1, i)), a hypergeometric term in (n, i) with no
floors. Let F(n, i) = Σ_{l=0}^{4} c_l(n) w(n−l, i) with Mathar's coefficients
c = (n+1, −2(2n+1), 2(n−1), 2(5−2n), n−3). Creative telescoping: with
G(n, i) = 2^(n−2i) [ (1+4i) X₀₀² − 6i X₀₀X₀₁ − 4i X₀₁² − (2+5i) X₀₀X₁₀ − ½ X₀₀X₂₀ + (½ − i/4) X₀₀X₃₀ + X₁₀²
+ (3i/4) X₁₀X₂₀ − (i/2) X₁₀X₃₀ + (¼ + 2i) X₂₀² − (5i/4) X₂₀X₃₀ + (i/4 − ¼) X₃₀² ], X_ab = C(n−i−a, i−b),
one has F(n, i) = G(n, i+1) − G(n, i). This is checked by writing every binomial as
C(n−i+1, i) times a rational function of (n, i) (contiguous relations) and verifying one rational-function
identity. Summing over 0 ≤ i ≤ n+1 gives Σ_l c_l(n) a(n−l) = G(n, n+2) − G(n, 0) = 0 (all binomials vanish
at i = n+2; at i = 0 the coefficients cancel). The identity needs (n−i+1)(n−i)…(n−i−3) ≠ 0; for n ≥ 8 the
other i have 2i ≥ n + 2, where every term is 0. n = 4..7 by direct computation.
G was found by fitting such binomial products with coefficients of degree ≤ 1 to the partial sums
Σ_{i'<i} F(n, i') (`certificate/find_certificate.py`).

Lean: [full proof](A124431/A124431_mathlib.lean).

### [A125148](A125148/): every x coprime to 10 has a prime x + 10m

**Source.** [A125148](https://oeis.org/A125148), comment: "Conjecture: for every odd (prime or nonprime) number x>=1
that is not a multiple of 5 there exists a prime p such that p = z + x; where z is a multiple of 10."
(OEIS text, CC BY-SA 4.0.)

**Result.** True, by Dirichlet's theorem.

**Argument.** gcd(x, 10) = 1, so there are infinitely many primes p ≡ x (mod 10); any such p ≥ x gives
z = p − x, a nonnegative multiple of 10 (positive if one takes p > x, as the entry's terms do).

Lean: [full proof](A125148/A125148_mathlib.lean).

### [A126142](A126142/): squares of the terms are 6k+1 (trivial)

**Source.** OEIS [A126142](https://oeis.org/A126142) (primes p whose square has a prime
digit sum), comment by Vincenzo Librandi (2009): "a(n)^2 is of the form 6*k+1."
(OEIS text, CC BY-SA 4.0.) The entry already adds (Berselli 2014) that this is trivially true.

**Result.** True (trivial). Every n with gcd(n, 6) = 1 has n^2 ≡ 1 (mod 24), hence
n^2 ≡ 1 (mod 6). All terms are primes ≥ 5 (a(1) = 5), so gcd(a(n), 6) = 1.

**Argument.** n odd and 3 ∤ n: n^2 ≡ 1 (mod 8) and n^2 ≡ 1 (mod 3); equivalently check the
eight residues mod 24 prime to 6.

Lean: [full proof](A126142/A126142_mathlib.lean).

### [A129454](A129454/): p-adic valuation of a triple gcd product (true after an index shift)

**Source.** OEIS [A129454](https://oeis.org/A129454): a(n) = Product_{i,j,k=1..n-1} gcd(i,j,k)
(offset 0; data 1, 1, 1, 2, 6, 1536, ...). Conjecture: "ordp(a(n),p) =
(floor(n/p))^3 + (floor(n/p^2))^3 + (floor(n/p^3))^3 + ...". (OEIS text, CC BY-SA 4.0.)

**Reading.** With the products running over 1..n-1 as in the current %N line, the literal
formula is off by one: a(3) = gcd(2,2,2) = 2, while the formula gives v_3(a(3)) = 1. The
formula is exactly right with n - 1 in place of n, i.e. for the product over 1..n (the form used in
the related A092287). The scan recorded this as proved "up to the index shift"; that is the
statement proved here.

**Result.** For every prime p and n ≥ 1, v_p(a(n)) = sum_{t≥1} floor((n-1)/p^t)^3. As printed
(with floor(n/p^t)) it fails, first at n = 2, p = 2 and n = 3, p = 3.

**Argument.** v_p(gcd(i,j,k)) = sum_{t≥1} [p^t | i, p^t | j, p^t | k]. Summing over
1 ≤ i, j, k ≤ N gives sum_t (number of multiples of p^t up to N)^3 = sum_t floor(N/p^t)^3,
with N = n - 1.

Lean: [full proof](A129454/A129454_mathlib.lean).

### [A129756](A129756/): roots of x^n − x^(n−1) − … − x − 1 in the right half-plane

**Source.** [A129756](https://oeis.org/A129756) (offset 0), "Repetitions of odd numbers four times",
a(n) = 1 + 2⌊n/4⌋. Comment (Michel Lagneau, Apr 09 2013): "Conjecture: number of roots of P(x) = x^n - x^(n-1) -
x^(n-2) - ... - x - 1 in the right half-plane." (OEIS text, CC BY-SA 4.0; revision #54, checked 2026-11-06.)
The companion entry [A083219](https://oeis.org/A083219) (a(n) = n − 2⌊n/4⌋) carries the same conjecture for the
left half-plane.

**Reading.** With the entry's offset 0 the index is shifted by one: the polynomial of degree n has 1 root with
positive real part for n = 1..4 and 3 for n = 5..8, i.e. a(n−1), not a(n) (a(4) = 3). So the statement holds as
"a(n) = number of roots of x^(n+1) − x^n − … − x − 1 with Re > 0" (counted with multiplicity; the roots are simple
anyway). No root lies on the imaginary axis, so "right half-plane" open or closed gives the same count.

**Result.** True with that index: for n ≥ 1, x^n − x^(n−1) − … − 1 has exactly 1 + 2⌊(n−1)/4⌋ roots with positive
real part and n − 1 − 2⌊(n−1)/4⌋ with negative real part (the A083219 comment, same shift).

**Argument.** Let P(z) = z^n − Σ_{j<n} z^j and Q(z) = (z − 1)P(z) = z^(n+1) − 2z^n + 1; Q has one more root (z = 1)
with positive real part than P.
1. *Q on the imaginary axis.* For real y, i^n(iy − 2) is iy − 2, −y − 2i, 2 − iy, y + 2i for n ≡ 0, 1, 2, 3 (mod 4),
   so Im Q(iy) = y^(n+1), −2y^n, −y^(n+1), 2y^n and Re Q(iy) = 1 − 2y^n, 1 − y^(n+1), 1 + 2y^n, 1 + y^(n+1).
   Hence Q(iy) is real only at y = 0, where Q(0) = 1. So Q has no imaginary root, and Q(iy) never meets (−∞, 0];
   arg Q(iy) (principal value) is continuous in y, and arg Q(−iy) = −arg Q(iy) (real coefficients).
2. *Argument through the roots.* Q(iy) = Π_r (iy − r) over the n + 1 roots r = a + bi (a ≠ 0). A continuous argument
   of iy − r = −a + i(y − b) is θ_r(y) = arctan((y − b)/(−a)), plus π when a > 0. The difference
   arg Q(iy) − Σ_r θ_r(y) is continuous with values in 2πℤ, so it is constant. Comparing y = Y and y = −Y:
   2 arg Q(iY) = Σ_r [θ_r(Y) − θ_r(−Y)].
3. *Y → ∞.* θ_r(Y) − θ_r(−Y) → π if a < 0 and → −π if a > 0. So 2 arg Q(iY) → π(N_L − N_R), where N_L + N_R = n + 1.
4. *Quadrant.* For Y > 1 the signs in step 1 put 2 arg Q(iY) in [π, 2π], [−2π, −π], [−π, 0], [0, π] for
   n ≡ 0, 1, 2, 3 (mod 4). So N_L − N_R lies in [1, 2], [−2, −1], [−1, 0], [0, 1], and its parity is that of n + 1.
   Hence N_L − N_R = 1, −2, −1, 0, i.e. N_R(Q) = 2m, 2m + 2, 2m + 2, 2m + 2 for n = 4m, 4m + 1, 4m + 2, 4m + 3.
   Subtracting the root z = 1: N_R(P) = 1 + 2⌊(n − 1)/4⌋.
This is the argument principle along the imaginary axis, done factor by factor so that only arctan limits are needed.

Lean: [full proof](A129756/A129756_mathlib.lean).

### [A133212](A133212/): a(n) = 2*A038503(n+3) for n > 0

**Source.** OEIS [A133212](https://oeis.org/A133212): a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3)
for n > 3, a(0..3) = 1, 4, 12, 32. Conjecture (R. J. Mathar, 2007): "a(n)=2*A038503(n+3) if
n>0." (OEIS text, CC BY-SA 4.0.) A038503(m) = sum_k C(m, 4k).

**Result.** True.

**Argument.** Roots-of-unity filter: A038503(m) = (2^m + (1+i)^m + (1-i)^m + 0^m)/4. For
m ≥ 1 the 0^m term vanishes, so b(m) = A038503(m) satisfies the recurrence with
characteristic polynomial (x - 2)(x^2 - 2x + 2) = x^3 - 4x^2 + 6x - 4 for m ≥ 4. Hence
n ↦ 2b(n+3) and a(n) satisfy the same order-3 recurrence for n ≥ 4, and both equal 4, 12, 32 at
n = 1, 2, 3. (At n = 0 they differ: a(0) = 1, 2b(3) = 2, matching "if n > 0".)

Lean: [full proof](A133212/A133212_mathlib.lean).

### [A134002](A134002/): n(n+5) = a(a+5) + b(b+5) is solvable iff n^2 + (n+5)^2 is composite

**Source.** OEIS [A134002](https://oeis.org/A134002): positive n such that
n(n+5) = a(a+5) + b(b+5) is solvable in positive integers. Conjecture (Layman, 2007): "If n a
positive integer not a term of this sequence, then n^2+(n+5)^2 is prime." (OEIS text,
CC BY-SA 4.0.)

**Result.** True, and the converse holds as well: with M = n^2 + (n+5)^2, the equation has a
solution in positive integers iff M is composite (see also OEIS-A134003).

**Argument.** Multiply by 4 and add 50: 2M = (2n+5)^2 + 5^2, and a solution is the same as
2M = X^2 + Y^2 with X = 2a+5, Y = 2b+5 odd and ≥ 7. M is odd (n and n+5 have opposite
parity). Representations 2M = X^2 + Y^2 with X ≥ Y ≥ 1 correspond to M = u^2 + v^2 with
u > v ≥ 0 via X = u+v, Y = u-v. The trivial one is (u, v) = (n+5, n), i.e. {2n+5, 5}.
- M prime: the representation of a prime as a sum of two squares is unique, so 2M has only
  {2n+5, 5}; Y = 5 means b = 0. No solution.
- 5 ∤ n, M composite: gcd(n, n+5) = 1, so every prime factor of M is ≡ 1 (mod 4) and
  r_2(M) = 4 d(M) ≥ 12. Counting (u, v) with u > v ≥ 0 gives at least 2 representations of M
  (d(M) ≥ 4 if M is not a square, d(M) ≥ 3 and the extra (√M, 0) if it is). The second one
  gives {X, Y} ≠ {2n+5, 5}; Y ≠ 5 (else X = 2n+5); Y = 1 or 3 would make (2n+5)^2 + 24 or
  (2n+5)^2 + 16 a square, impossible for n ≥ 1 (factor the difference of squares). So X, Y ≥ 7.
  (M = p^2 gives X = Y = p, i.e. a = b = (p-5)/2 ≥ 4.)
- n = 5m: 2M = 25((2m+1)^2 + 1) = (6m+7)^2 + (8m+1)^2, so a = 3m+1, b = 4m-2 ≥ 2; and
  M = 25(m^2 + (m+1)^2) is composite.

Lean: [full proof](A134002/A134002_mathlib.lean).

### [A134003](A134003/): n(n+5) = a(a+5) + b(b+5) has no positive solution when n^2 + (n+5)^2 is prime

**Source.** OEIS [A134003](https://oeis.org/A134003) (n with n^2 + (n+5)^2 prime). Conjecture
(Layman, 2007): "If n is in this sequence then n(n+5)=a(a+5)+b(b+5) is not solvable in
integers." (OEIS text, CC BY-SA 4.0.)

**Reading.** Literally ("in integers") it is false for every n: a = n, b = 0 is a solution (and
b = -5 as well). The intended reading, matching the definition of the complementary A134002, is
positive integers a, b.

**Result.** True for positive a, b; false as literally worded.

**Argument.** As in OEIS-A134002: 2M = (2n+5)^2 + 5^2 with M = n^2 + (n+5)^2, and a positive
solution is a representation 2M = X^2 + Y^2 with X, Y odd ≥ 7. For M prime the only
representation of 2M is {2n+5, 5} (uniqueness of the two-squares representation of the prime M,
transported by X = u+v, Y = u-v), so there is none.

Lean: [full proof](A134003/A134003_mathlib.lean).

### [A135499](A135499/): equal digit sums at odd and even positions implies 11 | n (trivial)

**Source.** OEIS [A135499](https://oeis.org/A135499): numbers whose digit sum at odd positions
equals the digit sum at even positions. Conjecture (Mathar, 2008): "this is a subsequence of
A008593" (multiples of 11). (OEIS text, CC BY-SA 4.0.) The entry already records that it follows
from the divisibility rule for 11 (Seidov 2008, Andersen 2014).

**Result.** True (trivial).

**Argument.** Let f(n) = (sum of digits at even positions from the right, counting from 0) minus
(sum at odd positions). Since 10 ≡ -1 (mod 11), n ≡ f(n) (mod 11). Equal sums means f(n) = 0
(the choice of counting from the left or right only swaps the two sums).

Lean: [full proof](A135499/A135499.lean).

### [A135571](A135571/): differences of two positive triangular numbers in an odd number of ways

**Source.** OEIS [A135571](https://oeis.org/A135571): positive integers that are the difference of
two positive triangular numbers in an odd number of ways. Conjecture: "This sequence is just the
sequence of positive integers that are either square, twice a square, or triangular, but not both
square and triangular (A001110)." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** T(a) - T(b) = (a-b)(a+b+1)/2. Put d = a - b ≥ 1 and e = a + b + 1, so 2n = d e with d,
e of opposite parity and e > d. Conversely each such factorisation gives a, b ≥ 0. Factorisations
2n = d e with d < e of opposite parity correspond to the odd divisors of n (the odd one of d, e is
an odd divisor of n, and the pair is determined by it), so there are d_odd(n) of them. b = 0 means
e = d + 1, i.e. 2n = d(d+1), which happens (once) iff n is triangular. So the number of
representations with b ≥ 1 is r(n) = d_odd(n) - [n triangular].
d_odd(n) = d(odd part of n) is odd iff the odd part is a square iff n is a square or twice a
square. Hence r(n) is odd iff exactly one of "n is a square or twice a square" and "n is
triangular" holds. A twice-square is never triangular (k(k+1)/2 = 2m^2 means k(k+1) = (2m)^2, a
product of consecutive positive integers, which is never a square), and no n is both a square and
twice a square. So r(n) is odd iff n is a square, twice a square, or triangular, but not both a
square and triangular: the conjectured set.

Lean: [full proof](A135571/A135571_mathlib.lean).

### [A135659](A135659/): every Mersenne prime > 3 is ≡ 7 (mod 24)

**Source.** OEIS [A135659](https://oeis.org/A135659) (a(n) = 24n + 7). Conjecture: "All Mersenne
Primes (A000668) > 3 are in this sequence." (OEIS text, CC BY-SA 4.0.)

**Result.** True (elementary).

**Argument.** If 2^n - 1 > 3 is not divisible by 3, then n is odd (for even n, 3 | 4^(n/2) - 1)
and n ≥ 3. For odd n ≥ 3, 2^n ≡ 0 (mod 8) and 2^n ≡ 2 (mod 3), so 2^n ≡ 8 (mod 24) and
2^n - 1 ≡ 7 (mod 24). A Mersenne prime > 3 is not divisible by 3.

Lean: [full proof](A135659/A135659.lean).

### [A137328](A137328/): the prime 2 never occurs

**Source.** OEIS [A137328](https://oeis.org/A137328): a(n) = prime(n) - primorial(k), k maximal
with primorial(k) ≤ prime(n). Conjecture: "Each prime number appears in this sequence at least
once." (OEIS text, CC BY-SA 4.0.)

**Result.** False: 2 is never a term. For odd primes the statement is open; every odd prime
q < 10^6 occurs.

**Argument.** For every prime p, primorial(1) = 2 ≤ p, so the maximal k is ≥ 1 and the subtracted
primorial P is even and ≥ 2. If p - P = 2 then p = P + 2 is even and ≥ 4, so not prime.
For an odd prime q to occur one needs k with p_k < q (otherwise q | P + q), P + q prime, and
P + q < primorial(k+1), i.e. q < P (p_(k+1) - 1); this is a finite search per q.

Lean: [full proof](A137328/A137328_mathlib.lean).

### [A139043](A139043/): sum of composites ≤ 10^n versus 10^n(10^n+1)/2 - 1 - (10^n)^2/(2 log 10^n - 1)

**Source.** OEIS [A139043](https://oeis.org/A139043): a(n) = sum of the composite numbers ≤ 10^n.
Conjecture (Cino Hilliard, 2008): "10^n(10^n+1)/2 - 1 -(10^n)^2/(2*log(10^n)-1) -> a(n) as n ->
infinity. Here (10^n)^2/(2*log(10^n)-1) is also conjectured to -> sum of primes < 10^n ..."
(OEIS text, CC BY-SA 4.0.)

**Reading.** "→" can mean asymptotic equivalence (ratio → 1) or difference → 0. With x = 10^n and
S(x) = sum of primes ≤ x, a(n) = x(x+1)/2 - 1 - S(x), so the left side minus a(n) equals
S(x) - x^2/(2 log x - 1).

**Result.** - Ratio reading: true. For the main statement it is immediate (both sides are ~ x^2/2, since
  S(x) ≤ x π(x) = o(x^2)); for the parenthetical statement S(x) ~ x^2/(2 log x - 1) it is the
  prime number theorem.
- Difference reading: false for both. S(x) - x^2/(2 log x - 1) ~ x^2/(8 log^3 x) → ∞.

**Argument.** By the PNT with the de la Vallée Poussin error term and partial summation,
S(x) = li(x^2) + O(x^2 exp(-c √(log x))). With L = log x, li(x^2) = x^2/(2L) + x^2/(4L^2) +
x^2/(4L^3) + O(x^2/L^4), while x^2/(2L - 1) = x^2/(2L) + x^2/(4L^2) + x^2/(8L^3) + O(x^2/L^4).
The difference is x^2/(8L^3)(1 + o(1)). (The scan argued failure of the difference reading from
oscillation of the error term; the third-order term gives it directly.)

Lean: [witness](A139043/A139043_mathlib.lean).

### [A140869](A140869/): if h is not a term, then 4h + 5 is prime

**Source.** OEIS [A140869](https://oeis.org/A140869): triangle T(m,n) = floor((2mn+m+n-2)/2),
m ≥ n ≥ 1. Conjecture (Librandi, 2012): "If h does not belong to the sequence, then 4*h+5 is
prime." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Contrapositive. If 4h + 5 = d e with d, e > 1, both are odd, d = 2a+1, e = 2b+1 with
a, b ≥ 1, and 4ab + 2a + 2b + 1 = 4h + 5. So a + b is even and h = ab + (a+b)/2 - 1 =
floor((2ab + a + b - 2)/2) = T(max, min).

Lean: [full proof](A140869/A140869.lean).

### [A144652](A144652/): if h is not a term, then 4h + 1 is prime (h ≥ 1)

**Source.** OEIS [A144652](https://oeis.org/A144652): triangle T(m,n) = floor((2mn+m+n)/2),
m ≥ n ≥ 1. Conjecture (Librandi, 2012): "If h does not belong to the sequence, then 4*h+1 is
prime." (OEIS text, CC BY-SA 4.0.)

**Reading.** h ranges over positive integers. For h = 0 (not a term) 4h + 1 = 1 is not prime.

**Result.** True for h ≥ 1.

**Argument.** Contrapositive. If 4h + 1 = d e with d, e > 1, then d = 2a+1, e = 2b+1 with
a, b ≥ 1 and 4ab + 2a + 2b + 1 = 4h + 1, so a + b is even and h = ab + (a+b)/2 = T(max, min).

Lean: [full proof](A144652/A144652.lean).

### [A152718](A152718/): inverse Motzkin transform of A054393

**Source.** [A152718](https://oeis.org/A152718) (offset 0), R. J. Mathar, Dec 11 2008: a(n) = 2a(n-1) - a(n-2) +
2a(n-3) - a(n-4) + a(n-5) for n > 5, with a(0..5) = 1, 1, 1, 1, 2, 4. Comment: "Conjecture: this is the inverse
Motzkin transform of A054393." G.f. 1 + x(-1 + x + x^3)/(-1 + 2x - x^2 + 2x^3 - x^4 + x^5) (Mathar, 2016).
[A054393](https://oeis.org/A054393) (Sloane and Pergola, 2000) counts permutations with certain forbidden
subsequences (Barcucci et al., "From Motzkin to Catalan permutations", Discrete Math. 217 (2000) 33-49); its
Mathematica program (Alcover, 2018) gives a(n) = (M^n)[1,1] for the n x n 0/1 matrix with M[i,j] = 1 iff j < i,
or i = j <= 5, or j = i+1. (OEIS text, CC BY-SA 4.0, revisions #21 of A152718 and #29 of A054393, checked
2026-11-06.)

**Reading.** Mathar uses "inverse Motzkin transform" for the substitution x -> x/(1+x+x^2) in the g.f. (see his
comments in A097861, A109196, A147691); equivalently A054393(x) = A152718(z) with z = x M(x), M the Motzkin
series, so z = x(1 + z + z^2). In coefficients: A054393(n) = sum_{k=0..n} A152718(k) [x^n] z^k. The matrix power
counts walks of length n on levels 1, 2, ... from level 1 back to level 1; a step goes up one level, drops to any
lower level, or stays put, staying only at levels 1..5 (levels 0..4 below). A walk of length n never goes above
level n/2 + 1, so the n x n truncation loses nothing.

**Result.** True: A054393(x) = A152718(x M(x)) as formal power series, so A152718 is the inverse Motzkin transform
of A054393.

**Argument.** Number the levels 0, 1, 2, ... and let E_h(x) count excursions at level h (walks from h back to h
that never go below h), G_h(x) count walks from h staying at or above h and ending anywhere.

1. *Decomposition.* An excursion at h is a sequence of loops at h (allowed iff h <= 4) and of arches: an up step to
   h+1, a walk counted by G_{h+1}, and one drop back to h. So E_h = 1/(1 - [h <= 4] x - x^2 G_{h+1}). Cutting a walk
   from h at its last visit to h gives G_h = E_h (1 + x G_{h+1}).
2. *Top levels.* For h >= 5 there are no loops, so E_h = E, G_h = G for all h >= 5. With no loops at all levels but
   one loop allowed at the base, the excursion series is the Motzkin series: 1/(1 - x - x^2 G) = M, which gives
   x^2 G = 1 - x - 1/M = x^2 M (from M = 1 + xM + x^2 M^2), i.e. G = M = z/x.
3. *Levels 4..0.* With x = z/(1+z+z^2): E_4 = 1/(1 - x - x^2 M) = M = 1+z+z^2, G_4 = M(1+z);
   E_3 = 1/(1-z); E_2 = (1-z)(1+z+z^2)/(1-z-z^3); E_1 = (1-z-z^3)/(1-2z+z^2-z^3); and
   E_0 = (1+z+z^2)(1-2z+z^2-z^3)/(1-2z+z^2-2z^3+z^4-z^5) = (1-z-2z^3-z^5)/(1-2z+z^2-2z^3+z^4-z^5).
4. *Comparison.* The last expression is Mathar's g.f. of A152718 evaluated at z, and E_0 is the g.f. of A054393.

The Lean proof runs the argument backwards, which avoids infinite sums of series: it defines candidate series
V_j (walks from 0 ending at level j: V_j = X^j U_j with U_j explicit rational expressions in z, and
U_{j+1}/U_j = (1+z+z^2)/(1+z) for j >= 4) and tails T_j (= sum_{i>j} V_i), checks that they satisfy the
dynamic-programming equations of the walk count (polynomial identities in z, u^{-1}, (1+z)^{-1}, Q(z)^{-1} with
explicit cofactors), and concludes by induction on the length that their coefficients are the walk counts.

Lean: [full proof](A152718/A152718_mathlib.lean).

### [A164754](A164754/): a(n) = 4n^2 - 11n + 5 for n >= 3

**Source.** [A164754](https://oeis.org/A164754) (offset 2), R. H. Hardin, Aug 24 2009: number of n X 2 arrays with
entries 1..4, each value's cells connected, 1, 2, 3, 4 in the upper left, upper right, lower left and lower right
corners, "and with no element having more than 2 neighbors with the same value". Formulas in the entry, all marked
empirical: a(n) = 3a(n-1) - 3a(n-2) + a(n-3) for n >= 6, the g.f. x^2(1 + 5x + 4x^2 - 2x^3)/(1 - x)^3 (Colin
Barker, 2018), and a(n) = 4(n-2)^2 + 5(n-2) - 1 for n >= 3 (Bill McEachen, 2020). The scan record quotes an older
form, "Except for the first term, a(n)=4*n^2+13*n+8" (Vincenzo Librandi, May 26 2010), which is the same polynomial
with n shifted by 3. (OEIS text, CC BY-SA 4.0, revision #35 of Sep 01 2020, checked 2026-11-05.)

**Reading.** Rows 1..n, columns L (left) and R (right); neighbours are the 4-neighbours (same row other column, or
same column adjacent row), so a cell has at most 3 neighbours. "Connected" means connected under this adjacency.
Corners: (1,L) = 1, (1,R) = 2, (n,L) = 3, (n,R) = 4. This reading reproduces a(2..7) = 1, 8, 25, 50, 83, 124 by
brute force over all arrays (certificate/brute.py). Librandi's 4n^2 + 13n + 8 is the formula in the variable n - 3;
in the entry's indexing the claim is a(n) = 4n^2 - 11n + 5 = 4(n-2)^2 + 5(n-2) - 1 for n >= 3 (a(2) = 1 differs).

**Result.** True: a(n) = 4n^2 - 11n + 5 for every n >= 3. The recurrence and the g.f. follow.

**Argument.** Write c-cell for a cell of value c and c-path for a path of c-cells.

1. *Each value fills an interval in each column.* Let (i,j) and (k,j) be c-cells, i < r < k, and suppose (r,j) has
   value d != c. A c-path from (i,j) to (k,j) changes row by at most 1 per step, so it meets every row s with
   i < s < k in a c-cell. Hence in every such row whose cell in column j is not a c-cell, the other cell is a
   c-cell. Now follow d-paths from (r,j): from a cell (s,j) with i < s < k and value d, the other cell of row s is
   a c-cell, and (i,j), (k,j) are c-cells, so every d-cell reachable from (r,j) lies in column j strictly between
   rows i and k. Every value sits in a corner, in row 1 or row n, which is outside that range: the d-cells are not
   connected. Contradiction.
2. *Crossing values.* Say c crosses if it has cells in both columns, with row intervals I_L and I_R. (a) A c-path
   from a cell in L to a cell in R has a horizontal step, so I_L and I_R share a row. (b) If a shared row s is not
   an end of I_L, the cell (s,L) has three c-neighbours (above, below, beside), which is forbidden; the same for
   I_R. So every shared row is an end of both intervals.
3. *Converse.* An array with the corner values, interval columns and (a), (b) is counted: each value is one or two
   vertical segments joined in a shared row; a cell with three equal neighbours would have both vertical
   neighbours equal (interior of its interval) and the horizontal one equal (a shared row), against (b).
4. *Column words.* Reading top-down, column L is a block of 1s, then blocks of some of 2, 4, then a block of 3s;
   column R is 2s, some of 1, 3, then 4s. The middle values of either column cross. If c, c' both cross with shared
   rows s, s', then in each column the block of c lies above the block of c' iff s < s', so crossing values appear
   in the same order in both columns. This leaves nine word pairs (L word, R word): (13,24); (123,24), (143,24),
   (13,214), (13,234); (123,234), (143,214); (1243,24), (13,2134). (For example 1423 puts 4 above 2 in L, while R
   starts with 2 and ends with 4; and 2 in L together with 1 in R puts 1 above 2 in L and 2 above 1 in R.)
5. *Counting.* Let blocks have lengths as written, all >= 1.
   - (13,24): L = 1^a 3^(n-a), R = 2^b 4^(n-b), a, b in [1, n-1], nothing crosses: (n-1)^2.
   - (123,24): L = 1^a 2^c 3^d, R = 2^b 4^e. Value 2 has I_L = [a+1, a+c], I_R = [1, b]; a shared row is >= a+1 >= 2,
     so by (b) it is b, and then (a) and (b) hold exactly when b = a+1. Free: a + c + d = n, C(n-1,2) arrays.
     (143,24), (13,214), (13,234) are its images under the left-right and top-bottom mirrors (value maps 1<->2,
     3<->4 and 1<->3, 2<->4): C(n-1,2) each.
   - (123,234): L = 1^a 2^c 3^d, R = 2^b 3^e 4^f. Value 2 forces b = a+1 as above. Value 3 has I_L = [a+c+1, n],
     I_R = [b+1, b+e] with b+e <= n-1, so the shared row is a+c+1 = b+e, i.e. e = c, and then f = d-1 >= 1. Free:
     a + c + d = n with d >= 2, C(n-2,2) arrays. (143,214) is the left-right mirror: C(n-2,2).
   - (1243,24): L = 1^a 2^c 4^g 3^d, R = 2^b 4^e. Value 2 forces b = a+1; value 4 has I_L = [a+c+1, a+c+g],
     I_R = [b+1, n]. Row n is not in I_L, so by (b) the only shared row is b+1 = a+2; the shared rows are
     [max(a+c+1, a+2), a+c+g], and this equals {a+2} only for c = g = 1. Free: a + d = n-2, n-3 arrays.
     (13,2134) is the left-right mirror: n-3.
   Sum: (n-1)^2 + 4 C(n-1,2) + 2 C(n-2,2) + 2(n-3) = 4n^2 - 11n + 5 for n >= 3.

Lean: [full proof](A164754/A164754_mathlib.lean).

### [A165300](A165300/): Layman's four rules for the 1,2-path sequence

**Source.** OEIS [A165300](https://oeis.org/A165300) (offset 1): "a(n) is the smallest number not already
present that permits the cyclic repetition of the path 1,2 of the digits in the sequence": 1, 2, 12, 121, 21,
212, 1212, ... Conjecture (J. W. Layman, Sep 2009): (1) for n > 1, if a(n) begins and ends with 1, a(n+1) is
a(n) with the initial 1 deleted; (2) begins with 1, ends with 2: append a final 1; (3) begins with 2, ends
with 1: append a final 2; (4) begins and ends with 2: prepend a 1. "confirmed through a(140) ... (and
should be fairly easy to prove)". (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05, revision #12.)

**Reading.** a(n) is the least m > 0, not among a(1), ..., a(n−1), such that the decimal digits of
a(1), ..., a(n−1), m written one after another read 1, 2, 1, 2, ... This reproduces the 25 printed terms
(also by brute force over all integers for the first 12).

**Result.** True (all four rules, for every n; the closed form below is also proved).

**Argument.** If the digits so far have length L, the admissible m are exactly the alternating numbers
(digits 1212... or 2121...) whose first digit is the (L+1)-st digit of the pattern; among these a longer one
is larger, so a(n) is the shortest unused one. Induction on j: after a(4j+2) the used numbers are exactly
the alternating numbers with at most 2j+1 digits (both starting digits), and L = (2j+1)(2j+2) is even.
Then a(4j+3) = 1212...12 (2j+2 digits), a(4j+4) = 1212...121 (2j+3), a(4j+5) = 2121...21 (2j+2),
a(4j+6) = 2121...212 (2j+3), and the invariant holds for j+1. With a(1) = 1, a(2) = 2 the rules read off
directly: 1...2 (even length, start 1) → append 1; 1...1 (odd, start 1) → delete the first digit;
2...1 → append 2; 2...2 → prepend 1 (including a(2) = 2 → a(3) = 12). Rule (1) fails at n = 1
(deleting the 1 of a(1) = 1 leaves nothing), which is why the entry excludes it.

Lean: [full proof](A165300/A165300_mathlib.lean).

### [A165640](A165640/): a(n) = floor(4(n+4)/5) - floor(2(n+4)/3)

**Source.** OEIS [A165640](https://oeis.org/A165640): number of multisets of n integers, each -2,
+1 or +3, with sum 3. Conjecture: "a(n) = Floor[4*(n+4)/5] - Floor[2*(n+4)/3]." (OEIS text,
CC BY-SA 4.0.) Offset 1.

**Result.** True for n ≥ 1 (at n = 0 the formula gives 1, the count is 0).

**Argument.** Let x, y, z be the multiplicities of -2, 1, 3. Then y = n - x - z and the sum
condition is 3x = n - 3 + 2z. So a(n) counts z ≥ 0 with z ≡ n (mod 3), 2z ≥ 3 - n and
5z ≤ 2n + 3 (from y ≥ 0). For n ≥ 3 this is the number of z ≡ n (mod 3) in
[0, floor((2n+3)/5)], a quasi-polynomial of degree 1 in n with period 15. The floor formula is a
quasi-polynomial of the same kind (periods 5 and 3). Two such functions that agree on 2 full
periods agree everywhere (METHODS §6); n = 1, 2 are checked directly.

Lean: [full proof](A165640/A165640_mathlib.lean).

### [A167230](A167230/): entries of exp(Sierpiński triangle)/e are Bell numbers

**Source.** OEIS [A167230](https://oeis.org/A167230): the matrix exponential of Sierpiński's
triangle S (Pascal's triangle mod 2, A047999) divided by e. Conjecture: "All the nonzero entries
in this triangle are Bell numbers (A000110)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. Entry (n,k) is Bell(j) when k AND n = k (bitwise), j = popcount(n) -
popcount(k), and 0 otherwise.

**Argument.** By Lucas's theorem, S(n,k) = prod_i M(n_i, k_i) over binary digits with
M = [[1,0],[1,1]], i.e. S is the (infinite) Kronecker power of M. Hence S^m is the Kronecker power
of M^m = [[1,0],[m,1]], so S^m(n,k) = m^j if k ⊆ n bitwise (j = number of bits set in n but not
in k), else 0. Then exp(S)(n,k) = sum_m m^j/m! = e·Bell(j) by Dobinski's formula.

Lean: [full proof](A167230/A167230_mathlib.lean).

### [A170941](A170941/): involutions without adjacent transpositions, proportion → 1/e

**Source.** [A170941](https://oeis.org/A170941) (offset 0), a(n+1) = a(n) + n·a(n−1) − a(n−2) + a(n−3),
a(0..3) = 1, 1, 1, 2. Comment (David Callan, Nov 11 2012): a(n) is the number of involutions on [n] that contain no
adjacent transposition, and "Conjecture: a(n)/A000085(n) -> 1/e as n -> inf." (OEIS text, CC BY-SA 4.0; still a
conjecture in revision #52, May 30 2026, checked 2026-11-06.)

**Result.** True: a(n)/I(n) → e^(−1), where I(n) = A000085(n) is the number of involutions of [n].

**Argument.** Write I(0) = I(1) = 1, I(m+2) = I(m+1) + (m+1) I(m).
1. *Inclusion–exclusion.* Let b(n) = Σ_k (−1)^k C(n−k, k) I(n−2k). C(n−k, k) counts sets of k pairwise disjoint
   adjacent pairs {i, i+1} in [n]; the involutions containing all of them as 2-cycles are the involutions of the other
   n − 2k points. So b(n) counts involutions of [n] with no adjacent transposition (this is Callan's comment).
2. *b satisfies the A170941 recurrence.* With K(n) = Σ_k k (−1)^k C(n−k, k) I(n−2k):
   - k·C(m−k, k) = (m−k)·C(m−k−1, k−1) and a shift k → k+1 give K(m+2) = K(m) − (m+1) b(m);
   - Pascal's rule C(n+2−k, k) = C(n+1−k, k) + C(n+1−k, k−1), the recurrence of I, and
     (n+1−2k) C(n+1−k, k) = (n+1−k) C(n−k, k) give b(n+2) = b(n+1) + n b(n) − K(n).
   Eliminating K: b(n+4) = b(n+3) + (n+3) b(n+2) − b(n+1) + b(n). Since b(0..3) = 1, 1, 1, 2, a = b.
3. *Domination.* I(m+2) ≥ (m+1) I(m), so by induction on k,
   (n−k)(n−k−1)⋯(n−2k+1) · I(n−2k) ≤ I(n). Hence the k-th term of b(n)/I(n), namely
   (−1)^k/k! · (n−k)_k I(n−2k)/I(n), has absolute value ≤ 1/k!.
4. *Termwise limit.* (m+1) I(m)² ≤ I(m+1)² (two-step induction), hence I(m+1)² ≤ 2(m+1) I(m)², so
   q(m) = I(m+1)/((m+1) I(m)) ≤ √(2/(m+1)) → 0. Then (m+1−k) I(m)/I(m+2) = (1 − k/(m+1))/(1 + q(m)) → 1, and by
   induction on k, (n−k)_k I(n−2k)/I(n) → 1 for each fixed k.
5. *Tannery.* By dominated convergence for series, b(n)/I(n) → Σ_k (−1)^k/k! = e^(−1).

Lean: [full proof](A170941/A170941_mathlib.lean).

### [A176494](A176494/): an odd prime p with |2^m - p| composite for every m ≥ 1

**Source.** OEIS [A176494](https://oeis.org/A176494) (least m ≥ 1 with |2^m - prime(n)| prime),
conjecture by Vladimir Shevelev (2010): "For every odd prime p, the sequence {|2^n - p|} contains at
least one prime." (OEIS text, CC BY-SA 4.0.)

**Result.** False. p = 509203 is prime and |2^m - 509203| is composite for every m ≥ 1, so a(n)
does not exist for prime(n) = 509203.

**Argument.** Covering congruences (Erdős's covering {3, 5, 7, 13, 17, 241} of the exponents mod
24). With o = ord_q(2):

| q | o | class of m (2^m ≡ p mod q) |
|---|---|---|
| 3 | 2 | 0 |
| 5 | 4 | 3 |
| 7 | 3 | 1 |
| 13 | 12 | 5 |
| 17 | 8 | 1 |
| 241 | 24 | 21 |

The classes cover Z/24, so for every m some q divides 2^m - p. Since 2^18 + 241 < p < 2^19 - 241,
|2^m - p| ≥ 15085 > 241, so q is a proper factor. p is prime (no divisor up to 713, and
714^2 > p).

Lean: [full proof](A176494/A176494.lean).

### [A182085](A182085/): (30k+7)(60k+13)(150k+31) is Carmichael whenever its factors are prime

**Source.** OEIS [A182085](https://oeis.org/A182085), conjecture by Marius Coman (2012): "N = (30k+7)*(60k+13)*(150k+31) is a Carmichael number if (but not only if) 30k+7, 60k+13 and 150k+31 are all three prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range k ≥ 0).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 60(5k+1)(900k^2+411k+47) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

Lean: [full proof](A182085/A182085_mathlib.lean).

### [A182088](A182088/): (30n-29)(60n-59)(90n-89)(180n-179) is Carmichael whenever its factors are prime

**Source.** OEIS [A182088](https://oeis.org/A182088), conjecture by Marius Coman (2012): "The number C = (30n-29)*(60n-59)*(90n-89)*(180n-179) is a Carmichael number if (but not only if) 30n-29, 60n-59, 90n-89 and 180n-179 are all four prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range n ≥ 1).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 180(n-1)(162000n^3-475200n^2+464635n-151433) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

Lean: [full proof](A182088/A182088_mathlib.lean).

### [A182089](A182089/): (330k+7)(660k+13)(990k+19)(1980k+37) is Carmichael whenever its factors are prime

**Source.** OEIS [A182089](https://oeis.org/A182089), conjecture by Marius Coman (2012): "C = (330k+7)*(660k+13)*(990k+19)*(1980k+37) is a Carmichael number if 330k+7, 660k+13, 990k+19 and 1980k+37 are all four prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range k ≥ 0).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 36(55k+1)(215622000k^3+13068000k^2+263945k+1777) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

Lean: [full proof](A182089/A182089_mathlib.lean).

### [A182132](A182132/): (30n-7)(90n-23)(300n-79) is Carmichael whenever its factors are prime

**Source.** OEIS [A182132](https://oeis.org/A182132), conjecture by Marius Coman (2012): "The number C = (30n-7)*(90n-23)*(300n-79) is a Carmichael number if (but not only if) 30n-7, 90n-23 and 300n-79 are all three prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range n ≥ 1).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 60(4n-1)(15n-4)(225n-53) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

Lean: [full proof](A182132/A182132_mathlib.lean).

### [A182133](A182133/): (30n+13)(90n+37)(150n+61) is Carmichael whenever its factors are prime

**Source.** OEIS [A182133](https://oeis.org/A182133), conjecture by Marius Coman (2012): "The number C = (30n+13)*(90n+37)*(150n+61) is a Carmichael number if (but not only if) 30n+13, 90n+37 and 150n+61 are all three prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range n ≥ 0).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 90(5n+2)(900n^2+766n+163) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

Lean: [full proof](A182133/A182133_mathlib.lean).

### [A182151](A182151/): Carmichael numbers divisible by 31 lie in three classes mod 2790

**Source.** OEIS [A182151](https://oeis.org/A182151), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 31 can be written in one of the following three forms: C = 2790n+31; C = 2790n+31^2 or C = 2790n+31*61, where n is natural."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 30 | C - 1. With 31 | C, the Chinese remainder theorem gives C ≡ 31 (mod 930). The three lifts of 31 mod 930 to residues mod 2790 are 31, 961 = 31^2 and 1891 = 31·61.

Lean: [full proof](A182151/A182151_mathlib.lean).

### [A182206](A182206/): Carmichael numbers divisible by 37 and 73 are 37·73·(18n+91)

**Source.** OEIS [A182206](https://oeis.org/A182206), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 37 and 73 can be written as C = 37*73*(18n+91), where n is natural."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Write C = 2701 m. Korselt gives 36 | C - 1 and 72 | C - 1, so 2701 m ≡ 37 m ≡ 1 (mod 72), i.e. m ≡ 37 (mod 72) (37^2 ≡ 1), hence m ≡ 1 (mod 18). m = 37 would make 37^2 | C, impossible for a Carmichael number, so m ≥ 109 and m = 18n + 91 with n ≥ 1. (Korselt gives the stronger m ≡ 37 mod 72.)

Lean: [full proof](A182206/A182206_mathlib.lean).

### [A182207](A182207/): Carmichael numbers divisible by p and 2p - 1 are p(2p-1)(n(2p-2)+p)

**Source.** OEIS [A182207](https://oeis.org/A182207), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by p and 2p-1 (where p and 2p-1 are prime numbers) can be written as C = p*(2p-1)*(n*(2p-2)+p)."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Carmichael numbers are odd, so p = 2r + 1, r ≥ 1, and 2p - 2 = 4r. Write C = p(2p-1) m. Korselt for the prime factor 2p - 1 gives 4r | C - 1. If p(2p-1)m - 1 = 4rc then m - p = 4r(pc - (4r^2+5r+2)m), so m ≡ p (mod 2p-2). As m > 0 and p < 2p - 2 + p, m = p + n(2p-2) with n ≥ 0 (in fact n ≥ 1, since m = p gives p^2 | C).

Lean: [full proof](A182207/A182207_mathlib.lean).

### [A182208](A182208/): Carmichael numbers divisible by 7 are never 7(6m+1)(6n-1)

**Source.** OEIS [A182208](https://oeis.org/A182208), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 7 can be written in one of two ways: (1) C=7*(6m+1)*(6n+1) ... or (2) C=7*(6m-1)*(6n-1) ... In other words, there aren't Carmichael numbers divisible by 7 of the form C=7*(6m+1)*(6n-1)."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 6 | C - 1; with 7 | C and 7 ≡ 1 (mod 6), C/7 ≡ 1 (mod 6). C/7 is composite (a Carmichael number has at least three prime factors) and prime to 6, and any factorisation C/7 = d e has d e ≡ 1 (mod 6), which forces d ≡ e ≡ 1 or d ≡ e ≡ 5 (mod 6). So both written forms occur as splittings and the mixed form never does.

Lean: [full proof](A182208/A182208_mathlib.lean).

### [A182334](A182334/): the order-9 recurrence fails at n = 10, 11 (holds from n = 12)

**Source.** OEIS [A182334](https://oeis.org/A182334): triangular numbers that differ from a square
by 1 (0, 1, 3, 10, 15, 120, 325, 528, 4095, 11026, 17955, ...; offset 1). Formula (Greathouse,
2012, a conjecture when added, now printed without qualification): "a(n) = 35*a(n-3) -
35*a(n-6) + a(n-9)." (OEIS text, CC BY-SA 4.0.)

**Result.** False as printed: at n = 10, a(10) = 11026 but 35a(7) - 35a(4) + a(1) = 11025; at
n = 11, a(11) = 17955 but the right side is 17956. It holds for all n ≥ 12 (proof sketch below,
checked to 10^60).

**Argument.** Failure: direct computation. Corrected statement: T = k(k+1)/2 = s^2 ± 1 is
x^2 - 8s^2 = 9 or -7 with x = 2k + 1. Each solution class is x_j = c β^j + c̄ β^(-j),
β = 3 + √8, so T = (x^2 - 1)/8 restricted to a class is annihilated by (t - 1)(t^2 - 34t + 1).
Three classes interleave with period 3 once the β^(-j) terms are small, giving the annihilator
(t^3 - 1)(t^6 - 34 t^3 + 1) = t^9 - 35t^6 + 35t^3 - 1. The smallest terms (0, 1, 3) are where
classes collide or fail to interleave, which is why n = 10, 11 fail. Barker's g.f. in the entry
has numerator degree 11 over a degree-9 denominator, so it also only implies the recurrence for
n ≥ 12.

Lean: [full proof](A182334/A182334_mathlib.lean).

### [A182336](A182336/): n + 1 ≤ a(n) ≤ 9n/8 + 1 for n > 96

**Source.** OEIS [A182336](https://oeis.org/A182336) (V. Shevelev, 2012): a(n) is the least
m ≥ n whose binary Hamming distance from n is 4. Conjecture: "for n > 96, n + 1 <= a(n) <= 9n/8
+ 1." (C. R. Greathouse IV, Apr 25 2012; OEIS text, CC BY-SA 4.0.)

**Result.** Proved. The threshold is sharp: a(96) = 111 > 109 = ⌊9·96/8⌋ + 1.

**Argument.** The lower bound holds because the distance from n to n is 0. For the upper bound,
build m with distance 4 and 8(m − n) ≤ n + 8. Hamming distance adds over a split into a high
part and a low part: D(2^K·a + s, 2^K·b + t) = D(a, b) + D(s, t) when s, t < 2^K. Write
n = 64q + r with 0 ≤ r < 64.
- r < 56: bit 3, 4 or 5 of n is 0. A table over r < 56 gives r < r' < 64 with r' ≤ r + 15 and
  D(r, r') = 4. Then m = 64q + r' works once n ≥ 112.
- r ≥ 56: let u = ⌊n/8⌋ and write u + 1 = 2^j·(2H + 1). Then j ≥ 3,
  n = 2^j·(16H + 7) + s and m = n + 2^j = 2^j·(16H + 8) + s with s < 2^j. So D(n, m) =
  D(7, 8) = 4, and 8·2^j ≤ 8(u + 1) ≤ n + 8. This case covers n = 2^L − 1, where the bound is
  nearly tight.
- 97 ≤ n < 112: finite check.

Lean: [full proof](A182336/A182336_mathlib.lean).

### [A182381](A182381/): Carmichael numbers divisible by 17 and 29 are 952n + 561

**Source.** OEIS [A182381](https://oeis.org/A182381), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 17 and 29 can be written as C = 952*n + 561."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 16 | C - 1 and 28 | C - 1, so C ≡ 1 (mod 112), in particular C ≡ 1 (mod 56). With 17 | C and 952 = 56·17, the Chinese remainder theorem gives one class mod 952, which is 561 = 33·17 (561 ≡ 1 mod 56).

Lean: [full proof](A182381/A182381_mathlib.lean).

### [A182416](A182416/): (60k+13)(180k+37)(300k+61) is Carmichael whenever its factors are prime

**Source.** OEIS [A182416](https://oeis.org/A182416), conjecture by Marius Coman (2012): "N = (60k+13)*(180k+37)*(300k+61) is a Carmichael number if (but not only if) 60k+13, 180k+37 and 300k+61 are all three prime numbers."
(OEIS text, CC BY-SA 4.0.)

**Result.** True (for the stated range k ≥ 0).

**Argument.** Chernick-type family. For each factor f, f - 1 divides N - 1 as polynomials in the
parameter with an integer quotient (N - 1 = 180(5k+1)(3600k^2+1532k+163) factored over Z; the quotients are in
`certificate/korselt_poly.py` and in the Lean file). If all factors are prime they are distinct
(the linear forms take different values in the stated range), so N is squarefree, and every prime
factor f has f - 1 | N - 1. Korselt's criterion then makes N a Carmichael number.

Lean: [full proof](A182416/A182416_mathlib.lean).

### [A182515](A182515/): Carmichael numbers divisible by 23 and 67 are 23·67·(66n+23)

**Source.** OEIS [A182515](https://oeis.org/A182515), conjecture by Marius Coman (2012): "Any Carmichael number C divisible by 23 and 67 can be written as C = 23*67*(66n+23)."
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 22 | C - 1 and 66 | C - 1. With C = 1541 m and 1541 ≡ 23 (mod 66), 23 m ≡ 1 (mod 66), so m ≡ 23 (mod 66) because 23^2 = 529 ≡ 1. (m = 23 gives 23^2 | C, so n ≥ 1.)

Lean: [full proof](A182515/A182515_mathlib.lean).

### [A182532](A182532/): Carmichael numbers divisible by 7 and 17: the four residue classes mod 120

**Source.** OEIS [A182532](https://oeis.org/A182532), conjecture by Marius Coman (2012): Conjectures (1)-(4): a Carmichael number C divisible by 7 and 17 "of the form 10k+1 can be written as C = 7*17*(120n+119)"; of the form 10k+5 as 7*17*(120n+95); 10k+3 as 7*17*(120n+47); 10k+9 as 7*17*(120n+71).
(OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Korselt's criterion in the necessary direction: if C is a Carmichael number and p
is a prime factor, then p - 1 | C - 1 (and C is squarefree). Korselt gives 6 | C - 1 and 16 | C - 1, so 48 | C - 1. With C = 119 m and 119 ≡ 23 (mod 48), m ≡ 23^(-1) = 23 (mod 48). C ≡ 9m (mod 10) fixes m mod 5 from C mod 10, and m ≡ 23 (mod 48) gives m ≡ 7 (mod 8), m ≡ 2 (mod 3); together m mod 120 is 119, 95, 47, 71 in the four cases.

Lean: [full proof](A182532/A182532_mathlib.lean).

### [A187011](A187011/): det(|p_i − p_j|) over the first n primes

**Source.** [A187011](https://oeis.org/A187011) (offset 0, a(0) = 1), Zhi-Wei Sun, Aug 30 2013: "Determinant
of the n X n matrix with (i,j)-entry equal to |p_i-p_j|, where p_k denotes the k-th prime." Comment: "Conjecture:
(-1)^(n-1)*a(n) > 0 for all n > 1, and |a(n)|^{1/n} tends to the infinity." (OEIS text, CC BY-SA 4.0; still stated
on 2026-11-05, revision #19 of Aug 16 2026.)

**Result.** Both parts are true, and both are proved in Lean 4 + Mathlib. For n ≥ 2,

a(n) = (−1)^(n−1) · 2^(n−2) · (p_n − 2) · ∏_{i<n} (p_{i+1} − p_i),

so the sign part is immediate. The growth part follows from this formula, a Selberg-sieve upper bound for prime
pairs uniform in the shift, and Chebyshev's lower bound for π(x).

**Argument.** 1. *Distance matrix of a path.* For x_1 < … < x_n (n ≥ 2) in an ordered commutative ring, let D = (|x_i − x_j|) and
   d_i = x_{i+1} − x_i. Subtract row i+1 from row i (i < n), then column j+1 from column j (j < n). That is U D Uᵀ with
   U = I − (superdiagonal), det U = 1. The result is the arrowhead matrix with diagonal −2d_1, …, −2d_{n−1}, last row and
   last column (d_1, …, d_{n−1}), corner 0. Adding half of each of the first n−1 columns to the last column (in Lean:
   multiply by V with last column (1, …, 1, 2), det V = 2) makes it lower triangular with diagonal −2d_1, …, −2d_{n−1},
   x_n − x_1. Hence 2 det D = (−2)^(n−1) (∏ d_i)(x_n − x_1), i.e.
   det D = (−1)^(n−1) 2^(n−2) (x_n − x_1) ∏ d_i. This is the path case of the Bapat–Kirkland–Neumann formula for
   weighted trees.
2. *Sign.* With x_i = p_i every factor x_n − x_1 = p_n − 2 and d_i is positive, so (−1)^(n−1) a(n) > 0 for n ≥ 2.
3. *Growth.* Let g_i = p_{i+1} − p_i. By step 1, |a(n)| ≥ ∏_{i<n} g_i (the factors 2^(n−2) and p_n − 2 are ≥ 1),
   so it suffices that (1/n) Σ_{i<n} log g_i → ∞. Fix H and let m ≥ 1, N = p_{m+1}.
   - *Small gaps give prime pairs.* If i ≥ 2 and g_i ≤ H, then h = g_i is even, 0 < h ≤ H, and q = p_i < N with q,
     q + h prime. The map i ↦ p_i is injective, so #{i ≤ m : g_i ≤ H} ≤ 1 + Σ_{h ≤ H even} #{q < N : q, q + h prime}.
   - *Sieve.* For even h > 0 and N ≥ 2, #{q < N : q, q + h prime} ≤ 2^13 K(h)^2 N / (log N)^2 with
     K(h) = ∏_{p | h} p/(p−1) (Selberg's Λ² sieve, proved in FAM/twin-primes). So the count is ≤ 1 + C_H N/(log N)^2
     with C_H = Σ_{h ≤ H even} 2^13 K(h)^2.
   - *Chebyshev.* m + 1 = π(N) ≥ (N log 2 − log(N+1)) / log N (Mathlib `Chebyshev.pi_ge`). For N large,
     4 log N + 1 + 2 C_H N / log N ≤ N/2, and with log(N+1) ≤ log 2 + log N and log 2 > 1/2 this gives
     #{i ≤ m : g_i ≤ H} ≤ m/2. Since N = p_{m+1} → ∞, this holds for all large m.
   - *Mean.* Gaps are ≥ 1, so Σ_{i ≤ m} log g_i ≥ log H · #{i ≤ m : g_i > H} ≥ (m/2) log H. With m = n − 1 ≥ n/2,
     log|a(n)|/n ≥ (log H)/4 for all large n. H is arbitrary, so log|a(n)|/n → ∞ and |a(n)|^(1/n) → ∞.

   Why a sieve is needed: Chebyshev bounds alone do not suffice. A set with π(x) ≍ x/log x in which a fraction
   1 − 1/log log n of the first n gaps equal 2 and the rest have size about log n · log log n has bounded mean log gap.
   AM–GM bounds the geometric mean of the gaps from above (by (p_n − 2)/(n − 1)), not from below. Excluding such
   clustering is exactly a Brun-type statement that p, p + h are rarely both prime.

Lean: [full proof](A187011/A187011_growth_mathlib.lean).

### [A188644](A188644/): (k^n + k^(-n))/2 is an integer for k = (√(x²-1) + x)²

**Source.** OEIS [A188644](https://oeis.org/A188644), conjecture by C. Hohn: "Given function
f(x, y)=((x^2+y)^(1/2)+x)^2; and constant k=f(x, y); then for all integers x>=1 and y=[+-]1,
k may be irrational, but ((k^n)+(k^(-n)))/2 always produces integer sequences"; this entry is
the case y = -1 (A188645 is the other sign). (OEIS text, CC BY-SA 4.0.)

**Result.** True: (k^n + k^(-n))/2 = T_n(2x^2 + y), with T_n the Chebyshev polynomial of the
first kind.

**Argument.** Since y^2 = 1, 1/k = (√(x²+y) - x)² / y² = (√(x²+y) - x)², so
k + 1/k = 2(2x² + y). Put m = 2x² + y; u_n = (k^n + k^(-n))/2 satisfies u_0 = 1, u_1 = m,
u_(n+1) = 2m u_n - u_(n-1), which is the Chebyshev recurrence: u_n = T_n(m) ∈ Z.
(Equivalently, the entry's comment A(n,k) = T_(2k)(n) by Manyama.)

Lean: [full proof](A188644/A188644_mathlib.lean).

### [A188645](A188645/): (k^n + k^(-n))/2 is an integer for k = (√(x²+1) + x)²

**Source.** OEIS [A188645](https://oeis.org/A188645), conjecture by C. Hohn: "Given function
f(x, y)=((x^2+y)^(1/2)+x)^2; and constant k=f(x, y); then for all integers x>=1 and y=[+-]1,
k may be irrational, but ((k^n)+(k^(-n)))/2 always produces integer sequences"; this entry is
the case y = 1 (A188644 is the other sign). (OEIS text, CC BY-SA 4.0.)

**Result.** True: (k^n + k^(-n))/2 = T_n(2x^2 + y), with T_n the Chebyshev polynomial of the
first kind.

**Argument.** Since y^2 = 1, 1/k = (√(x²+y) - x)² / y² = (√(x²+y) - x)², so
k + 1/k = 2(2x² + y). Put m = 2x² + y; u_n = (k^n + k^(-n))/2 satisfies u_0 = 1, u_1 = m,
u_(n+1) = 2m u_n - u_(n-1), which is the Chebyshev recurrence: u_n = T_n(m) ∈ Z.
(Equivalently, the entry's comment A(n,k) = T_(2k)(n) by Manyama.)

Lean: [full proof](A188645/A188645_mathlib.lean).

### [A188646](A188646/): a(n) = k a(n-1) - (k-1)/k^n is an integer sequence

**Source.** OEIS [A188646](https://oeis.org/A188646), conjecture by C. Hohn: with k = ((x^2+y)^(1/2)+x)^2
and a(0) = 1, "for all integers x>=1 and y=[+-]1, k may be irrational, but sequence
a(n)=a(n-1)*k-((k-1)/(k^n)) always produces integer sequences"; this entry is y = -1 (A188647 is the
other sign). (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** By induction a(n) = (k^(n+1) + k^(-n))/(k+1): a(0) = 1, and
k (k^n + k^(1-n))/(k+1) - (k-1)k^(-n) = (k^(n+1) + k^(2-n) - k^(2-n) + k^(-n))/(k+1). Then
(k^(n+1) + k^(-n))/(k+1) = k^(-n) (k^(2n+1) + 1)/(k+1) = sum_{i=0}^{2n} (-1)^i k^(i-n)
= (-1)^n [1 + sum_{j=1}^{n} (-1)^j (k^j + k^(-j))], and k^j + k^(-j) = 2 T_j(2x² + y) is an
integer (OEIS-A188644/A188645, using 1/k = (√(x²+y) - x)² since y² = 1).

Lean: [full proof](A188646/A188646_mathlib.lean).

### [A188647](A188647/): a(n) = k a(n-1) - (k-1)/k^n is an integer sequence

**Source.** OEIS [A188647](https://oeis.org/A188647), conjecture by C. Hohn: with k = ((x^2+y)^(1/2)+x)^2
and a(0) = 1, "for all integers x>=1 and y=[+-]1, k may be irrational, but sequence
a(n)=a(n-1)*k-((k-1)/(k^n)) always produces integer sequences"; this entry is y = 1 (A188646 is the
other sign). (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** By induction a(n) = (k^(n+1) + k^(-n))/(k+1): a(0) = 1, and
k (k^n + k^(1-n))/(k+1) - (k-1)k^(-n) = (k^(n+1) + k^(2-n) - k^(2-n) + k^(-n))/(k+1). Then
(k^(n+1) + k^(-n))/(k+1) = k^(-n) (k^(2n+1) + 1)/(k+1) = sum_{i=0}^{2n} (-1)^i k^(i-n)
= (-1)^n [1 + sum_{j=1}^{n} (-1)^j (k^j + k^(-j))], and k^j + k^(-j) = 2 T_j(2x² + y) is an
integer (OEIS-A188644/A188645, using 1/k = (√(x²+y) - x)² since y² = 1).

Lean: [full proof](A188647/A188647_mathlib.lean).

### [A192205](A192205/): a(n)^(1/n) → 16√3/9 for the coefficient sum of (1-x-x^2+x^3)^n

**Source.** OEIS [A192205](https://oeis.org/A192205): a(n) = sum of absolute values of the
coefficients of (1-x-x^2+x^3)^n. Conjecture: "limit a(n)^(1/n) = 16*sqrt(3)/9 = 3.079201...,
which is substantiated by the observation that the sums of the coefficients squared in
(1-x-x^2+x^3)^n equals binomial(4n,n)." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Let P(x) = 1 - x - x^2 + x^3 = (1-x)^2(1+x), l1 = a(n), l2 = (sum c_k^2)^(1/2) for
P^n. Cauchy–Schwarz over the 3n+1 coefficients gives l2 ≤ l1 ≤ √(3n+1) l2, so
lim l1^(1/n) = lim l2^(1/n) if the latter exists. By Parseval, l2^2 = (1/2π) ∫ |P(e^(it))|^(2n) dt,
and the L^(2n) norm of |P| on the circle tends (as n → ∞, after taking the 1/(2n)-th power) to its
sup norm. |P(e^(it))|^2 = |1-e^(it)|^4 |1+e^(it)|^2 = 64 s^2 (1-s) with s = sin^2(t/2), maximal at
s = 2/3 with value 256/27, so sup |P| = 16/(3√3) = 16√3/9.
(The entry's identity sum c_k^2 = C(4n,n), checked here for n < 200, gives the same limit
(256/27)^(1/2) via Stirling, but it is not needed.)

Lean: [full proof](A192205/A192205_mathlib.lean).

### [A195507](A195507/): the recurrence a(n+1) = d a(n) - (d-1) n + 1

**Source.** OEIS [A195507](https://oeis.org/A195507): a(n) = smallest m > n with m ≡ n (mod k)
for k = 1..n-1. Conjecture: "Write a(n)/n in lowest terms as num/d. Then a(n+1) = d*a(n) -
(d-1)*n + 1." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** m ≡ n (mod k) for all k < n iff L = lcm(1..n-1) divides m - n, so a(n) = n + L
(Adams-Watters, in the entry). The reduced denominator of (n + L)/n is
d = n/gcd(n + L, n) = n/gcd(L, n). Then lcm(1..n) = lcm(L, n) = L n/gcd(L, n) = d L, so
a(n+1) = n + 1 + d L = d(n + L) - (d - 1)n + 1.

Lean: [full proof](A195507/A195507_mathlib.lean).

### [A195538](A195538/): denominators of Pythagorean approximations to √8 satisfy a(n) = 35a(n−2) − 35a(n−4) + a(n−6)

**Source.** OEIS [A195538](https://oeis.org/A195538) (offset 1): denominators a(n) of Pythagorean approximations
b(n)/a(n) to √8: 5, 12, 145, 420, 4901, 14280, ... Conjecture (R. J. Mathar, Sep 2011): "a(n) = 35*a(n-2)
-35*a(n-4) +a(n-6) with bisections A098602 and A076218." (OEIS text, CC BY-SA 4.0; still a conjecture on
2026-11-05, revision #15.)

**Reading.** P. J. C. Moses' program (A195500, A195538): s = r + √(1 + r²) = 3 + 2√2 for r = √8; for each n
take the n-term continued-fraction convergent p/q of s and reduce (p² − q²)/(2pq); a(n) is its
denominator. Offsets: A098602 (offset 0) = 0, 12, 420, ..., so the even bisection claim is
a(2k) = A098602(k), k ≥ 1; A076218 (offset 1) = 0, 1, 5, 145, ..., so the odd one is a(2k−1) = A076218(k+2).
The bisection sequences are taken from their own definitions: A098602(n) = A001652(n)·A046090(n), A001652 by
its recurrence, A046090 = X+1 over Pythagorean triples (X, X+1, Z), A076218 = numbers m with 2m² − 3m + 1 a
square.

**Result.** True (recurrence and both bisections).

**Argument.** s = 3 + 2√2 = [5; 1, 4, 1, 4, ...] (complete quotients (√2+1)/2 and 2 + 2√2 alternate).
Let (X_k, W_k) be the solutions of X² − 8W² = 1 ((1,0), (3,1), (17,6), ...; step (X, W) → (3X+8W, X+3W)),
U = X + 2W, V = X + 3W. The convergent recurrences give p_(2k) = U_(k+1) = U + 4V, q_(2k) = U, and
p_(2k+1) = V_(k+1) = U + 5V, q_(2k+1) = V (indices k on the right). From U² + 4UV − 4V² = 1:
- n = 2k+1: p, q odd and (p² − q²)/(2pq) = 4V(U+2V)/((U+4V)U) in lowest terms, so a = (U+4V)U;
- n = 2k+2: p − q odd and (p² − q²)/(2pq) = (U+4V)(U+6V)/(2(U+5V)V) in lowest terms, so a = 2(U+5V)V.
(Each coprimality has an explicit Bézout pair linear in U, V, e.g. (U+6V)(U+2V) − 4V(U+4V) = 1.) Both
bisections are quadratic forms in (X_k, W_k) under a matrix with eigenvalues λ^{±1}, λ = 3 + 2√2, so they
satisfy the recurrence with characteristic roots λ², 1, λ⁻², i.e. x³ − 35x² + 35x − 1 (a polynomial identity).
Bisections: a(2k+1) = (U+4V)U = 4W_(k+1)² + 1 (uses X² − 8W² = 1), and the m with 2m² − 3m + 1 = (2m−1)(m−1)
a square are 0 and, for m ≥ 1, m − 1 = u², 2m − 1 = v² (coprime factors), v² − 8(u/2)² = 1, so m = 4W_j² + 1.
a(2k+2) = 2(U+5V)V = x(x+1) with 2x + 1 = X_(k+1) + 4W_(k+1); A001652 satisfies 2x(k) + 1 = X_k + 4W_k, and
X² + (X+1)² = Z² ⇔ (2X+1)² − 2Z² = −1, which maps to X'² − 8W'² = 1 by X' = 2Z − (2X+1), W' = (2X+1−Z)/2,
so the Pythagorean X+1 values are x(k) + 1. Every solution of x² − 8w² = 1 in ℕ is some (X_k, W_k) by descent
(x, w) → (3x − 8w, 3w − x).

Lean: [full proof](A195538/A195538_mathlib.lean).

### [A195539](A195539/): numerators of Pythagorean approximations to √8 satisfy b(n) = 34b(n−2) − b(n−4)

**Source.** OEIS [A195539](https://oeis.org/A195539) (offset 1): numerators b(n) of Pythagorean approximations
b(n)/a(n) to √8: 12, 35, 408, 1189, 13860, ... Conjecture (R. J. Mathar, Sep 2011): "a(n) = +34*a(n-2)
-a(n-4) with a(2*n+1) = A000129(4*n+4), a(2*n) = A046176(n+1)." (OEIS text, CC BY-SA 4.0; still a conjecture
on 2026-11-05, revision #10.)

**Reading.** Same construction as [A195538](A195538/README.md) (P. J. C. Moses' program): b(n) is the
numerator of (p² − q²)/(2pq) in lowest terms, p/q the n-term convergent of 3 + 2√2. A000129 = Pell numbers
(offset 0, by their recurrence); A046176 (offset 1) = positive m such that m² is a hexagonal number h(2h − 1),
in increasing order (1, 35, 1189, ...).

**Result.** True (recurrence and both bisection formulas, the odd one for n ≥ 0 and the even one for n ≥ 1).

**Argument.** With the notation of A195538 ((X_k, W_k) solutions of X² − 8W² = 1, U = X + 2W, V = X + 3W),
the lowest-terms computation gives b(2k+1) = 4V(U+2V) and b(2k+2) = (U+5V)² − V². The addition formula
X_(a+b) = X_aX_b + 8W_aW_b, W_(a+b) = X_aW_b + W_aX_b turns these into b(2k+1) = 2W_(2k+2) and
b(2k+2) = W_(2k+3). Pell(2j) = 2W_j and Pell(2j+1) = X_j + 2W_j (induction), so b(2n+1) = Pell(4n+4).
m² = h(2h − 1) ⇔ (4h − 1)² − 8m² = 1, so (4h − 1, m) = (X_k, W_k); X_k ≡ 1 (mod 4) for even k and 3 for
odd k, so the hexagonal-square indices are W_(2j+1), j ≥ 0, and A046176(n+1) = W_(2n+1) = b(2n). The
recurrence b(n) = 34b(n−2) − b(n−4) follows since both bisections are W at indices in an arithmetic
progression of step 2 (a polynomial identity in X_k, W_k).

Lean: [full proof](A195539/A195539_mathlib.lean).

### [A195608](A195608/): first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts

**Source.** [A195608](https://oeis.org/A195608): "Numbers n such that Sum_{i=1..n} A(i) = A(n)*A(n+1)/4, where
A(n) = A001969(n)" (evil numbers, offset 1, A(1) = 0). Comment by V. Shevelev (2011): "Conjectures: 1) there are
only 3 different first differences 1,4,6; 2) the sequence contains either isolated series of terms, e.g.,
{1},{7},{25},{31},..., or series of 3 consecutive integers, e.g., {11,12,13}, {19,20,21}, etc.; 3)the first terms m
of every series satisfy the condition A(m+1)-A(m-1)=5, where A(n)=A001969(n)." (OEIS text, CC BY-SA 4.0; entry
fetched 2026-11-05, unchanged since Dec 2019.) The twin entry for odious numbers is [A195609](A195609/README.md).

**Reading.** S = {n ≥ 1 : 4·Σ_{i≤n} A(i) = A(n)A(n+1)} (the same as the /4 equation). A "series" is a maximal
run of consecutive integers in S; the comment's examples count the singletons {1}, {7} as series.
- 1) For every n ∈ S the next element of S is n + 1, n + 4 or n + 6 (this also gives that S is infinite);
  all three differences occur.
- 2) If [a, b] ⊆ S, a − 1 ∉ S and b + 1 ∉ S, then b = a or b = a + 2.
- 3) If m ∈ S and m − 1 ∉ S then A(m+1) − A(m−1) = 5, for m ≥ 2. The series {1} has m = 1 and A(0) does not
  exist, so m = 1 is excluded (it is the only run start below 2). Read with singletons included, as the comment's
  wording does; for runs of 3 alone the statement is a special case.

**Result.** All three conjectures are true. Closed form, with t the Thue–Morse sequence (A010060):
S = {2j+1 : t(j) = 0} ∪ {2j+2 : t(j) = t(j+1) = 0}. Sharper form of 3): for m ∈ S, m ≥ 2,
A(m+1) − A(m−1) is 5 if m starts its series and 4 otherwise.

**Argument.** A(k+1) = 2k + t(k) (A001969 comment, Alekseyev), t(2j) = t(j), t(2j+1) = 1 − t(j), so
Σ_{k<2j} t(k) = j and Σ_{i≤n} A(i) = n(n−1) + Σ_{k<n} t(k). Write a = t(j), b = t(j+1).
- n = 2j+1: the equation is 16j² + 12j + 4a = (4j + a)(4j + 3 − a), true iff a = 0.
- n = 2j+2: it is 16j² + 28j + 12 = (4j + 3 − a)(4j + 4 + b), true iff a = b = 0.
Let Z = {j : t(j) = 0}. t never takes one value three times in a row (t(2i) ≠ t(2i+1)).
- 1) n = 2j+2 ∈ S gives 2j+3 ∈ S. For n = 2j+1, j ∈ Z, the next zero of t after j is j+1, j+2 or j+3, giving the
  next element 2j+2, 2j+5 or 2j+7; the even numbers in between need two consecutive zeros, which are absent.
- 2) Every even element 2j+2 brings 2j+1 and 2j+3 with it, and 2j, 2j+4 ∉ S (each would need three zeros of t
  in a row). A run of length ≥ 2 contains an even element, so it is exactly {2j+1, 2j+2, 2j+3}.
- 3) Series start m = 2j+1 with j ∈ Z, j ≥ 1, t(j−1) = 1. A(m+1) − A(m−1) = 4 + t(2j+1) − t(2j−1)
  = 4 + t(j−1) − t(j) = 5.

Lean: [full proof](A195608/A195608_mathlib.lean).

### [A195609](A195609/): first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts

**Source.** [A195609](https://oeis.org/A195609): "Numbers n such that Sum_{i=1..n} A(i) = A(n)*A(n+1)/4, where
A(n) = A000069(n)" (odious numbers, offset 1, A(1) = 1). Comment by V. Shevelev (2011): "Conjectures: 1) there are
only 3 different first differences 1,4,6; 2) the sequence contains either isolated series of terms, e.g.,
{9},{23},{33},{39},..., or series of 3 consecutive integers, e.g., {3,4,5}, {15,16,17}, etc.; 3)the first terms m
of every series satisfy the condition A(m+1)-A(m-1)=5, where A(n)=A000069(n)." (OEIS text, CC BY-SA 4.0; fetched
2026-11-05, unchanged since Dec 2019.) Twin of [A195608](A195608/README.md) (evil numbers).

**Reading.** As for A195608: S = {n ≥ 1 : 4·Σ_{i≤n} A(i) = A(n)A(n+1)}, a series is a maximal run of consecutive
integers in S (singletons included), 1) next element is n + 1, n + 4 or n + 6, 2) [a, b] ⊆ S with a − 1, b + 1 ∉ S
gives b ∈ {a, a + 2}, 3) m ∈ S, m − 1 ∉ S gives A(m+1) − A(m−1) = 5. Here min S = 3, so 3) needs no exception.

**Result.** All three conjectures are true. Closed form, with t the Thue–Morse sequence:
S = {2j+1 : t(j) = 1} ∪ {2j+2 : t(j) = t(j+1) = 1}. For m ∈ S, A(m+1) − A(m−1) is 5 if m starts its series and
4 otherwise.

**Argument.** A(k+1) = 2k + u(k) with u = 1 − t, the indicator of evil numbers shifted by one: the n-th odious number
is the (n−1)-th zero of u. u has the same recursions u(2j) = u(j), u(2j+1) = 1 − u(j) (only u(0) = 1 differs), so
Σ_{k<2j} u(k) = j and the A195608 argument goes through word for word with t replaced by u. The Lean file proves
everything once for any 0/1 sequence with these two recursions (`TMLike`) and instantiates it twice. The odious
closed form was derived this way and checked numerically before the proof (n ≤ 400000, and against the b-file).

Lean: [full proof](A195608/A195608_mathlib.lean).

### [A197521](A197521/): the constant 3.52133782... is 3 plus the constant of A197383

**Source.** OEIS [A197521](https://oeis.org/A197521): least x > 0 with cos(πx/2) = cos²(πx/3).
Conjecture: "the constant here, 3.52133782..., is 3 plus the constant in A197383, the latter being
the least t>0 satisfying sin(Pi*t/6)=(sin Pi*t/3)^2." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Put x = t + 3 and s = sin(πt/6), θ = πt/6. Then cos(πx/2) = sin(3θ) = 3s - 4s^3 and
cos²(πx/3) = cos²(2θ) = (1 - 2s²)². The first equation becomes
4s^4 + 4s^3 - 4s^2 - 3s + 1 = (s + 1)(4s^3 - 4s + 1) = 0. The A197383 equation
sin θ = sin²(2θ) = 4s²(1 - s²) becomes s(4s^3 - 4s + 1) = 0.
- No root with x ∈ (0, 3]: there t ∈ (-3, 0], s ∈ (-1, 0]; s = -1 only at x = 0, and
  g(s) = 4s^3 - 4s + 1 > 0 on [-1, 0] (minimum at s = -1/√3, value 1 + 8/(3√3) > 0).
- For t > 0 the least root of either equation comes from the least θ > 0 with g(sin θ) = 0, i.e.
  θ = arcsin(s1) with s1 ≈ 0.2696 the least positive root of g (s = -1 needs θ = 3π/2, s = 0 needs
  θ = π, both later). So both least roots are t0 = (6/π) arcsin(s1) = 0.52133782957..., and the
  A197521 constant is 3 + t0.

Lean: [full proof](A197521/A197521_mathlib.lean).

### [A197702](A197702/): least k with n = ±1 ±3 ± … ±(2k−1)

**Source.** [A197702](https://oeis.org/A197702) (offset 1), comment by J. W. Layman: "Conjecture. Let SO(k)
be the sum of the first k odd positive integers. Then a(n)=k if n=SO(k). Otherwise, choose k so that
SO(k-1)<n<SO(k). Then if SO(k)-n=4, a(n)=k+2, else if SO(k)-n is odd then a(n)=k+1 else a(n)=k." (OEIS
text, CC BY-SA 4.0; still stated on 2026-11-05, "verified for n up to 200".)

**Result.** True for every n ≥ 1. SO(k) = k².

**Argument.** Let S_k be the set of values ±1 ±3 … ±(2k−1). Claim: m ∈ S_k iff |m| ≤ k², k² − m is even
and |m| ≠ k² − 4 (equivalently, for k ≥ 2 the subset sums of {1, 3, …, 2k−1} are [0, k²] minus
{2, k² − 2}). Induction on k with S_{k+1} = (S_k + 2k+1) ∪ (S_k − 2k−1): the forward direction is direct;
backwards, for m ≥ 0 take m − (2k+1) unless it equals −(k² − 4), and then m + (2k+1) works (uses k² ≥ 4k
for k ≥ 4; k ≤ 3 by the exact values of k²; m < 0 is symmetric). Now let (k−1)² < n ≤ k². No j < k works
since n > j². If n = k², j = k works. If d = k² − n is odd, k fails by parity and k + 1 works. If d = 4,
k is excluded, k + 1 fails by parity, k + 2 works (d becomes 4k + 8). Otherwise d is even and ≠ 4, and k works.

Lean: [full proof](A197702/A197702_mathlib.lean).

### [A210445](A210445/): a(n) < n for n > 1 and a(n) < n/2 for n > 47 (least k with kn practical)

**Source.** OEIS [A210445](https://oeis.org/A210445): least positive k with k n practical.
Conjecture (Sun, 2013): "a(n)<n for all n>1, and a(n)<n/2 for all n>47." (OEIS text,
CC BY-SA 4.0.)

**Result.** True.

**Argument.** Stewart–Sierpiński: m = p_1^e_1 ··· p_r^e_r (p_1 < ... < p_r) is practical iff
p_1 = 2 and p_(i+1) ≤ 1 + σ(p_1^e_1 ··· p_i^e_i) for all i.
- n not prime, largest prime factor P: take k = 2^t with 2^t < P ≤ 2^(t+1) (k = 1 if n is a power
  of 2). In kn the power of 2 is ≥ 2^t, so 1 + σ(2-part) ≥ 2^(t+1) ≥ every odd prime of n:
  kn is practical. k < P ≤ n/2 (n composite) gives both bounds.
- n = p prime: k = 2^t with 2^t < p ≤ 2^(t+1) makes kp practical and k < p, so a(p) < p.
  For a(p) < p/2: k in the family {2^a·105, 2^a·165 : a ≥ 3} is practical, and for p > 11,
  kp is practical iff p ≤ 1 + σ(k). Consecutive σ-values in the family differ by a factor ≤ 1.5,
  the smallest is σ(8·105) = 2880, and k/σ(k) ≤ 0.306 in the family. So for p ≥ 2881 the least k
  in the family with σ(k) ≥ p - 1 has k ≤ 0.306 · 1.5 (p - 1) < p/2. Primes 47 < p < 2881 are
  checked directly.

Lean: [full proof](A210445/A210445_mathlib.lean).

### [A210529](A210529/): a(n) is defined for every n (Dirichlet)

**Source.** OEIS [A210529](https://oeis.org/A210529): a(n) is 1 or the smallest prime making
|a(n)^2 - prime(n)^2| divisible by all primes below √prime(n). Conjecture: "a(n) is defined for
all positive integers n." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Let p = prime(n) and Q the product of the primes below √p. p is prime to Q (all those
primes are smaller than p). By Dirichlet's theorem there are infinitely many primes a ≡ p (mod Q);
any such a ≠ p gives Q | a - p | a^2 - p^2. So the search in the definition terminates.

Lean: [full proof](A210529/A210529_mathlib.lean).

### [A210826](A210826/): multiplicative with Dirichlet g.f. ζ(3s)/ζ(s)

**Source.** OEIS [A210826](https://oeis.org/A210826): defined by sum_{n≥1} a(n) x^n/(1 - x^n) =
sum_{n≥1} x^(n^3). Conjecture (Mathar, 2012): "this is a multiplicative sequence with Dirichlet
g.f. zeta(3s)/zeta(s) and inverse Mobius transform in A010057." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Comparing coefficients of x^n, the Lambert series says sum_{d|n} a(d) = [n is a cube]
= A010057(n), i.e. the inverse Möbius transform of a is A010057, and a = μ * A010057 (Dirichlet
convolution). Both factors are multiplicative, so a is; its Dirichlet series is
ζ(3s) · (1/ζ(s)). At prime powers a(p^e) = [3 | e] - [3 | e - 1] = -1 + ((e + 2) mod 3) (the
formula now in the entry, Cloitre 2012).

Lean: [full proof](A210826/A210826_mathlib.lean).

### [A212843](A212843/): Carmichael numbers with prime factors ≡ 1 (mod 10)

**Source.** OEIS [A212843](https://oeis.org/A212843), conjectures by Marius Coman (2012):
(1) "only Carmichael numbers of the form 10n+1 can have prime divisors of the form 10k+1";
(2) "all Carmichael numbers C (not only with three prime divisors) of the form 10n+1 that have
only prime divisors of the form 10k+1 can be written as C = (30a+1)*(30b+1)*(30c+1),
C = (30a+11)*(30b+11)*(30c+11), or C = (30a+1)*(30b+11)*(30c+11). In other words, there are no
numbers of the form C = (30a+1)*(30b+1)*(30c+11)." (OEIS text, CC BY-SA 4.0.)

**Reading.** "Not only with three prime divisors" means the three factors may be composite
(products of prime factors). The "in other words" sentence is not equivalent to (2) under this
reading, so it is treated separately.

**Result.** - (1) True.
- (2) True: every such C can be written in one of the three listed forms.
- The "in other words" sentence is true for Carmichael numbers with exactly three prime factors
  and **false** in general: C = 1044430736441 = 41·191·281·521·911 (a Carmichael number, all five
  primes ≡ 11 mod 30) equals 7831 · 146401 · 911 with 7831 ≡ 146401 ≡ 1 and 911 ≡ 11 (mod 30).
  Four such C (five prime factors, all ≡ 11 mod 30) occur below 10^13.

**Argument.** - (1) If a prime p ≡ 1 (mod 10) divides C, Korselt gives 10 | p - 1 | C - 1.
- Primes ≡ 1 (mod 10) are ≡ 1 or 11 (mod 30) (21 is excluded by 3), and products of such numbers
  stay in {1, 11} mod 30 (11^2 ≡ 1). A prime factor ≡ 1 (mod 30) gives 3 | p - 1 | C - 1, so
  C ≡ 1 (mod 3); since 11 ≡ 2 (mod 3), C then has an even number of prime factors ≡ 11 (mod 30)
  and C ≡ 1 (mod 30).
- (2) Group the prime factors into three nonempty blocks. If C ≡ 1 (mod 30), any grouping has an
  even number of blocks ≡ 11: forms (1,1,1) or (1,11,11). If C ≡ 11 (mod 30), all primes are
  ≡ 11 and their number r is odd ≥ 3; put one prime in each of two blocks and the rest (odd count)
  in the third: form (11,11,11).
- Three prime factors: (30a+1)(30b+1)(30c+11) with 30a+1 prime forces C ≡ 1 (mod 3), but the
  product is ≡ 2 (mod 3). With r ≥ 5 primes all ≡ 11 (mod 30) (r odd), pairing four of them gives
  the form (1,1,11); the example above is one.

Lean: [full proof](A212843/A212843_mathlib.lean).

### [A214305](A214305/): Coman's residue conjecture for Poulet numbers fails

**Source.** OEIS [A214305](https://oeis.org/A214305) (Fermat pseudoprimes to base 2 with two
prime factors), conjecture 2 by Marius Coman (2012): "Any Poulet number p2 divisible by d can be
written as (p1 - d)*n + d, where n is a positive integer, if there exists a smaller Poulet number p1
with two prime factors divisible by d." (OEIS text, CC BY-SA 4.0.) Conjectures 1 and 3 assert
infinitely many such p2 for d the largest prime factor of p1.

**Reading.** d is not specified in conjecture 2. Two readings: d any prime of p1, or (as in
conjectures 1 and 3) d the largest prime factor of p1.

**Result.** Conjecture 2 is false under both readings.
- d any prime: p1 = 341 = 11·31, p2 = 561 = 3·11·17, d = 11: 561 - 11 = 550 is not a multiple of
  341 - 11 = 330.
- d largest: p1 = 23377 = 97·241, p2 = 34945 = 5·29·241, d = 241: 34704 is not a multiple of 23136.
  23377 is the only two-factor Poulet number below 34945 with largest factor 241, so this also
  defeats the reading "for some qualifying p1". Another: p1 = 5461 = 43·127, p2 = 55245 = 3·5·29·127.
Conjectures 1 and 3 ("infinitely many") are not addressed.

**Argument.** Direct computation (Fermat condition 2^(n-1) ≡ 1 mod n, factorisations, the failed
divisibilities).

Lean: [full proof](A214305/A214305_mathlib.lean).

### [A214449](A214449/): A214449 is not A118168 with two 1s deleted (first mismatch n = 188)

**Source.** OEIS [A214449](https://oeis.org/A214449): least m > 0 with n! ≤ m^m (offset 1).
Conjecture: "this sequence results from A118168 by deleting the first two 1s." (OEIS text,
CC BY-SA 4.0.) A118168(n) = the x minimizing |x^x - n!| (offset 0: 1, 1, 1, 2, 3, 3, ...).

**Reading.** Deleting the first two terms of A118168 aligns A214449(n) with A118168(n+1).

**Result.** False. A214449(188) = 159 but A118168(189) = 158. There are 24 mismatches for
n ≤ 1500 (188, 248, 271, 310, ...).

**Argument.** 158^158 < 188! ≤ 159^159, so A214449(188) = 159. 189! ≈ 208·158^158 lies between
158^158 and 159^159 ≈ 431·158^158 and is nearer to 158^158, so A118168(189) = 158 (x^x is
increasing, so the minimizer is a neighbour).

Lean: [full proof](A214449/A214449_mathlib.lean).

### [A214900](A214900/): every n is a sum of three squares and a fourth power

**Source.** OEIS [A214900](https://oeis.org/A214900): number of ordered representations
n = x² + y² + z² + w⁴. Conjecture (Sun, 2012): "a(n) != 0, that is, all numbers are sums of three
squares and one fourth power." (OEIS text, CC BY-SA 4.0.)

**Result.** True (given Legendre's three-square theorem).

**Argument.** Legendre: m is a sum of three squares iff m is not 4^a(8b+7). If n is not of that
form, w = 0. Otherwise n = 4^a(8b+7):
- a = 0: n - 1 = 8b + 6 ≡ 2 (mod 4) is not excluded; w = 1.
- a = 1: n - 1 = 32b + 27 is odd and ≡ 3 (mod 8); w = 1.
- a ≥ 2: n = 16m with m < n; if m = x² + y² + z² + w⁴ then n = (4x)² + (4y)² + (4z)² + (2w)⁴.

Lean: [witness](A214900/A214900.lean).

### [A214970](A214970/): L(2k-1) and L(2k)+1 divide their base-φ → base-φ² images

**Source.** OEIS [A214970](https://oeis.org/A214970): integers n dividing f(n), where f is the
change-of-base function of A214969 with b = φ and c = φ² (write n in base φ by the greedy
algorithm, n = sum d_i φ^i, then f(n) = sum d_i φ^(2i)). Conjecture (Kimberling, 2012): "L(2k-1)
and L(2k)+1 are terms of the sequence, for all positive integers k, where L=A000032 (Lucas
numbers)." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** The greedy base-φ expansion of an integer is its standard representation (digits
0/1, finitely many, no two adjacent 1s), which is unique (Bergman 1957). Using φ - φ^(-1) = 1 and
L(m) = φ^m - φ^(-m) for odd m:
sum_{j=-(k-1)}^{k-1} φ^(2j) = (φ^(2k-1) - φ^(-(2k-1)))/(φ - φ^(-1)) = L(2k-1). The digits sit at
even positions only, so this is the standard representation of L(2k-1), and
f(L(2k-1)) = sum φ^(4j) = (φ^(4k-2) - φ^(-(4k-2)))/(φ^2 - φ^(-2)) = F(4k-2) = F(2k-1) L(2k-1),
using φ^2 - φ^(-2) = √5. Likewise L(2k) + 1 = φ^(2k) + 1 + φ^(-2k) is a standard representation
for k ≥ 1, and f(L(2k)+1) = φ^(4k) + 1 + φ^(-4k) = L(4k) + 1 = L(2k)^2 - 1 =
(L(2k) - 1)(L(2k) + 1).

Lean: [full proof](A214970/A214970_mathlib.lean).

### [A215461](A215461/): 2n is a prime plus an odd nonprime for every n > 5

**Source.** OEIS [A215461](https://oeis.org/A215461): number of ordered decompositions of 2n into
an odd prime and an odd nonprime (1 counts as nonprime). Conjecture: "a(n) is never zero for
n > 5, verified to 10^9." (OEIS text, CC BY-SA 4.0.)

**Result.** True (elementary).

**Argument.** 2n - 3, 2n - 5, 2n - 7 are three odd numbers with distinct residues mod 3, so one is
divisible by 3; for n > 5 it exceeds 3, so it is an odd nonprime, and its partner 3, 5 or 7 is
prime.

Lean: [full proof](A215461/A215461.lean).

### [A215462](A215462/): 2n is a sum of two odd nonprimes for n > 19; eventual ordering

**Source.** OEIS [A215462](https://oeis.org/A215462): number of ordered decompositions of 2n into
two odd nonprimes (1 counts as nonprime). Conjectures: "a(n) is never zero for n > 19, verified to
10^9" and "a(n) > A215461(n) > A002372(n) for sufficiently large n." (OEIS text, CC BY-SA 4.0.)

**Result.** Both true; both proved in Lean 4 + Mathlib. Conjecture 2 holds for every n ≥ 2^(10^9)
(Lean bound, far from optimal); numerically the last failure below 10^6 is n = 1546.

**Argument.** - Conjecture 1. 9, 25, 35 are odd nonprimes with residues 0, 1, 2 mod 3, so for one of them c,
  d = 2n - c is divisible by 3; d is odd, and for n ≥ 22, d ≥ 9, so d is nonprime. n = 20: 40 =
  25 + 15; n = 21: 42 = 15 + 27.
- Conjecture 2, counting. The n ordered pairs (2i+1, 2j+1) with i + j = n - 1 split as
  g + b + a = n with g = A002372(n) (both prime), b = A215461(n) (exactly one), a = a(n) (neither).
  With P = #{i < n : 2i+1 prime} and π = π(2n): P ≤ π ≤ P + 1, the right entries are also prime
  for at most π indices, so a ≥ n - 2π, b ≤ 2π and b ≥ P - g ≥ π - 1 - g. Hence b < a once
  4π < n, and g < b once 2g + 1 < π. Also g ≤ G(n) = #{m < 2n : m, 2n - m prime}.
- Chebyshev (Mathlib `Chebyshev.pi_ge`, `Chebyshev.pi_le_log4_mul_div`): for 2^(20j) ≤ n < 2^(20j+20),
  j ≥ 5·10^7, n ≤ 21 j π and 4π < n.
- Sieve. Let Y = w^4, Q = primorial(Y), h' = 2n(Q - 1). For m < 2n and a prime q ∣ Q,
  m + h' + (2n - m) = 2nQ, so q ∣ m(m + h') iff q ∣ m(2n - m). Every m < 2n with m, 2n - m prime
  and both > Y survives the FAM-twin-primes Selberg sieve on m(m + h') with sifting primes ≤ Y,
  so G(n) ≤ 2(Y + 1) + (sifted count). Selberg's bound gives sifted ≤ 2n/S + Y^4. For the main term
  S use the completely multiplicative f with f(p) = 2/p for p ∤ 2n and f(p) = 1/p for p ∣ 2n
  (f(p) ≤ ν(p) because the local root count of m(m + h') is 2 for p ∤ 2n and at least 1 always).
  The number of factorisations m = ab with a coprime to 2n is at most m f(m), so
  S ≥ (∑_{a ≤ w, (a,2n)=1} 1/a)(∑_{b ≤ w} 1/b) ≥ log(w+1)^2 / K(2n), K(c) = ∏_{p∣c} p/(p-1).
  Result: G(n) ≤ 2(w^4 + 1) + K(2n)·2n/log(w+1)^2 + w^16. Only one factor K appears.
- K bound. (p/(p-1))^2 ≤ p/(p-2) for odd p, and ∏ p/(p-2) over any k distinct odd numbers ≥ 3 is at
  most 2k + 1 (the worst case 3, 5, …, 2k+1 telescopes). So K(c)^2 ≤ 4(2ω(c) + 1) with
  2^ω(c) ≤ c, i.e. K(2n) = O((log n)^(1/2)) = o(log n); explicitly K(2n) ≤ j/500.
- With w = 2^j: G(n) ≤ n/(50 j), so 2g + 1 ≤ n/(25 j) + 1 < n/(21 j) ≤ π.

Lean: [full proof](A215462/A215462_conj2_mathlib.lean).

### [A217448](A217448/): a(n) exists for every n (CRT)

**Source.** OEIS [A217448](https://oeis.org/A217448): least k > 0 such that 1 + n^2 and 1 + (n+k)^2
have the same smallest prime factor. Conjecture: "a(n) exists for all n." (OEIS text,
CC BY-SA 4.0.)

**Result.** True.

**Argument.** Let q = spf(1 + n^2). Choose k by the Chinese remainder theorem with
k ≡ 0 (mod q), and for each prime ℓ < q: if ℓ = 2, n + k even (then 1 + (n+k)^2 is odd); if ℓ is
odd, n + k avoids the at most two roots of x^2 ≡ -1 (mod ℓ) (ℓ ≥ 3 leaves at least one residue).
The moduli are distinct primes, so such k > 0 exists. Then (n+k)^2 ≡ n^2 ≡ -1 (mod q), so
q | 1 + (n+k)^2, and no smaller prime divides it: spf(1 + (n+k)^2) = q. (If q = 2, n is odd and any
even k works.)

Lean: [full proof](A217448/A217448_mathlib.lean).

### [A217876](A217876/): adjacent transpositions in a random involution are asymptotically Poisson(1)

**Source.** [A217876](https://oeis.org/A217876), triangle T(n,k): the number of involutions of [n] whose
cycle form has exactly k adjacent transpositions (i i+1); row sums A000085 = I(n). Comment by David Callan
(2012): "Conjecture: The asymptotic distribution of adjacent transpositions in involutions is Poisson
with mean 1." (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05.)

**Reading.** X_n = number of adjacent transpositions of a uniform involution of [n]; the claim is
X_n → Poisson(1) in distribution, i.e. (X_n is N-valued) P(X_n = j) = T(n,j)/I(n) → e^{−1}/j! for every j.

**Result.** True: T(n,j)/I(n) → e^{−1}/j! for every j ≥ 0. Also E C(X_n,i) → 1/i!.

**Argument.** A set of i pairwise disjoint adjacent pairs of [n] can be chosen in C(n−i,i) ways, and the
involutions containing all of them as 2-cycles number I(n−2i). So b_i(n) := E C(X_n,i) =
C(n−i,i)·I(n−2i)/I(n) and, by inclusion–exclusion, T(n,j) = Σ_i (−1)^{i+j} C(i,j)·C(n−i,i)·I(n−2i).
From I(n+2) = I(n+1) + (n+1)I(n), y(n) = I(n+1)/I(n) satisfies √(n+1) ≤ y(n) ≤ √(n+1) + 1 (induction), so
c(n) = (n+1)I(n)/I(n+2) = 1/(1 + y(n)/(n+1)) → 1 and c(n) ≤ 1. The recursion
b_{i+1}(n+2) = (1/(i+1))·((n+1−i)/(n+1))·c(n)·b_i(n) gives b_i(n) → 1/i! and 0 ≤ b_i(n) ≤ 1/i!. Then
T(n,j)/I(n) = Σ_i (−1)^{i+j} C(i,j) b_i(n), and dominated convergence for series (Tannery, bound
C(i,j)/i! ≤ 2^i/i!) gives the limit Σ_i (−1)^{i+j} C(i,j)/i! = (1/j!) Σ_l (−1)^l/l! = e^{−1}/j!.
No method-of-moments theorem is needed.

Lean: [checked](A217876/A217876_mathlib.lean).

### [A221650](A221650/): P(n,j,k) = [k | j] p(n-j) counts partitions with at least j/k parts k

**Source.** OEIS [A221650](https://oeis.org/A221650): tetrahedron P(n,j,k) = T(j,k) p(n-j), T(j,k) =
1 if k | j else 0. Conjecture 1: "P(n,j,k) is the number of partitions of n that contain at least
m parts of size k, where m = j/k, if k divides j otherwise P(n,j,k) = 0." Conjecture 2: "P(n,j,k) is
the number of parts that are the m-th part of size k in all partitions of n ..." (O. Omar, 2013;
OEIS text, CC BY-SA 4.0.)

**Result.** Both true.

**Argument.** Removing m copies of k from a partition of n with at least m parts equal to k is a
bijection onto the partitions of n - mk = n - j (inverse: add m copies of k). So the count is
p(n - j). Conjecture 2 counts, over all partitions of n, the parts that are the m-th occurrence of
k; each partition with at least m parts k contributes exactly one such part, so the count is the
same.

Lean: [full proof](A221650/A221650_mathlib.lean).

### [A225001](A225001/): floor(1/frac(e^(4/(5n)))) = A047203(n) for n > 1

**Source.** OEIS [A225001](https://oeis.org/A225001), now a dead entry ("Duplicate of A047203").
Its Mathematica program defines a(n) = floor(1/FractionalPart[(e^(4/5))^(1/n)]). Conjecture
(R. J. Mathar, 2013): "a(n) = A047203(n), n>1." A047203 = numbers ≡ 0, 2, 3, 4 (mod 5),
A047203(n) = floor((5n-2)/4). (OEIS text, CC BY-SA 4.0.)

**Result.** True. (The scan recorded only that the entry was merged; the identity is proved here.)

**Argument.** Let u = 4/(5n). For n ≥ 2, u ≤ 2/5 < log 2, so frac(e^u) = e^u - 1. For u > 0,
1/u - 1/2 < 1/(e^u - 1) < 1/u - 1/2 + u/12 (from the Bernoulli expansion; both bounds are
standard). Hence 1/frac(e^u) = 5n/4 - 1/2 + δ with 0 < δ < u/12 = 1/(15n) ≤ 1/30. The number
5n/4 - 1/2 = (5n-2)/4 has fractional part 0, 1/4, 1/2 or 3/4, so adding δ < 1/4 does not cross an
integer: a(n) = floor((5n-2)/4) = A047203(n). (n = 1: a(1) = 4 ≠ A047203(1) = 0, hence "n > 1".)

Lean: [full proof](A225001/A225001_mathlib.lean).

### [A226661](A226661/): 3x+k cycles with exactly n odd elements exist for every n

**Source.** OEIS [A226661](https://oeis.org/A226661): Smallest positive integer k (or 0 if no such k) with a primitive cycle of positive integers, exactly n of which are odd, under iteration by the Collatz-like 3x+k function. Conjecture: "a(n)>0 for all n." (OEIS text, CC BY-SA 4.0.) A cycle is primitive
if its elements are not a common multiple of the elements of another cycle, i.e. the gcd of its
elements is 1.

**Result.** True: an explicit primitive cycle exists for every admissible size, so a(n) > 0
(this gives an upper bound for a(n), not its value).

**Argument.** T_k(x) = x/2 (x even), (3x+k)/2 (x odd). Take m ≥ 1 with 2^(n+m) > 3^n and gcd(3^n - 2^n, 2^m - 1) = 1, and k = 2^(n+m) - 3^n (odd, prime to 3). With y_j = 3^j 2^(n-j) (2^m - 1) and x_j = y_j - k (0 ≤ j ≤ n): x_0 = 3^n - 2^n > 0; for j < n, x_j is odd and T_k(x_j) = (3y_j - 2k)/2 = y_(j+1) - k = x_(j+1); x_n = 2^m (3^n - 2^n), and m halvings return to x_0. The n odd elements increase strictly and the m even ones are 2^i (3^n - 2^n), 1 ≤ i ≤ m, so this is a cycle with exactly n odd elements. Primitive: the gcd of the elements divides x_0 and 2x_1 - 3x_0 = k, and gcd(x_0, k) = gcd(3^n - 2^n, 2^n(2^m - 1)) = gcd(3^n - 2^n, 2^m - 1) = 1. A suitable m exists: any prime m > 3^n/2, since a prime factor q of 2^m - 1 has ord_q(2) = m, so q ≡ 1 (mod m) and q > 3^n > 3^n - 2^n.

Lean: [full proof](A226661/A226661_mathlib.lean).

### [A226676](A226676/): 3x-k cycles of every length N ≥ 3 exist

**Source.** OEIS [A226676](https://oeis.org/A226676): Smallest positive integer k (or 0 if no such k) with a primitive cycle of n positive integers under iteration by the Collatz-like 3x-k function. Conjecture: "For n>2, a(n)>0." (OEIS text, CC BY-SA 4.0.) A cycle is primitive
if its elements are not a common multiple of the elements of another cycle, i.e. the gcd of its
elements is 1.

**Result.** True: an explicit primitive cycle exists for every admissible size, so a(n) > 0
(this gives an upper bound for a(n), not its value).

**Argument.** T_k(x) = x/2 (x even), (3x-k)/2 (x odd). For N ≥ 3 put n = N - 1 ≥ 2, k = 3^n - 2^(n+1) = 3^(N-1) - 2^N (positive, odd, prime to 3) and x_j = k + 3^j 2^(n-j), 0 ≤ j ≤ n. For j < n, x_j is odd and T_k(x_j) = (3x_j - k)/2 = k + 3^(j+1) 2^(n-j-1) = x_(j+1); x_n = k + 3^n = 2(3^n - 2^n) is even and T_k(x_n) = 3^n - 2^n = x_0. The odd x_j increase strictly, so the cycle has exactly n + 1 = N elements. Primitive: the gcd of the elements divides x_0 and k, and gcd(3^n - 2^n, 3^n - 2^(n+1)) = gcd(3^n - 2^n, 2^n) = 1 because 3^n - 2^n is odd. (Same construction as OEIS-A226677.)

Lean: [full proof](A226676/A226676_mathlib.lean).

### [A226677](A226677/): 3x-k cycles with exactly n odd elements exist for every n

**Source.** OEIS [A226677](https://oeis.org/A226677): Smallest positive integer k (or 0 if no such k) with a primitive cycle of positive integers, exactly n of which are odd, under iteration by the Collatz-like 3x-k function. Conjecture: "a(n)>0 for all n." (OEIS text, CC BY-SA 4.0.) A cycle is primitive
if its elements are not a common multiple of the elements of another cycle, i.e. the gcd of its
elements is 1.

**Result.** True: an explicit primitive cycle exists for every admissible size, so a(n) > 0
(this gives an upper bound for a(n), not its value).

**Argument.** T_k(x) = x/2 (x even), (3x-k)/2 (x odd). n = 1: the cycle {1} of T_1. For n ≥ 2 put k = 3^n - 2^(n+1) (positive, odd, prime to 3) and x_j = k + 3^j 2^(n-j), 0 ≤ j ≤ n. For j < n, x_j is odd and T_k(x_j) = x_(j+1); x_n = 2(3^n - 2^n) is even and T_k(x_n) = x_0 = 3^n - 2^n. The odd x_j (j < n) increase strictly, so this is a cycle of n + 1 elements with exactly n odd ones. Primitive: the gcd of the elements divides x_0 and 2x_1 - 3x_0 = -k, and gcd(3^n - 2^n, 3^n - 2^(n+1)) = gcd(3^n - 2^n, 2^n) = 1 since 3^n - 2^n is odd.

Lean: [full proof](A226677/A226677_mathlib.lean).

### [A227500](A227500/): (b(n) - a(n))/c(n) is 0, 0 followed by the Fibonacci numbers

**Source.** [A227500](https://oeis.org/A227500) (offset 0), P. Curtz, Jul 13 2013: a(0) = a(1) = 0 and, for n > 1,
a(n) = numerator(r(n)) with r(n) = r(n-1) + r(n-2) + A027641(n-2)/A027642(n-2), r(0) = r(1) = 0. A comment applies the
same transform to the second Bernoulli numbers A164555(n)/A027642(n), giving b(n)/c(n), and states: "Conjecture:
(b(n)-a(n))/c(n) = 0, 0, 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ..., that is two 0 followed by A000045." Alcover
confirmed 100 terms (Jul 19 2013). (OEIS text, CC BY-SA 4.0, revision #20 of Jul 21 2013, checked 2026-11-06.)

**Reading.** A027641/A027642 are the Bernoulli numbers with B(1) = -1/2; A164555/A027642 are the same numbers with
B(1) = +1/2 (they agree at every other index). c(n) is the reduced denominator, which the comment takes to be shared
by both fractions; this is part of what is proved.

**Result.** True: for all n >= 2, r2(n) - r1(n) = F(n-2) (Fibonacci, F(0) = 0), and r2(0) - r1(0) = r2(1) - r1(1)
= 0. Since the difference is an integer, both fractions have the same reduced denominator c(n), and
(b(n) - a(n))/c(n) = F(n-2) for n >= 2 and 0 for n < 2.

**Argument.** The two transforms are linear with the same recurrence, so d(n) = r2(n) - r1(n) satisfies
d(0) = d(1) = 0 and d(n) = d(n-1) + d(n-2) + (B2(n-2) - B1(n-2)), where the last term is 1 for n = 3 and 0 otherwise.
Hence d(2) = 0, d(3) = 1, d(4) = 1, and from then on d follows the Fibonacci recurrence, so d(n) = F(n-2) for
n >= 2. Adding an integer to a rational number does not change its reduced denominator, so r1(n) and r2(n) share
c(n), and b(n) - a(n) = d(n) c(n).

Lean: [full proof](A227500/A227500_mathlib.lean).

### [A227553](A227553/): number of solutions of x^2 - y^2 - z^2 ≡ 1 (mod p^s)

**Source.** OEIS [A227553](https://oeis.org/A227553): number of solutions of x^2 - y^2 - z^2 ≡ 1
(mod n). Conjecture: "a(2) = 4; if s > 1 then a(2^s) = 2^(2s-1); if p == 1 (mod 4) then a(p^s) =
(p+1)*p^(2s-1); if p == 3 (mod 4) then a(p^s) = (p-1)*p^(2s-1)." (OEIS text, CC BY-SA 4.0.)
(The scan's record misquotes the odd case as p(p±1)^(2s-1); the entry's formula is the one above
and is the one proved.)

**Result.** True.

**Argument.** - p odd, s = 1. Substitute u = x - y, v = x + y (invertible since 2 is a unit): uv = 1 + z^2. For
  each z, if 1 + z^2 ≢ 0 there are p - 1 pairs (u, v); if 1 + z^2 ≡ 0 there are 2p - 1. The number of
  z with z^2 ≡ -1 is 2 if p ≡ 1 (mod 4) and 0 if p ≡ 3. Total p(p-1) + 2p = p(p+1), resp. p(p-1).
- p odd, lifting. Every solution mod p is nonsingular (the gradient (2x, -2y, -2z) vanishes only at
  0, which is not a solution), so by Hensel each solution mod p^s has exactly p^2 lifts mod
  p^(s+1): a(p^s) = (p ± 1) p · p^(2(s-1)) = (p ± 1) p^(2s-1).
- p = 2. a(2) = 4 directly. For s ≥ 2: x must be odd (if x is even, y^2 + z^2 ≡ x^2 - 1 ≡ 3
  (mod 4), impossible). For given y, z the number of x mod 2^s with x^2 ≡ A := 1 + y^2 + z^2 is 2
  (s = 2) or 4 (s ≥ 3) when A ≡ 1 (mod 4) resp. (mod 8), and 0 otherwise. A ≡ 1 (mod 8) iff
  y^2 + z^2 ≡ 0 (mod 8) iff y ≡ z ≡ 0 or y ≡ z ≡ 2 (mod 4): 2^(2s)/8 pairs; A ≡ 1 (mod 4) iff y,
  z both even: 2^(2s)/4 pairs. So a(4) = 2·4 = 8 and a(2^s) = 4·2^(2s-3) = 2^(2s-1) for s ≥ 3.

Lean: [full proof](A227553/A227553_mathlib.lean).

### [A228931](A228931/): the optimal ascending continued fraction of √2 - 1 follows a(k+1) = a(k)^2 - 2

**Source.** OEIS [A228931](https://oeis.org/A228931): optimal ascending continued fraction (OACF,
defined in A228929) of √2 - 1: 2, -6, 34, 1154, 1331714, ... Conjecture (Artico, 2013): "The terms
from a(3) are all positive and can be generated by the recurrence relation a(k+1) = a(k)^2 - 2."
(OEIS text, CC BY-SA 4.0.)

**Reading.** A228929's algorithm: z_0 = x - floor(x); r_k = round(1/|z_k|),
a(k+1) = sign(z_k) r_k, z_(k+1) = |z_k| r_k - 1.

**Result.** True.

**Argument.** Lemma: if |z_k| = 1/U for a real quadratic unit U > 2 of norm +1, then
U + 1/U = t ∈ Z, r_k = round(U) = t (since 0 < 1/U < 1/2), and
z_(k+1) = t/U - 1 = 1/U^2 > 0. By induction all later z are U^(-2^j) > 0 and the later terms are
U^(2^j) + U^(-2^j) > 0, each the square of the previous minus 2.
For x = √2 - 1: r_0 = round(√2 + 1) = 2, a(1) = 2, z_1 = 2(√2 - 1) - 1 = -(3 - 2√2), so
|z_1| = 1/U with U = 3 + 2√2 (norm 1). Hence a(2) = -6, and from z_2 on the lemma gives
a(3) = 34, a(k+1) = a(k)^2 - 2 for k ≥ 2 (in particular from a(3)), all positive.

Lean: [full proof](A228931/A228931_mathlib.lean).

### [A228933](A228933/): the optimal ascending continued fraction of 1/φ follows a(n) = a(n-1)^2 - 2 from the fourth term

**Source.** OEIS [A228933](https://oeis.org/A228933): optimal ascending continued fraction
(A228929) of φ - 1 = 1/φ: 2, 4, -18, 322, ... Conjecture (Artico, 2013): "The golden ratio (phi)
expansion exhibits from the fourth term the recurrence relation a(n) = a(n-1)^2 - 2 described in
A228931." (OEIS text, CC BY-SA 4.0.)

**Result.** True.

**Argument.** Same lemma as OEIS-A228931 (if |z_k| = 1/U, U > 2 a unit of norm +1, then every later
step squares U and the terms satisfy t ↦ t^2 - 2). For x = 1/φ: r_0 = round(φ) = 2, a(1) = 2,
z_1 = 2/φ - 1 = φ^(-3). r_1 = round(φ^3) = 4 because φ^3 - φ^(-3) = L_3 = 4 (φ^3 has norm -1),
a(2) = 4, z_2 = 4φ^(-3) - 1 = (φ^3 - φ^(-3))φ^(-3) - 1 = -φ^(-6). With U = φ^6 = 9 + 4√5 (norm +1,
U + 1/U = L_6 = 18): a(3) = -18, and from there a(n) = a(n-1)^2 - 2 (a(4) = 322, ...).

Lean: [full proof](A228933/A228933_mathlib.lean).

### [A228934](A228934/): the optimal ascending continued fraction of √44 − 6 follows a two-step recurrence

**Source.** OEIS [A228934](https://oeis.org/A228934) (offset 1): optimal ascending continued fraction
(OACF, defined in A228929) of √44 − 6: 2, 4, 15, −99, −199, −800, −79201, −316808, ... Conjecture
(G. Artico, Sep 2013): "The terms of the expansion of sqrt(x) are all negative starting from a(4) and
satisfy these recurrence relations for n>=3: a(2n) = 4*a(2n-1) - 4 and a(2n+1) = -2*a(2n-1)^2 + 1."
(OEIS text, CC BY-SA 4.0; still stated on 2026-11-05. "sqrt(x)" means the expansion of √44 − 6.)

**Reading.** A228929's algorithm: z_0 = x − ⌊x⌋; r_k = round(1/|z_k|), a(k+1) = sign(z_k) r_k,
z_(k+1) = |z_k| r_k − 1. No 1/|z_k| is a half-integer here, so the rounding convention does not matter.

**Result.** True.

**Argument.** Let s = √44 and ε = 199 + 30s (a unit: 1/ε = 199 − 30s, ε + 1/ε = 398). Direct
computation: z_0 = s − 6, z_1 = 2s − 13, z_2 = 8s − 53, z_3 = 120s − 796 = −4/ε, with terms 2, 4, 15, −99
(1/|z_3| = ε/4 = 99.4997...), and z_4 = 78803 − 11880s = 1/ε² − 2/ε.
Two-step lemma: let G ≥ 11 with G + 1/G = 2t, t ∈ ℤ, and z_k = 1/G² − 2/G < 0. Then
1/|z_k| = G²/(2G−1) = t + (G−1)²/(2G(2G−1)), so r_k = t, a(k+1) = −t and
z_(k+1) = −(G−1)²/(2G³). Next 1/|z_(k+1)| = 2G³/(G−1)² = (4t+4) + (4G²−2)/(G(G−1)²), so
r_(k+1) = 4t+4, a(k+2) = −(4t+4), and z_(k+2) = 1/G⁴ − 2/G². The hypothesis holds again for G²
with t' = 2t² − 1. Starting from G = ε, t = 199 at k = 4: a(5) = −199, a(6) = −800, and in general
a(2n−1) = −t, a(2n) = −(4t+4) = 4a(2n−1) − 4, a(2n+1) = −(2t² − 1) = −2a(2n−1)² + 1 for n ≥ 3;
all these terms are negative.

Lean: [full proof](A228934/A228934_mathlib.lean).

### [A229910](A229910/): primitive roots g with g + g⁻¹ primitive (proved); the finite-field version fails at q = 25, 121

**Source.** OEIS [A229910](https://oeis.org/A229910): a(n) = number of 0 < g < p = prime(n) with g
and g + g⁻¹ primitive roots mod p. Conjectures (Z.-W. Sun, 2013): "a(n) > 0 for all n > 6", i.e.
every prime p > 13 has such g; and "Let F be a finite field with |F| = q > 13. Then there is a
primitive root g of F ... such that g + g^{-1} is also a primitive root of F. If q > 61, then there
exists a primitive root g of F such that g - g^{-1} is also a primitive root of F."
(OEIS text, CC BY-SA 4.0.)

**Result.** - Prime case: true, by Cohen, Oliveira e Silva, Sutherland, Trudgian, Corollary 2 (exceptions for
  g + g⁻¹ are q ∈ {2, 3, 4, 5, 7, 9, 13, 25, 121}; the primes among them are ≤ 13).
- Finite-field case: false as stated. q = 25 and q = 121 have no primitive g with g + g⁻¹
  primitive, and q = 121 > 61 has none with g - g⁻¹ primitive.

**Argument.** Prime case: the cited theorem (character sums plus a computer search). Field case:
exhaustive search in F_25 = F_5[√2] and F_121 = F_11[√2].

Lean: [witness](A229910/A229910.lean).

### [A024812](A024812/): A024812(k) = (A024813(k) + k − 1)/2

**Source.** [A024812](https://oeis.org/A024812), comment by L. E. Jeffery (2013): "Conjecture (verified for
k <= 10^6 by M. F. Hasler): A024812(k) = (A024813(k)+k-1)/2, k=1,2,...." (OEIS text, CC BY-SA 4.0.)
A024812 = values n taken by f(m) = floor(cot(π/(2m))) for exactly one m; A024813 = the m with
f(m−1) < f(m) < f(m+1).

**Result.** True. Proved in the OEIS by H. Rungta (A024813, Oct 2026); re-derived here. (Barker's 2014
recurrence for A024812 is a separate claim, already marked false in the entry.)

**Argument.** g(x) = cot(π/(2x)) has g'(x) = (2/π)·((π/(2x))/sin(π/(2x)))^2, decreasing in x ≥ 2 with
2/π < g' ≤ π/4. By the mean value theorem g(m+1) − g(m) < 1 and g(m+2) − g(m) > 1 for m ≥ 2, and
f(1) = 0, f(2) = 1. So f is nondecreasing, hits every positive integer, each once or twice. If
n = A024812(k) is taken once, at m = A024813(k), then the positions 1..m hold f(1) = 0, the n − 1 values
1..n−1 (k − 1 of them once, n − k twice) and n itself: m = 1 + (k−1) + 2(n−k) + 1 = 2n − k + 1.

Lean: [full proof](A024812/A024812_mathlib.lean).

### [A030210](A030210/): coefficients of (η(q)η(q^5))^4 satisfy |a(p)| < 2p^(3/2)

**Source.** OEIS [A030210](https://oeis.org/A030210) (offset 1): expansion of (eta(q) * eta(q^5))^4 in powers
of q. Conjecture (M. Somos, Oct 31 2005): "|a(p)| < 2*p^(3/2) for p prime." (OEIS text, CC BY-SA 4.0;
revision #45.)

**Result.** True for every prime p.

**Argument.** f(τ) = η(τ)^4 η(5τ)^4 is a cusp form of weight 4 on Γ_0(5) with trivial character (an
eta-quotient with Σ δr_δ = 24, Σ (5/δ)r_δ = 24, character from 5^4, a square; per the entry it is no. 13 in Martin's list of
multiplicative eta-quotients, Trans. AMS 348 (1996), Table I). S_4(Γ_0(5)) is 1-dimensional and has no old
forms (S_4(SL_2(ℤ)) = 0), so f is the normalised newform LMFDB
[5.4.a.a](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/5/4/a/a/) (q-expansion 1, −4, 2, 8, −5, −8, 6, 0,
−23, ..., eta-quotient η(z)^4η(5z)^4, Atkin–Lehner sign +1 at 5, not CM).

- p ≠ 5. P. Deligne, La conjecture de Weil I, Publ. Math. IHÉS 43 (1974), Théorème 8.2: for a primitive
  (new) holomorphic cusp form on Γ_0(N) of weight k ≥ 2 with character, and p ∤ N, |a_p| ≤ 2p^{(k−1)/2}. With
  N = 5, k = 4: |a(p)| ≤ 2p^{3/2}. Equality would give a(p)^2 = 4p^3, impossible for an integer since p^3 is
  not a square. So |a(p)| < 2p^{3/2}.
- p = 5. For a newform with trivial character and p ∥ N, a_p = −w_p p^{k/2−1} with w_p the Atkin–Lehner
  eigenvalue (Atkin–Lehner 1970; standard, not re-read here). Here w_5 = +1, so a(5) = −5, matching the printed term and
  the entry's formula a(5^e) = (−5)^e. |a(5)| = 5 < 2·5^{3/2} ≈ 22.36.

Lean: needs Mathlib.

### [A063289b](A063289b/): newform dimension formula for Gamma_1(16) (9n/4 is a typo for 9n/2)

**Source.** OEIS wiki, Talk:Conjectures/List, line for A063289: "Conjecture: a(n) = 9*n/4+(-1)^n/4-45/4, n>=3 with first differences in A010710".
[A063289](https://oeis.org/A063289) is "Dimension of the space of weight n cuspidal newforms for Gamma_1(16)",
offset 2, data -1, 2, 7, 11, 16, 20, 25, ... The entry itself now states: a(n) = 9*n/2 + (-1)^n/4 - 45/4 for n >= 3, with first differences in A010710 (R. J. Mathar, Dec 06 2010).

**Reading.** The OEIS data are shifted by one weight: term a(n) is the dimension in weight n - 1
(a(3) is the weight-2 dimension; a(2) = -1 is not a dimension, the true weight-1 dimension is 0).
Below, n is the OEIS index and k = n - 1 the weight.

**Result.** Misstated. At n = 3 the printed formula gives 27/4 - 1/4 - 45/4 = -19/4, not an integer, and its slope 9/4 is half the true growth 9/2 per weight, so it fails in every indexing (the PARI run finds no agreement for n = 3..81 or k = 2..80). It is a transcription of Mathar's formula with 9n/2 written as 9n/4. The first differences of Mathar's formula alternate 4, 5, which is A010710.
The corrected formula is true: a(n) = 9n/2 + (-1)^n/4 - 45/4 for n >= 3 in the OEIS indexing, that is
dim S_k^new(Gamma_1(16)) = 9k/2 - (-1)^k/4 - 27/4 for k >= 2.

**Argument.** The newspace dimension is a fixed finite combination of cusp-space dimensions:
from S_k(Gamma_1(N)) = sum over M | N and d | N/M of the images of S_k^new(Gamma_1(M)) under q -> q^d,
Moebius inversion gives dim S_k^new(Gamma_1(N)) = sum over M | N of beta(N/M) dim S_k(Gamma_1(M)),
with beta = mu * mu. For k >= 3 each dim S_k(Gamma_1(M)) (Cohen-Oesterle) is (k - 1)/12 times a
constant plus a term that depends only on k mod 12 (elliptic and irregular-cusp terms, present only
for M <= 4); the k = 2 term has an extra Eisenstein correction. G. Martin, J. Number Theory 112 (2005)
298-331, Theorem 13 (Gamma_1, k >= 2; Theorem 1 for Gamma_0) writes this out explicitly.
So for k >= 3, on each residue class of k mod 12, the true dimension is linear in k; the corrected
formula has the same shape. Two such functions agree for all k >= 3 once they agree for 24
consecutive k (two values per class). PARI/GP `mfdim([16, k, -1], 0)` agrees with the formula for
k = 2..80, which covers k = 2 and the 24 values k = 3..26.

Lean: —.

### [A063305](A063305/): newform dimension formula for Gamma_1(32) (18n is missing the constant -41)

**Source.** OEIS wiki, Talk:Conjectures/List, line for A063305: "Conjecture: a(n) = 18n".
[A063305](https://oeis.org/A063305) is "Dimension of the space of weight n cuspidal newforms for Gamma_1(32)",
offset 2, data -1, 13, 31, 49, 67, ... The entry itself now states: a(n) = 18*n - 41 for n > 2 (P. Luschny, Mar 04 2012).

**Reading.** The OEIS data are shifted by one weight: term a(n) is the dimension in weight n - 1
(a(3) is the weight-2 dimension; a(2) = -1 is not a dimension, the true weight-1 dimension is 0).
Below, n is the OEIS index and k = n - 1 the weight.

**Result.** Misstated. 18n differs from 18n - 41 by 41 at every n (e.g. a(3) = 13), and from the weight form by 23, so the printed formula is false for every n in either indexing. The constant -41 was dropped.
The corrected formula is true: a(n) = 18n - 41 for n >= 3 in the OEIS indexing, that is
dim S_k^new(Gamma_1(32)) = 18k - 23 for k >= 2.

**Argument.** The newspace dimension is a fixed finite combination of cusp-space dimensions:
from S_k(Gamma_1(N)) = sum over M | N and d | N/M of the images of S_k^new(Gamma_1(M)) under q -> q^d,
Moebius inversion gives dim S_k^new(Gamma_1(N)) = sum over M | N of beta(N/M) dim S_k(Gamma_1(M)),
with beta = mu * mu. For k >= 3 each dim S_k(Gamma_1(M)) (Cohen-Oesterle) is (k - 1)/12 times a
constant plus a term that depends only on k mod 12 (elliptic and irregular-cusp terms, present only
for M <= 4); the k = 2 term has an extra Eisenstein correction. G. Martin, J. Number Theory 112 (2005)
298-331, Theorem 13 (Gamma_1, k >= 2; Theorem 1 for Gamma_0) writes this out explicitly.
So for k >= 3, on each residue class of k mod 12, the true dimension is linear in k; the corrected
formula has the same shape. Two such functions agree for all k >= 3 once they agree for 24
consecutive k (two values per class). PARI/GP `mfdim([32, k, -1], 0)` agrees with the formula for
k = 2..80, which covers k = 2 and the 24 values k = 3..26.

Lean: —.

### [A063321](A063321/): newform dimension formula for Gamma_1(48) (the constant -72 was dropped)

**Source.** OEIS wiki, Talk:Conjectures/List, line for A063321: "Conjecture: a(n) = 13*(n + (n-1) mod 2) + 14*(n + n mod 2)".
[A063321](https://oeis.org/A063321) is "Dimension of the space of weight n cuspidal newforms for Gamma_1(48)",
offset 2, data -1, 23, 49, 77, 103, ... The entry itself now states: a(n) = 13*(n + (n-1) mod 2) + 14*(n + n mod 2) - 72 for n > 2 (P. Luschny, Mar 05 2012); a(n) = (54n - 117 - (-1)^n)/2 for n > 2 (C. Barker, Sep 28 2012).

**Reading.** The OEIS data are shifted by one weight: term a(n) is the dimension in weight n - 1
(a(3) is the weight-2 dimension; a(2) = -1 is not a dimension, the true weight-1 dimension is 0).
Below, n is the OEIS index and k = n - 1 the weight.

**Result.** Misstated. The printed expression exceeds the entry's formula by exactly 72 at every n (a(3): 95 against 49), and exceeds the weight form by 44 (k even) or 46 (k odd), so it is false for every n in either indexing. The constant -72 was dropped.
The corrected formula is true: a(n) = 13(n + (n-1) mod 2) + 14(n + n mod 2) - 72 = (54n - 117 - (-1)^n)/2 for n >= 3 in the OEIS indexing, that is
dim S_k^new(Gamma_1(48)) = (54k - 63 + (-1)^k)/2 for k >= 2.

**Argument.** The newspace dimension is a fixed finite combination of cusp-space dimensions:
from S_k(Gamma_1(N)) = sum over M | N and d | N/M of the images of S_k^new(Gamma_1(M)) under q -> q^d,
Moebius inversion gives dim S_k^new(Gamma_1(N)) = sum over M | N of beta(N/M) dim S_k(Gamma_1(M)),
with beta = mu * mu. For k >= 3 each dim S_k(Gamma_1(M)) (Cohen-Oesterle) is (k - 1)/12 times a
constant plus a term that depends only on k mod 12 (elliptic and irregular-cusp terms, present only
for M <= 4); the k = 2 term has an extra Eisenstein correction. G. Martin, J. Number Theory 112 (2005)
298-331, Theorem 13 (Gamma_1, k >= 2; Theorem 1 for Gamma_0) writes this out explicitly.
So for k >= 3, on each residue class of k mod 12, the true dimension is linear in k; the corrected
formula has the same shape. Two such functions agree for all k >= 3 once they agree for 24
consecutive k (two values per class). PARI/GP `mfdim([48, k, -1], 0)` agrees with the formula for
k = 2..80, which covers k = 2 and the 24 values k = 3..26.

Lean: —.

### [A063337](A063337/): newform dimension formula for Gamma_1(64) (72n is missing the constant -155)

**Source.** OEIS wiki, Talk:Conjectures/List, line for A063337: "Conjecture: a(n) = 72*n".
[A063337](https://oeis.org/A063337) is "Dimension of the space of weight n cuspidal newforms for Gamma_1(64)",
offset 2, data -1, 61, 133, 205, 277, ... The entry itself now states: comment 'Conjecture: a(n) = 72*n - 155 for n > 2' (P. Luschny, Mar 05 2012).

**Reading.** The OEIS data are shifted by one weight: term a(n) is the dimension in weight n - 1
(a(3) is the weight-2 dimension; a(2) = -1 is not a dimension, the true weight-1 dimension is 0).
Below, n is the OEIS index and k = n - 1 the weight.

**Result.** Misstated. 72n differs from 72n - 155 by 155 at every n (a(3) = 61), and from the weight form by 83, so the printed formula is false for every n in either indexing. The constant -155 was dropped. The entry still carries 72n - 155 as a conjecture; it is true (below).
The corrected formula is true: a(n) = 72n - 155 for n >= 3 in the OEIS indexing, that is
dim S_k^new(Gamma_1(64)) = 72k - 83 for k >= 2.

**Argument.** The newspace dimension is a fixed finite combination of cusp-space dimensions:
from S_k(Gamma_1(N)) = sum over M | N and d | N/M of the images of S_k^new(Gamma_1(M)) under q -> q^d,
Moebius inversion gives dim S_k^new(Gamma_1(N)) = sum over M | N of beta(N/M) dim S_k(Gamma_1(M)),
with beta = mu * mu. For k >= 3 each dim S_k(Gamma_1(M)) (Cohen-Oesterle) is (k - 1)/12 times a
constant plus a term that depends only on k mod 12 (elliptic and irregular-cusp terms, present only
for M <= 4); the k = 2 term has an extra Eisenstein correction. G. Martin, J. Number Theory 112 (2005)
298-331, Theorem 13 (Gamma_1, k >= 2; Theorem 1 for Gamma_0) writes this out explicitly.
So for k >= 3, on each residue class of k mod 12, the true dimension is linear in k; the corrected
formula has the same shape. Two such functions agree for all k >= 3 once they agree for 24
consecutive k (two values per class). PARI/GP `mfdim([64, k, -1], 0)` agrees with the formula for
k = 2..80, which covers k = 2 and the 24 values k = 3..26.

Lean: —.

### [A071010](A071010/): if n is not a sum of two squares then 4 | sigma(n)

**Source.** [A071010](https://oeis.org/A071010) (sigma(k)/4 for k not a sum of 2 squares), comment:
"Conjecture : if n is not the sum of 2 squares sigma(n) == 0 (mod 4) ..." (OEIS text, CC BY-SA 4.0.)
The same statement is B. Cloitre's 2002 conjecture in [A022544](https://oeis.org/A022544).

**Result.** True. Proved in A022544 by M.-A. Leduc (Mar 2026); re-derived here.

**Argument.** By the two-squares theorem, n is not a sum of two squares iff some prime p ≡ 3 (mod 4)
divides n to an odd power e. Then σ(p^e) = (1 + p) + p^2(1 + p) + … + p^(e−1)(1 + p) ≡ 0 (mod 4), since
4 | p + 1, and σ is multiplicative.

Lean: [full proof](A071010/A071010_mathlib.lean).

### [A085765b](A085765b/): a(n) mod 2 has period 7

**Source.** [A085765](https://oeis.org/A085765) (partial sums and bisection of A086450), comment:
"Conjecture: a(n) mod 2 repeats the 7-pattern 0,0,1,1,1,0,1." (OEIS text, CC BY-SA 4.0.) (The entry's
other conjecture, log a(n)/log n unbounded, is a separate item.)

**Result.** True. The entry already notes (L. Herrgesell, 2007) that it follows from the A086450 pattern
proved there; re-derived here.

**Argument.** A086450: b(0) = 1, b(2n+1) = b(n), b(2n) = b(0) + … + b(n). Claim b(n) ≡ P(n mod 7) (mod 2),
P = 1,1,0,1,0,0,1. By strong induction: for odd indices P((2r+1) mod 7) = P(r); for even indices P sums to 4
over a period, so b(0) + … + b(n) ≡ Q(n mod 7) with Q the prefix sums of P mod 2, and P(2r mod 7) = Q(r).
A085765(n) = b(2n) ≡ P(2n mod 7): 1, 0,0,1,1,1,0,1, 0,0,1,1,1,0,1, …

Lean: [witness](A085765b/A085765b.lean).

### [A086449](A086449/): parity of a(n) and a(2^k − 2)

**Source.** [A086449](https://oeis.org/A086449) (a(0) = 1, a(2n+1) = a(n), a(2n) = a(n) + a(n−1) + a(n−2) +
a(n−4) + …, a(<0) = 0), comment: "Conjecture: all a(n) are even except a(2^k-1) = 1. Also a(2^k-2) = 2^(k-1).
[For proof see link.]" (OEIS text, CC BY-SA 4.0.)

**Result.** True. Proof linked in the entry (L. Herrgesell); re-derived here.

**Argument.** a(2^k − 1) = a(2^(k−1) − 1) = … = a(0) = 1. Strong induction for evenness: an odd n = 2m+1
not of the form 2^k − 1 has m not of that form. For n = 2m (m ≥ 1), a(2m) = a(m) + Σ_j a(m − 2^j), and by
induction the odd terms are those with argument 2^i − 1: [m + 1 = 2^k] + #{j : m + 1 = 2^i + 2^j}. If
m + 1 = 2^k this is 1 + 1; if m + 1 has two 1-bits it is 0 + 2; otherwise 0. So a(2m) is even.
For a(2^k − 2), m = 2^(k−1) − 1: m − 2^j has j trailing ones, then the bits of 2^(k−1−j) − 2, so
a(m − 2^j) = a(2^(k−1−j) − 2) = 2^(k−j−2) for j ≤ k − 3 and a(0) = 1 for j = k − 2. Then
a(2^k − 2) = 1 + (2^(k−2) + … + 2) + 1 = 2^(k−1).

Lean: —.

### [A088982](A088982/): a prime between consecutive prime-indexed primes

**Source.** [A088982](https://oeis.org/A088982), comment: "Conjecture: For x > 1 there is at least 1 prime
between prime(prime(x)) and prime(prime(x+1))." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial. The entry already contains the proof (M. F. Hasler, 2015).

**Argument.** For x > 1, prime(x) and prime(x+1) are odd, so prime(x+1) ≥ prime(x) + 2 and
prime(prime(x)) < prime(prime(x) + 1) < prime(prime(x+1)).

Lean: —.

### [A088987](A088987/): the number of primes between consecutive prime-indexed primes is odd

**Source.** [A088987](https://oeis.org/A088987), comment: "Conjecture: There cannot be an even number total
of primes between two consecutive prime-indexed primes." (OEIS text, CC BY-SA 4.0.)

**Result.** True except for the first pair: between prime(2) = 3 and prime(3) = 5 there are 0 primes,
an even number. The entry already notes this exception.

**Argument.** Between prime(a) and prime(b) (a < b) lie exactly b − a − 1 primes. For consecutive primes
a = p_x, b = p_{x+1} with x ≥ 2 both are odd, so b − a − 1 is odd. For x = 1, b − a − 1 = 0.

Lean: —.

### [A094913](A094913/): maximal number of distinct nonempty factors of a binary word of length n equals A006697(n) − 1

**Source.** OEIS [A094913](https://oeis.org/A094913) (offset 0): maximal number of distinct nonempty
substrings (factors) of a binary string of length n. Conjecture (V. Jovovic, Sep 19 2005):
"a(n) = A006697(n)-1." (OEIS text, CC BY-SA 4.0; revision #33.) A006697 is the subword complexity ρ_z(n)
(number of distinct factors of length n) of z, the fixed point of a → aab, b → b.

**Result.** True.

**Argument.** Write M(n) = Σ_{i=0..n} min(2^i, n − i + 1).
- A. Flaxman, A. W. Harrow, G. B. Sorkin, Strings with maximally many distinct subsequences and substrings,
  Electron. J. Combin. 11 (2004) R8, Theorem 8, bullets 1–2: a word of length n over d letters has at most
  min(d^m, n − m + 1) distinct factors of length m, and a modified de Bruijn word attains all these bounds at
  once. With d = 2 and m ≥ 1 summed, a(n) = M(n) − 1 (the m = 0 term is the empty word).
- J.-P. Allouche, J. Shallit, On the subword complexity of the fixed point of a → aab, b → b, and
  generalizations, arXiv:1605.02361, Theorem 1: ρ_z(n) = M(n) for n ≥ 0, so A006697(n) = M(n).
  Remark 3 there notes that M(n) is the maximal number of factors of all lengths (empty word included) of a
  binary word of length n, citing Iványi 1987, Shallit 1993 and FHS 2004, and Remark 16 states that this
  confirms Jovovic's conjecture A006697(n) = A094913(n) + 1.

Hence a(n) = M(n) − 1 = A006697(n) − 1.

FHS Theorem 8 bullet 3 also gives a closed form (d^{k+1} − 1)/(d − 1) + C(n − k + 1, 2) with k = ⌊log_d n⌋.
For d = 2 it is wrong at n = 4, 8, 9, 16, 17, 18, 32, ... (n = 4 gives 10, while M(4) = 9); the correct split
point is the largest k with 2^k ≤ n − k + 1, as in Hasler's LambertW formula (AS 2016, Remark 16). The
argument above uses only bullets 1–2.

Lean: —.

### [A095380](A095380/): the proportion of non-values of σ up to 2^n tends to 1

**Source.** OEIS [A095380](https://oeis.org/A095380) (offset 1): number of integers not exceeding 2^n that are
not a value of σ (the sum-of-divisors function), i.e. terms of A007369 up to 2^n. Conjecture: "ratio of
non-sigma numbers tends to one. Increasing majority of numbers is impossible as a sum of divisors." (OEIS text,
CC BY-SA 4.0.)

**Reading.** "Ratio" is a(n)/2^n.

**Result.** True: a(n)/2^n → 1.

**Argument.** Let V_σ(x) = #{m ≤ x : m = σ(k) for some k}. Then a(n) = 2^n − V_σ(2^n). K. Ford, The
distribution of totients, Ramanujan J. 2 (1998) 67–151 (arXiv:1104.3264), Theorem 1 gives
V(x) = (x/log x) exp{C(log_3 x − log_4 x)^2 + D log_3 x − (D + 1/2 − 2C) log_4 x + O(1)} for totient values,
and Theorem 14 extends Theorem 1 to multiplicative f : ℕ → ℕ with {f(p) − p} finite and not containing 0 and
Σ_{h square-full} h^δ/f(h) ≪ 1 for some δ > 0; Ford names σ as satisfying these (f(p) − p = 1, and σ(h) ≥ h
makes the square-full sum converge for δ < 1/2). Hence V_σ(x) = x/(log x)^{1+o(1)} = o(x), and
a(n)/2^n = 1 − V_σ(2^n)/2^n → 1.

Lean: needs Mathlib.

### [A097602](A097602/): the squares hit are exactly m² with 3 ∤ m

**Source.** [A097602](https://oeis.org/A097602) (offset 1), Reinhard Zumkeller, Aug 30 2004: "a(n+1) = a(n) +
number of squares so far; a(1) = 1." Comment: "Conjecture: a(n) = m^2 iff m mod 3 > 0." The entry also carries,
credited to Vladeta Jovovic (2004, added in revision #16, May 10 2013), "a(n) is a square iff n is congruent to
{1, 4} mod 9", the formulas a(9n+1) = (3n+1)², a(9n+4) = (3n+2)² and a rational g.f., all without proof.
(OEIS text, CC BY-SA 4.0, revision #22 of Sep 22 2025, checked 2026-11-06.)

**Reading.** "Squares so far" counts the squares among a(1), ..., a(n), including a(n) (the entry's example
a(2) = 1 + 1 confirms this). The conjecture reads: m² is a term of the sequence iff m mod 3 ≠ 0 (m = 0 included:
0 is not a term).

**Result.** True. For every k ≥ 0, with c the running count of squares,
a(9k+1) = (3k+1)² (c = 2k+1), a(9k+2), a(9k+3) = (3k+1)² + (2k+1), + 2(2k+1),
a(9k+4) = (3k+2)² (c = 2k+2), a(9k+5), a(9k+6) = (3k+2)² + (2k+2), + 2(2k+2),
a(9k+7) = (3k+3)² + 1, a(9k+8), a(9k+9) = (3k+3)² + 1 + (2k+2), + 2(2k+2).
So a(n) is a square iff n ≡ 1, 4 (mod 9) (Jovovic's claims), and the squares hit are (3k+1)², (3k+2)².

**Argument.** Induction on k. At a(9k+1) = (3k+1)² the count is 2k+1 (the squares (3j+1)², (3j+2)² for j < k and
(3k+1)²). Since (3k+2)² − (3k+1)² = 6k+3 = 3(2k+1), three steps reach (3k+2)², and the two intermediate values lie
strictly between consecutive squares. Now c = 2k+2 and (3k+3)² − (3k+2)² = 6k+5 = 3(2k+2) − 1, so the third
step lands on (3k+3)² + 1, skipping (3k+3)²; again nothing in between is square. Then (3k+4)² − ((3k+3)² + 1) =
6k+6 = 3(2k+2), so three more steps reach (3k+4)², with count 2k+3 = 2(k+1)+1. The base case is a(1) = 1, c = 1.

Lean: [full proof](A097602/A097602_mathlib.lean).

### [A098021](A098021/): former and current definitions agree

**Source.** OEIS [A098021](https://oeis.org/A098021), current name (C. Kimberling, adopted by
N. J. A. Sloane 2016-01-30, rev. #25): "Positions of 0's in the zero-one sequence
[n*r+2*r]-[n*r]-[2*r], where r=sqrt(2) and [ ]=floor; see A187967." Former definition
(R. L. Bagula 2004, [history](https://oeis.org/history?seq=A098021)): f(n) = n·√2 mod 1,
g(x) = −1 on [0,1/3], 0 on (1/3,2/3], 1 on (2/3,1]; n is a term when
f(n+2) − 2f(n+1) + f(n) − g(f(n+1)) = 0. Kimberling's 2011 comment was the conjecture that the two
agree. (OEIS text, CC BY-SA 4.0.)

**Reading.** The former FORMULA line wrote "g(x)=1 if 1/3<x<=1", an evident typo for 2/3 (the
Mathematica program uses 2/3); with the cases tested in order both give the same g.

**Result.** The definitions agree for every integer n; proved in Lean 4 + Mathlib.

**Argument.** Let x = frac((n+1)√2) and α = √2 − 1 ≈ 0.414. Then frac(n√2) = x − α + [x < α] and
frac((n+2)√2) = x + α − [x ≥ 1 − α], so the second difference is [x < α] − [x ≥ 1 − α].
- x < α: difference 1, but g(x) ∈ {−1, 0}.
- x ≥ 1 − α ≈ 0.586: difference −1, but g(x) ∈ {0, 1}.
- α ≤ x < 1 − α: difference 0 = g(x).
So the old condition holds iff α ≤ x < 1 − α, i.e. iff frac(n√2) < 1 − 2α = 3 − 2√2. The new
condition [n√2 + 2√2] − [n√2] − 2 = 0 holds iff frac(n√2) + 2√2 < 3, the same inequality.
Irrationality of √2 is not used.

Lean: [full proof](A098021/A098021_mathlib.lean).

### [A113599](A113599/): no term is zero (pigeonhole)

**Source.** [A113599](https://oeis.org/A113599) (least n-digit multiple of n whose digit permutations give at least
n distinct multiples of n, 0 if none), comment: "Conjecture: No term is zero. The proof should be simple."
(OEIS text, CC BY-SA 4.0.)

**Result.** True. Proved in the entry by J. Rayman (Feb 2023); re-derived here.

**Argument.** There are at least ⌊9·10^(n−1)/n⌋ n-digit multiples of n and C(n+9, 9) multisets of n digits, so
some multiset carries at least ⌈⌊9·10^(n−1)/n⌋/C(n+9, 9)⌉ of them; these are distinct n-digit multiples of n that
are digit permutations of one another. The bound is ≥ n for every n ≥ 4 (it grows by a factor ≈ 10n/(n+10) per
step); n = 1, 2, 3 have the terms 1, 20, 102.

Lean: —.

### [A115509](A115509/): a(n) = 0 for 2^(k+1) ≤ n < 3·2^k

**Source.** OEIS [A115509](https://oeis.org/A115509) (Max Alekseyev, 2006): "Number of circular
permutations of {1, 2, ..., n} such that in every pair of adjacent elements each element in binary
notation has ones at the same or adjacent positions to those of the other element." The statement
"If 2^(k+1) <= n < 3*2^k for k >= 1, then a(n) = 0" was a conjecture on the OEIS wiki list
(Talk:Conjectures/List) and became a plain FORMULA line in rev. #6 (2023-03-18) with no proof
recorded. (OEIS text, CC BY-SA 4.0.)

**Reading.** x and y may be adjacent when every 1-bit of x has a 1-bit of y at the same or a
neighbouring position, and vice versa. Circular permutations are counted up to rotation only (the
data has a(3) = 2, so the two orientations count separately); we count arrangements that start with 1.

**Result.** True for every k ≥ 1; proved in Lean 4 + Mathlib.

**Argument.** Let m = 2^(k+1) ≤ n < 3·2^k, so n ≥ 4. A neighbour y of m has all its 1-bits at
positions k, k+1 or k+2, so 2^k divides y; 1 ≤ y < 3·2^k leaves y = 2^k or y = 2^(k+1) = m.
On a circle of n ≥ 4 distinct numbers, m has two distinct neighbours, both different from m,
so both would equal 2^k. Hence no arrangement exists and a(n) = 0.

Lean: [full proof](A115509/A115509_mathlib.lean).

### [A117414](A117414/): an Euler triangle without a definition (row sums, columns 1 and 2)

**Source.** OEIS wiki, Talk:Conjectures/List, line for A117414. [A117414](https://oeis.org/A117414)
(P. Barry, 2006), name "An Euler triangle.", data only:
"Conjecture: row sums are the Euler numbers A000364. Second column is A024255. Third column is A117415."

**Reading.** The entry has had no definition since revision #1 (2006): name, data and the conjecture
only. A claim about a triangle given by 45 numbers is ill-posed. The only rule for all rows in the
entry is G. Critzer's g.f. (Apr 2023):
Sum_{n,k} T(n,k) u^k z^n / B(n) = E((u-1)z)/E(-z), with B(n) = (2n)!/2^n = A000680(n) and
E(z) = Sum_n z^n/B(n). It reproduces all 45 data terms. We take it as the definition.
Columns are numbered from 0, so "second column" is k = 1 and "third column" is k = 2.
(Critzer's comment that T(n,k) counts alternating permutations of [2n] with k cyclically alternating
components is a separate conjecture, not addressed here.)

**Result.** Misstated (no definition). With Critzer's g.f. as the definition all three claims are
true: row sums = A000364 (Euler secant numbers), column 1 = A024255 (n times the tangent number
t(2n-1)), column 2 = A117415 (e.g.f. (x tan x - x^2)/8, even powers).

**Argument.** Put t = sqrt(2z). Then z^n/B(n) = t^(2n)/(2n)!, so a series Sum c_n z^n/B(n) is the
even e.g.f. Sum c_n t^(2n)/(2n)!, and T(n,k) is (2n)! times the coefficient of u^k t^(2n). Also
E(z) = cosh(sqrt(2z)), so E(-z) = cos t.
- u = 1: the g.f. is E(0)/E(-z) = 1/cos t = sec t = Sum A000364(n) t^(2n)/(2n)!.
- Coefficient of u: z E'(-z)/E(-z). From E(w) = cosh s with s = sqrt(2w), E'(w) = sinh(s)/s, and at
  w = -z, s = i t, so E'(-z) = sin(t)/t. The coefficient is (t^2/2)(sin t/t)/cos t = (t tan t)/2,
  the e.g.f. of A024255 (even part of x tan(x)/2), i.e. T(n,1) = n t(2n-1).
- Coefficient of u^2: z^2 E''(-z)/(2 E(-z)), with E''(w) = cosh(s)/s^2 - sinh(s)/s^3, so
  E''(-z) = -cos(t)/t^2 + sin(t)/t^3 and the coefficient is (t^4/8)(tan(t)/t^3 - 1/t^2)
  = (t tan t - t^2)/8, the e.g.f. of A117415.

Lean: needs Mathlib.

### [A118990](A118990/): A118990(n) = 2^n A086906(n-1)

**Source.** OEIS [A118990](https://oeis.org/A118990), number of symmetric singular n X n
(+1,-1) matrices over the reals (0, 4, 32, 512, 15872, ...; offset 1), and OEIS
[A086906](https://oeis.org/A086906), number of symmetric singular n X n (0,1) matrices over
the reals (1, 4, 32, 496, 14172, ...; offset 1). Each entry lists the other under Cf.; neither
states a formula between them (both entries read 2026-11-05). The idea comes from OpenAI
manuscript family 239, "The sharp exponential rate of singularity for symmetric Bernoulli
matrices" (OpenAI, October 3, 2026), Lemma 2.1: for n >= 2 a uniform symmetric sign matrix
A_n and a uniform symmetric 0/1 matrix B_(n-1) are singular with the same probability.

**Result.** For n >= 2, A118990(n) = 2^n A086906(n-1). Proved in Lean (all n).

**Argument.** Fix n >= 0 and write matrices of size n+1 with indices 0..n.
Given a sign vector s (length n+1) and a symmetric 0/1 matrix B of size n, put
e = (1, s_1, ..., s_n), let N be the matrix with first row and first column all 1 and
N_ab = 1 - 2 B_ab for a, b >= 1, and set M = s_0 diag(e) N diag(e), that is
M_00 = s_0, M_0b = M_b0 = s_0 s_b, M_ab = s_0 s_a s_b (1 - 2 B_ab).
M is symmetric with entries +1/-1.
Conversely, a symmetric sign matrix M gives back s_0 = M_00, s_k = M_00 M_0k and
B_ab = (1 - M_00 M_0a M_0b M_ab)/2 in {0, 1}, and the two maps are inverse to each other
(this uses s_i^2 = 1 and M_0k = M_k0). So (s, B) <-> M is a bijection between
{+1,-1}^(n+1) x {symmetric 0/1 matrices of size n} and symmetric sign matrices of size n+1.
The case M_00 = -1 needs no special treatment: it is absorbed in s_0 = -1.
Determinant: det M = s_0^(n+1) (prod e_i)^2 det N, and subtracting row 0 from every other row
of N leaves first column (1, 0, ..., 0) and lower block -2B, so det N = (-2)^n det B.
Hence M is singular iff B is, and the singular sign matrices number 2^(n+1) times the
singular 0/1 matrices. With n+1 = the OEIS index this is A118990(n) = 2^n A086906(n-1).
The count form of OpenAI's Lemma 2.1 is the same statement: multiplying the equal
probabilities by 2^(n(n+1)/2) and 2^((n-1)n/2) gives the factor 2^n.

Lean: [full proof](A118990/A118990_mathlib.lean).

### [A121627](A121627/): divisibility of the "complex factorial" real parts

**Source.** [A121627](https://oeis.org/A121627) (a(n) = Re(∏_{k≤n} k(1+i))), comment: "Conjecture (1): Current nonzero
term divides next nonzero term ... Conjecture (2): If the term in (12, 8, 5, ...) is generated from a(n)/a(n-1) or
a(n)/a(n-2), then n divides each (12, 8, 5, ...)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. Derived in the entry from explicit formulas (H. Fischer, 2011); re-derived here.

**Argument.** a(n) = n!·Re((1+i)^n) = n!·2^(n/2)·cos(nπ/4). It vanishes iff n ≡ 2, 6 (mod 8), and otherwise
|a(n)| = n!·2^⌊n/2⌋. For consecutive nonzero indices m < n (n − m ∈ {1, 2}), a(n)/a(m) = ±(n!/m!)·2^(⌊n/2⌋−⌊m/2⌋),
an integer divisible by n.

Lean: —.

### [A131439](A131439/): 1, 7, then 4k + 14, and its inverse binomial transform

**Source.** [A131439](https://oeis.org/A131439) (offset 1), Gary W. Adamson, Jul 11 2007: "Inverse binomial
transform of A131438 (assuming zero offset in both sequences)". Comments: "Conjecture: The sequence appears to be
(1, 7, ...) followed by 4k + 14; k=0,1,2,..." and "Inverse binomial transform of this sequence = (1, 6, 1, -4, 7,
-10, 13, -16, 19, -22, ...)". [A131438](https://oeis.org/A131438) is defined by a(n) = (2+n)·2^n − 2 − 3n
(offset 1; definition replaced by this formula by R. J. Mathar, 2011). (OEIS text, CC BY-SA 4.0, A131439
revision #21 of Mar 23 2026, A131438 revision #14 of Oct 17 2025, checked 2026-11-06.)

**Reading.** With zero offset, b(k) = A131438(k+1) for k ≥ 0 and A131439(m+1) = Σ_{k=0..m} (−1)^(m−k) C(m,k) b(k).
The entry's example (1,3,3,1)·(1,7,14,18) = 82 = A131438(4) confirms this. The second comment is read the same way
(zero offset). The example in A131438, "a(3) = 19 = ... (7 + 9 + 13)", disagrees with its data and formula
(a(3) = 29); it does not affect A131439, which uses the formula.

**Result.** True. A131439 = 1, 7, then A131439(n) = 4n + 2 for n ≥ 3 (that is 4k + 14 with k = n − 3). Its
inverse binomial transform is 1, 6, then (−1)^m (3m − 5) for m ≥ 2.

**Argument.** 1. The inverse binomial transform of f at m is the m-th forward difference Δ^m f(0).
2. b(k) = (k+3)·2^(k+1) − 2 − 3(k+1) = (2k+6)·2^k − 3k − 5. Then Δb(k) = (2k+10)·2^k − 3 and
   Δ²b(k) = (2k+14)·2^k. For g_A(k) = (2k+A)·2^k, Δg_A = g_{A+4}. So Δ^m b = g_{4m+6} for m ≥ 2 and
   A131439(m+1) = Δ^m b(0) = 4m + 6; directly, A131439(1) = 1 and A131439(2) = 7.
3. So c(m) = A131439(m+1) = (4m+6) − 3·[m = 1] − 5·[m = 0]. The inverse binomial transform is linear; it sends
   4m+6 to 0 for m ≥ 2 (second difference of a linear function) and the point mass v·[k = i] to
   (−1)^(m−i) C(m,i) v. For m ≥ 2 this gives −3·(−1)^(m−1) m − 5·(−1)^m = (−1)^m (3m − 5); m = 0, 1 give 1, 6.

Lean: [full proof](A131439/A131439_mathlib.lean).

### [A138904](A138904/): rotational symmetries of a binary expansion

**Source.** OEIS [A138904](https://oeis.org/A138904) (Max Sills, 2008), a(m) = number of rotational
symmetries of the binary expansion of m. Two conjectures in the comments (OEIS text, CC BY-SA 4.0):
"For binary expansions of length n, there are d(n) distinct values that will show up as symmetries
... precisely the divisors of n", and, for n whose proper divisors are all coprime, "only one number
of length n with n symmetries ... 2^n - 1"; for each proper divisor d > 1 the numbers with n/d
symmetries are (2^0 + 2^d + ... + 2^(n-d))·a with 2^(d-1) <= a < 2^d - 1; "the rest ... only the
trivial symmetry".

**Reading.** a(m) counts the rotations k in {0, ..., L-1} of the L-bit word of m (L = binary length,
m = 0 is "0") that give the same word; a(0..98) agree with the data. "Proper divisors all coprime" is
read as: the divisors of L strictly between 1 and L are pairwise coprime (L = 1, p, p^2 or pq).

**Result.** Both conjectures hold.
1. For m of length L, a(m) divides L, and every divisor of L is a(m) for some m of length L.
2. a(m) = L only for m = 2^L - 1. For every prime d dividing L with d < L (any L, not only the
   coprime-divisor case), a(m) = L/d exactly when m = R·a, R = 1 + 2^d + ... + 2^(L-d),
   2^(d-1) <= a < 2^d - 1. If the divisors of L strictly between 1 and L are pairwise coprime, every
   such divisor is prime, so all other m of length L have a(m) = 1.

**Argument.** Let S = {k : rotation by k fixes the word}. S is closed under addition and under
k, j -> j - k (indices mod L), so with p the least positive element, S = {multiples of p} and p | L;
hence a(m) = L/p divides L. The word with a single 1 at the top of each block of length q = L/e has
least period q, so a = e. a(m) = L means period 1, so all bits equal the top bit 1. Period d means
the word is its low d-bit block a repeated, i.e. m = R·a, with top bit of a set (a >= 2^(d-1)); the
least period then divides d, and for prime d it is 1 or d, and 1 only for a = 2^d - 1. If proper
divisors are pairwise coprime, a composite proper divisor d would share its prime factor r < d with
itself as a divisor pair (r, d), so every proper divisor is prime.

Lean: [full proof](A138904/A138904.lean).

### [A145878](A145878/): polynomial formulas for T(r+k, k), r = 3..7 (previous conjectures)

**Source.** OEIS [A145878](https://oeis.org/A145878): T(n,k) = number of permutations of [n] with
k strong fixed points. Formulas T(3+k,k) = 3k+3, T(4+k,k) = (k+1)(k+28)/2, T(5+k,k) =
(k+1)(3k+77), T(6+k,k) = (k+1)(k^2+110k+2982)/6, T(7+k,k) = (k+1)(3k^2+235k+7352)/2, now marked
"previous conjectures" in the entry (McGinnis 2018, with the paper of Baren et al.).
(OEIS text, CC BY-SA 4.0.)

**Result.** True (resolved by others; re-derived here).

**Argument.** The k strong fixed points cut a permutation into k + 1 consecutive blocks, each a
permutation with no strong fixed point (empty blocks allowed). With c(m) = T(m,0) (A052186:
1, 0, 1, 3, 14, 77, 497, 3676), T(r+k, k) = sum over compositions of r into k+1 parts of the
product of c(parts). Since c(1) = 0, at most floor(r/2) parts are nonempty, so
T(r+k,k) = sum_j C(k+1, j) w_r(j) is a polynomial in k of degree ≤ floor(r/2) ≤ 3. Agreement at 4
values of k proves each formula. (Example r = 4: w(1) = 14, w(2) = c(2)^2 = 1, so
T = 14(k+1) + C(k+1,2) = (k+1)(k+28)/2.)

Lean: [witness](A145878/A145878.lean).

### [A164848](A164848/): a(n) = A026741(n)/A051712(n+1) has period 24

**Source.** OEIS [A164848](https://oeis.org/A164848) (Paul Curtz, 2009), a(n) = A026741(n)/A051712(n+1):
"Conjecture (checked for the first 3000 entries): periodic with a(n+24)=a(n)." (OEIS text, CC BY-SA 4.0.)

**Reading.** A026741(n) = n for odd n, n/2 for even n. A051712(n) is the numerator of
b(n) - b(n+1) with b(n) = n/((n+1)(n+2)) (offset 1). Offset of A164848 is 1; a(1..105) agree with the data.

**Result.** True: a(n) = gcd(n, 24) for odd n and gcd(n, 24)/2 for even n, so a(n+24) = a(n) for all n >= 1.
This also gives Howroyd's formula a(n) = gcd(12, n/gcd(2, n)) listed in the entry.

**Argument.** b(n+1) - b(n+2) = n(n+3)/((n+2)(n+3)^2(n+4)). Since (n+2)(n+3)(n+4) = 24 + n(n^2 + 9n + 26),
gcd(n(n+3), (n+2)(n+3)^2(n+4)) = (n+3)·gcd(n, 24), so A051712(n+1) = n/g with g = gcd(n, 24). Then
a(n) = n/(n/g) = g for odd n and (n/2)/(n/g) = g/2 for even n (g is even). Both depend only on n mod 24.

Lean: [full proof](A164848/A164848.lean).

### [A168295](A168295/): "Conjecture: Worpitzky forms" states no claim

**Source.** OEIS wiki, Talk:Conjectures/List, line for A168295: "Conjecture: \"Worpitzky forms\"".
[A168295](https://oeis.org/A168295) (R. L. Bagula, 2009): triangle of coefficients of
p(x, n) = (n-1)! Sum_{j=1..n} A142458(n, j) binomial(x + j - 1, n - 1).

**Result.** Misstated: nothing to prove. The 2009 comment, after the word "Conjecture", only names a
family: for a "general Pascal recursion" triangle Pascal[n,k,m],
p[x,n,m] = Sum_k Pascal[n,k,m] binomial(x+k-1, n-1), "where p[x,n,m] are the inverse z transform
polynomials". No equation or property is asserted. G. C. Greubel removed the comment in revision #3
(2022-03-17, approved by N. J. A. Sloane in #5); the current entry has no conjecture.

**Argument.** The one reading that turns the comment into a statement is: the ordinary g.f. in x of
p(x) is Sum_k Pascal[n,k,m] z^(n-k)/(1-z)^n. This holds for any coefficient array, since
Sum_{x>=0} binomial(x+k-1, n-1) z^x = z^(n-k)/(1-z)^n (substitute x = n - k + j). So under that
reading it is a tautology, and under any other it has no content.

Lean: —.

### [A173989](A173989/): 2-adic valuations of A173300 follow A, A, A+1, A with A odd

**Source.** [A173989](https://oeis.org/A173989) (offset 1), J. Lowell, Mar 04 2010: a(n) is the 2-adic valuation of
A173300(n), the denominator of x^n + y^n with x = (1+√3)/2, y = (1−√3)/2 (Maple and PARI programs in the entry).
Comment: "Conjecture: always follows the pattern A, A, A+1, A, where A is an odd number." Data: 0, 0, 1, 1, 2, 1,
3, 3, 4, 3, … (OEIS text, CC BY-SA 4.0, revision of Mar 23 2026, checked 2026-11-05.)

**Reading.** The pattern starts at n = 3: (a(4j+3), a(4j+4), a(4j+5), a(4j+6)) = (A, A, A+1, A) with A = 2j+1.
a(1) = a(2) = 0 precede it.

**Result.** True: for every j ≥ 0, a(4j+3) = a(4j+4) = a(4j+6) = 2j+1 and a(4j+5) = 2j+2.

**Argument.** 1. s_n = (1+√3)^n + (1−√3)^n satisfies s_0 = s_1 = 2, s_{n+2} = 2 s_{n+1} + 2 s_n (both roots satisfy
   t² = 2t + 2), so s_n ∈ ℤ and x^n + y^n = s_n / 2^n.
2. (1+√3)² = 2(2+√3), so s_{2m} = 2^m T_m, s_{2m+1} = 2^m U_m with T_0 = U_0 = 2, T_{m+1} = T_m + U_m,
   U_{m+1} = 2T_m + 3U_m.
3. Induction on m: T_{2m} ≡ 2 (mod 4), T_{2m+1} ≡ 4 (mod 8), U_m ≡ 2 (mod 4). (From T_{2m+1} ≡ 4 (mod 8),
   U_{2m+1} ≡ 2 (mod 4): T_{2m+2} = T + U ≡ 2, U_{2m+2} = 2T + 3U ≡ 2 (mod 4), T_{2m+3} = 3T + 4U ≡ 4 (mod 8),
   U_{2m+3} = 8T + 11U ≡ 2 (mod 4), with T, U at index 2m+1.)
4. So v2(s_{4j+3}) = 2j+2, v2(s_{4j+4}) = 2j+3, v2(s_{4j+5}) = 2j+3, v2(s_{4j+6}) = 2j+5. If s_n = 2^e u with u odd and
   e ≤ n, then s_n / 2^n = u / 2^(n−e) in lowest terms, so a(n) = n − e, which gives 2j+1, 2j+1, 2j+2, 2j+1.

Lean: [full proof](A173989/A173989_mathlib.lean).

### [A192023](A192023/): the determinant-2n matrix count does not match; a linear count does

**Source.** OEIS [A192023](https://oeis.org/A192023) (Wiener index of the comb graph with 2n
nodes, a(n) = n(2n² + 6n − 5)/3), comment by Clark Kimberling (Mar 31 2012): "Conjecture: for
n>2, A192023(n-2) is the number of 2 X 2 matrices with all terms in {1,2,...,n} and
determinant 2n." (OEIS text, CC BY-SA 4.0.)

**Reading.** Literal: count matrices [[w, x], [y, z]] with w, x, y, z ∈ {1, …, n} and
wz − xy = 2n. Allowing |det| = 2n only doubles the count and does not help.

**Result.** False as stated, already at n = 3: the matrices with entries in {1, 2, 3} and
determinant 6 are [[3, 1], [3, 3]] and [[3, 3], [1, 3]], two of them, while A192023(1) = 1.
The two sides differ for every 3 ≤ n ≤ 120 (count 2, 9, 16, 33, 42, 69, … against
1, 10, 31, 68, 125, 206, …). The determinant count is not even monotone (228 at n = 12, 180 at n = 13).

The comment is a misattribution. Kimberling's own guide in [A211795](https://oeis.org/A211795)
pairs A192023 with the linear relation w = −x + y + z + 2, and that version holds:

  #{(w, x, y, z) ∈ {1, …, n}⁴ : w + x = y + z + 2} = A192023(n − 1) for all n ≥ 2,

with A192023(m) the Wiener index of the comb graph with 2m nodes (the entry's definition).
This is proved in Lean for all n, together with the entry's formula a(m) = m(2m² + 6m − 5)/3.

equivalently A192023(n − 2) counts 4-tuples in {1, …, n − 1} with w + x = y + z + 2 (n ≥ 3).
A search over 2268 readings (entry ranges {0..k}, {1..k}, {−k..k} with k = n − 3, …, n + 3;
determinant, |determinant| or permanent equal to αn + β, 0 ≤ α ≤ 3, −4 ≤ β ≤ 4;
`certificate/search2.py`) finds no determinant or permanent reading that matches for
3 ≤ n ≤ 10.

**Argument.** Counterexample: wz − xy = 6 with entries ≤ 3 forces wz = 9 (w = z = 3) and
xy = 3, so (x, y) ∈ {(1, 3), (3, 1)}.
Corrected statement: with r(s) = #{(w, x) ∈ {1..n}² : w + x = s} = n − |s − n − 1| for
2 ≤ s ≤ 2n, the count is Σ_s r(s) r(s − 2). For n ≥ 2 and m = n − 2 the terms
s = 4..n + 1 give Σ_{t=1}^{m} t(t + 2), s = n + 2 gives (n − 1)², and s = n + 3..2n give
Σ_{u=1}^{m} u(u + 2) again. With Σ_{t=1}^{m} t(t + 2) = m(m + 1)(2m + 7)/6 the total is
(m + 1)(2m² + 10m + 3)/3 = a(m + 1) = a(n − 1). For n = 1 both sides are 0.
Wiener index: with spine vertices (i, 0) and teeth (i, 1), the distance is |i − j| + s + t for
i ≠ j and [s ≠ t] for i = j. Summing over the four (s, t) gives 4|i − j| + 4 (i ≠ j) or 2
(i = j), and Σ_{i,j<m} |i − j| = (m³ − m)/3, so half the ordered sum is
m + 2(m³ − m)/3 + 2(m² − m) = a(m).

Lean: [full proof](A192023/A192023_mathlib.lean).

### [A206912](A206912/): the differences of A206912 are 1s and 2s

**Source.** [A206912](https://oeis.org/A206912) (offset 1), Clark Kimberling, Feb 13 2012: position of log(n+1)
when the partial sums of the harmonic series are jointly ranked with {log(k+1)}; complement of A206911. Comment:
"Conjecture: the difference sequence of A206912 consists of 1s and 2s; see Comments at A206911." (OEIS text,
CC BY-SA 4.0, checked 2026-11-05.)

**Reading.** Write H_k = 1 + 1/2 + … + 1/k. Below log(n+1) in the joint ranking lie log 2, …, log n and the H_k
(k ≥ 1) with H_k < log(n+1), so A206912(n) = n + #{k ≥ 1 : H_k < log(n+1)}. This matches the Mathematica program
of A206911 and the data (A206912 = 1, 3, 4, 6, 7, 9, …). A tie H_k = log(n+1) cannot occur (log(n+1) is irrational
for n ≥ 1), but the proof does not need this: it holds for the definition that counts H_k strictly below.

**Result.** True. A206912(n+1) − A206912(n) ∈ {1, 2} for every n.

**Argument.** 1. *Key lemma.* For m ≥ 1 there is no k with log m ≤ H_k and H_{k+1} < log(m+1). Otherwise
   1/(k+1) = H_{k+1} − H_k < log(m+1) − log m = log(1 + 1/m) ≤ 1/m, so m ≤ k, and then
   log(m+1) ≤ log(k+1) ≤ H_k ≤ H_{k+1} < log(m+1) (using H_k ≥ log(k+1)), a contradiction.
2. *Finiteness.* H_k < log(n+1) forces k < n, since H_k ≥ log(k+1).
3. *Differences.* A206912(n+1) − A206912(n) = 1 + #{k ≥ 1 : log(n+1) ≤ H_k < log(n+2)}. H is increasing, so two
   such indices k < k' give log(n+1) ≤ H_k and H_{k+1} ≤ H_{k'} < log(n+2), which step 1 (m = n+1) excludes. So the
   count is 0 or 1.

Lean: [full proof](A206912/A206912_mathlib.lean).

### [A209260](A209260/): Jeffery's two conjectures (both proved in the entry's references)

**Source.** OEIS [A209260](https://oeis.org/A209260) (irregular triangle; a permutation of the
natural numbers derived from A141419). Conjecture 1: "2*n+1 is in the set S_n = {union of first n
rows of A209260} if and only if 2*n+1 is composite." Conjecture 2: N appears in row
r = min(B_N), B_N the integral values of d + (h-1)/2 over factorisations N = d h; and N appears
in row b of A141419 for each b in B_N. (L. E. Jeffery, 2013; OEIS text, CC BY-SA 4.0.)

**Result.** Both true, resolved by others: the entry states Conjecture 1 "has been proved (see
[Jeffery])" and gives a link to a proof of Conjecture 2 (H. F. W. Hoft, Apr 2016), with the
row-column formula: v = d h with h odd sits in row d + (h-1)/2 of A141419, and in A209260 at the
minimum of d + (h-1)/2 over such divisor pairs.

**Argument.** Not re-derived here; the record rests on the cited proofs. (The scan recorded only
Conjecture 1 as proved; the entry fetched 2026-11-01 for this write-up also cites Hoft's proof of
Conjecture 2.)

Lean: —.

### [A212916](A212916/): standard Young tableaux of height ≤ 10, a(n) ~ 10^n π^(−5) (10/n)^(45/2) ∏ Γ(j/2)

**Source.** OEIS [A212916](https://oeis.org/A212916) (offset 0): number of standard Young tableaux with n
cells and at most 10 rows. Conjecture (V. Kotesovec, Sep 12 2013): "generally (for tableaux with height
<= k), a(n) ~ k^n/Pi^(k/2) * (k/n)^(k*(k-1)/4) * prod(j=1..k,Gamma(j/2)); set k=10 for this sequence."
(OEIS text, CC BY-SA 4.0; revision #32.) The same general conjecture is in A229068 (k = 12), see
[`../A229068/README.md`](A229068/README.md).

**Result.** True for every k ≥ 1, by a theorem of Regev (1981).

**Argument.** Let S_k(n) = Σ f^λ over partitions λ ⊢ n with at most k rows. A. Regev, Asymptotic values for
degrees associated with strips of Young diagrams, Adv. Math. 41 (1981) 115–136, Corollary 4.4, restated with
d = α = 1 as Theorem 3.5 of A. Regev, Asymptotics of Young tableaux in the strip, the d-sums,
arXiv:1004.4476 (there T_{1,s}(m) = S_s(m), Definition 1.1), gives

S_k(n) ~ (√k)^{k(k−1)/2} · (1/k!) · n^{−k(k−1)/4} · k^n · Γ(3/2)^{−k} · ∏_{j=1..k} Γ(1 + j/2).

The 2010 paper corrects Corollary 4.4 only for d > 1 and states that the d = 1 formula is unchanged and
agrees with (F.4.5.1) of the 1981 paper.

Regev's constant equals Kotesovec's. By Γ(1 + x) = xΓ(x),
∏_{j=1..k} Γ(1 + j/2) = ∏_{j=1..k} (j/2) Γ(j/2) = (k!/2^k) ∏_{j=1..k} Γ(j/2),
and Γ(3/2) = √π/2 gives Γ(3/2)^{−k} = 2^k π^{−k/2}. The factors k! and 2^k cancel, and
(√k)^{k(k−1)/2} n^{−k(k−1)/4} = (k/n)^{k(k−1)/4}, so

S_k(n) ~ k^n π^{−k/2} (k/n)^{k(k−1)/4} ∏_{j=1..k} Γ(j/2),

which is the conjectured formula. For k = 10, ∏_{j=1..10} Γ(j/2) = (42525/32) π^{5/2}, which gives the
entry's %F line a(n) ~ 42525/32 · 10^{n+45/2} / (π^{5/2} n^{45/2}).

Lean: —.

### [A213257](A213257/): the excluded integers are the positions of 2 in a morphic word

**Source.** OEIS [A213257](https://oeis.org/A213257): a(1) = 1, a(2) = 2 and a(n) the least integer > a(n-1) such that no three terms form a progression {x, 2x, 4x}. Conjecture: "The positive integers that are not in this sequence are given by the positions of 2 in the fixed-point of the morphism 0->01, 1->02, 2->03, 3->01 (see A191255)." (C. Kimberling, 2012; OEIS text, CC BY-SA 4.0.)

**Result.** True: n is excluded from A213257 iff v_2(n) ≡ 2 (mod 3), iff the fixed point has
letter 2 at position n.

**Argument.** - Greedy set. A progression x, 2x, 4x lies inside one chain {o·2^e : e ≥ 0} (o odd). When n = o·2^e
  is considered, the larger members of its chain are not yet decided, so n is rejected iff o·2^(e-1)
  and o·2^(e-2) are both in the set. Hence membership depends only on e: e = 0, 1 in; e = 2 out;
  e = 3 in (e - 1 = 2 is out); e = 4 in; e = 5 out; ... so n is out iff e ≡ 2 (mod 3).
  (a(1) = 1, a(2) = 2 agree with this rule.)
- Morphism. The morphism is 2-uniform with every image starting with 0, so the fixed point w
  (positions from 1) has w(2m - 1) = 0 and w(2m) = g(w(m)) with g: 0→1, 1→2, 2→3, 3→1. So
  w(n) = g^(v_2(n))(0): 0, 1, 2, 3, 1, 2, 3, ... for v_2(n) = 0, 1, 2, ..., and w(n) = 2 iff
  v_2(n) ≡ 2 (mod 3), v_2(n) ≥ 2.

Lean: —.

### [A213258](A213258/): terms are the positions of 2 in a morphic word (n = 2^(3t+2)·odd)

**Source.** OEIS [A213258](https://oeis.org/A213258): positive integers not in A213257 (greedy {x,2x,4x}-free sequence). Conjecture: "The terms of this sequence are given by the positions of 2 in the fixed-point of the morphism 0 -> 01, 1 -> 02, 2 -> 03, 3 -> 01 (see A191255)." (C. Kimberling, 2012; OEIS text, CC BY-SA 4.0.)

**Result.** True: n is excluded from A213257 iff v_2(n) ≡ 2 (mod 3), iff the fixed point has
letter 2 at position n.

**Argument.** - Greedy set. A progression x, 2x, 4x lies inside one chain {o·2^e : e ≥ 0} (o odd). When n = o·2^e
  is considered, the larger members of its chain are not yet decided, so n is rejected iff o·2^(e-1)
  and o·2^(e-2) are both in the set. Hence membership depends only on e: e = 0, 1 in; e = 2 out;
  e = 3 in (e - 1 = 2 is out); e = 4 in; e = 5 out; ... so n is out iff e ≡ 2 (mod 3).
  (a(1) = 1, a(2) = 2 agree with this rule.)
- Morphism. The morphism is 2-uniform with every image starting with 0, so the fixed point w
  (positions from 1) has w(2m - 1) = 0 and w(2m) = g(w(m)) with g: 0→1, 1→2, 2→3, 3→1. So
  w(n) = g^(v_2(n))(0): 0, 1, 2, 3, 1, 2, 3, ... for v_2(n) = 0, 1, 2, ..., and w(n) = 2 iff
  v_2(n) ≡ 2 (mod 3), v_2(n) ≥ 2.

Lean: —.

### [A217319](A217319/): the P-positions of Mark-4 are 0 and the numbers with odd 4-adic valuation

**Source.** OEIS [A217319](https://oeis.org/A217319), numbers whose binary representation ends in
4k+2 or 4k+3 zeros. Formula line: "Conjecture. For n>=1, a(n) = A171949(n+1)." OEIS
[A171949](https://oeis.org/A171949), P-positions of the game Mark-4, carries the same conjecture
(V. Shevelev, Mar 2013). (OEIS text, CC BY-SA 4.0; both still conjectures on 2026-11-06.)

**Reading.** Mark-t (A. S. Fraenkel): from n a player moves to n−1, ..., n−(t−1) (staying ≥ 0) or to
⌊n/t⌋; the player unable to move loses (definition as in Guo, arXiv:1108.1239, Sec. 1). For t = 4, 0 is
the first P-position (A171949(1) = 0) and A217319 is the set of n ≥ 1 with odd 4-adic valuation (binary
trailing-zero count ≡ 2, 3 mod 4), so the conjecture says: P-positions = {0} ∪ {n ≥ 1 : v_4(n) odd}.

**Result.** True; known (Fraenkel 2012, for every t: the P-positions of Mark-t are the numbers with an odd
number of trailing zeros in base t). Reproved here in core Lean.

**Argument.** Let D = {0} ∪ {n : v_4(n) odd}. No move joins two members of D: for n ∈ D, n > 0, 4 | n and
n/4 ∉ D; the moves n−1, n−2, n−3 are positive and not divisible by 4, so not in D, and ⌊n/4⌋ = n/4 ∉ D.
Every n ∉ D (so n > 0) has a move into D: if 4 | n then n/4 ∈ D; if r = n mod 4 ≠ 0, either n − r ∈ D, or
n − r = 4q with q ≥ 1 and q ∈ D, and then ⌊n/4⌋ = q. Since moves decrease n, these two facts give
P-positions = D by strong induction.

Lean: [full proof](A217319/A217319.lean).

### [A223577](A223577/): A223578(n) = 2·A223577(n) − n + 1

**Source.** [A223577](https://oeis.org/A223577) and [A223578](https://oeis.org/A223578), both by L. Edson Jeffery,
Mar 22 2013, offset 1. With f(m) = ⌊cot(π/(2m))⌋: A223577 lists the positive integers k for which exactly one
negative integer m has −k = f(m); A223578 lists the positive integers k with f(−k−1) < f(−k) < f(−k+1).
Comments: "Conjecture: a(n) = (A223578(n) + n - 1)/2" (A223577) and "Conjecture: a(n) = 2*A223577(n) - n + 1"
(A223578). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.) Scan ids OEIS-A223577 and OEIS-A223578 (one shared
claim; the scan record of A223578 writes "A223568" for A223578, a typo).

**Reading.** f(0) is undefined, so k = 1 is not in A223578 (its data starts at 2); the Lean predicate states
k ≥ 2 explicitly. Offsets: OEIS index n is `n − 1` in `Nat.nth`.

**Result.** True for all n. Proved by Sela Fried (2025); this directory adds a Lean (Mathlib) proof.

**Argument.** 1. Let c(j) = cot(π/(2j)) and g(j) = ⌈c(j)⌉ for j ≥ 1. Since cot is odd and ⌊−x⌋ = −⌈x⌉, f(−j) = −g(j).
   So A223577 = values v ≥ 1 taken by g exactly once, A223578 = {j ≥ 2 : g(j−1) < g(j) < g(j+1)}.
2. For j ≥ 2, with a = π/(2(j+1)) and b = π/(2j): c(j+1) − c(j) = sin(b−a)/(sin a · sin b) and
   b − a = (2/π)·ab. From x − x³/6 < sin x < x, b ≤ π/4 and b − a ≤ π/12 this gives
   3/5 ≤ c(j+1) − c(j) ≤ 1; also c(1) = 0, c(2) = 1. Hence g steps by 0 or 1, g(j+2) ≥ g(j) + 1 (no value
   taken three times), g(1) = 0, g(2) = 1, and g(j) ≥ (3/5)(j − 1).
3. Counting. Let N(j) = #{i ≤ j : i ∈ A223578}. By induction on j ≥ 1,
   N(j) + j + [g(j+1) = g(j)] = 2g(j) + 1, and #{v ≤ g(j) : v ∈ A223577} = N(j).
   At j = A223578(n): g(j+1) ≠ g(j), N(j) = n and g(j) = A223577(n), so j = 2·A223577(n) − n + 1.
4. Both sets are infinite, since N(j) ≥ 2g(j) − j ≥ (j − 6)/5.

Lean: [full proof](A223577/A223577_mathlib.lean).

### [A223578](A223578/): A223578(k) = 2·A223577(k) − k + 1

**Source.** [A223578](https://oeis.org/A223578), with the linear relation to A223577 stated as a conjecture.

**Result.** True. Proved by Sela Fried (J. Integer Sequences 29 (2026), Art. 26.1.8), and reproved in Lean here.

**Argument and evidence.** See [OEIS/A223577](A223577/README.md) (Lean: `A223578_eq` in
`OEIS/A223577/A223577_mathlib.lean`).

Lean: [full proof](A223577/A223577_mathlib.lean).

### [A225003](A225003/): a(n) = A047332(n) for n ≥ 2

**Source.** OEIS [A225003](https://oeis.org/history?seq=A225003) (T. D. Noe, 2013, from
M. B. Nathanson, On the fractional parts of roots of positive real numbers, Amer. Math. Monthly 120
(2013) 409–429): "Floor(1/f(x^(1/n))) for x = e^(5/7), where f computes the fractional part",
offset 1, data 23, 2, 3, 5, 6, 7, .... Comment: "Conjecture: a(n) = A047332(n), n>1. - R. J. Mathar,
Apr 28 2013". Since 2017 the entry is "Duplicate of A047332" (dead, A. Zabolotskiy).
[A047332](https://oeis.org/A047332): numbers congruent to {0, 2, 3, 5, 6} mod 7, offset 1, with
FORMULA a(n) = floor((7n−3)/5). (OEIS text, CC BY-SA 4.0.)

**Result.** True: a(n) = floor((7n−3)/5) = A047332(n) for every n ≥ 2 (a(1) = 23); proved in
Lean 4 + Mathlib.

**Argument.** Let t = 5/(7n) ≤ 5/14 and q = floor((7n−3)/5), so 5q + 3 ≤ 7n ≤ 5q + 7, i.e.
qt ≤ 1 − 3t/5 and (q+1)t ≥ 1 − 2t/5. Taylor bounds give
1 + t + t²/2 ≤ e^t ≤ 1 + t + t²/2 + 2t³/9, so 1 < e^t < 2 and frac(e^t) = d = e^t − 1. Then
q·d ≤ (1 − 3t/5)(1 + t/2 + 2t²/9) ≤ 1 and (q+1)·d ≥ (1 − 2t/5)(1 + t/2) = 1 + t/10 − t²/5 > 1,
so q ≤ 1/d < q + 1. The values of floor((7n−3)/5) for n ≥ 1 are strictly increasing and are exactly
the numbers ≡ 0, 2, 3, 5, 6 mod 7, so they enumerate A047332.

Lean: [full proof](A225003/A225003_mathlib.lean).

### [A226160](A226160/): a(n+1)/a(n) → exp(1/φ) = 1.855276958... (harmonic-number threshold)

**Source.** OEIS [A226160](https://oeis.org/A226160): least positive integer k with 1 + 1/2 + ... + 1/k > n/φ, φ the golden ratio.
Conjecture: "a(n+1)/a(n) converges to 1.8552..." (OEIS text, CC BY-SA 4.0.) The entry adds "Conjecture
confirmed" with limit exp(1/φ) = 1.855276958... (J.-F. Alcover, 2013, from the expansion of the harmonic numbers).

**Result.** True: a(n+1)/a(n) → exp(1/φ).

**Argument.** H_k - log k decreases to Euler's γ, and H_k < log k + γ + 1/(2k). With c = 1/φ,
H_(a-1) ≤ c n < H_a for a = a(n), so log(a - 1) + γ < c n < log a + γ + 1/(2a). Hence
log a(n) = c n - γ + o(1), and a(n+1)/a(n) = exp(c + o(1)) → exp(c).

Lean: [full proof](A226160/A226160_mathlib.lean).

### [A226187](A226187/): a(n+1)/a(n) → exp(1/3)

**Source.** [A226187](https://oeis.org/A226187) (offset 1), Clark Kimberling, May 30 2013: least positive integer k
such that 1 + 1/2 + … + 1/k > n/3. Comment: conjecture that a(n+1)/a(n) converges to 1.39…, probably exp(1/3).
(OEIS text, CC BY-SA 4.0, checked 2026-11-05.)

**Result.** True: a(n+1)/a(n) → exp(1/3) = 1.39561…

**Argument.** Let H_k = 1 + … + 1/k and a = a(n).
1. Since H_0 = 0 ≤ n/3, a ≥ 1, and by minimality H_{a−1} ≤ n/3 < H_a, so 0 < H_a − n/3 ≤ 1/a.
2. a(n) → ∞: H is increasing, so a(n) < N gives n/3 < H_N, i.e. n < 3 H_N.
3. H_k − log k → γ (Euler's constant). So log a(n) − n/3 = (H_a − n/3) − (H_a − log a) → 0 − γ.
4. Hence log a(n+1) − log a(n) = [log a(n+1) − (n+1)/3] − [log a(n) − n/3] + 1/3 → 1/3, and the ratio
   a(n+1)/a(n) = exp(log a(n+1) − log a(n)) → exp(1/3).

Lean: [full proof](A226187/A226187_mathlib.lean).

### [A226188](A226188/): a(n+1)/a(n) → exp(2/3) = 1.947734... (harmonic-number threshold)

**Source.** OEIS [A226188](https://oeis.org/A226188): least positive integer k with 1 + 1/2 + ... + 1/k > 2n/3.
Conjecture: "a(n+1)/a(n) converges to 1.94..." (OEIS text, CC BY-SA 4.0.) The entry adds "Conjecture
confirmed" with limit exp(2/3) = 1.947734... (J.-F. Alcover, 2013, from the expansion of the harmonic numbers).

**Result.** True: a(n+1)/a(n) → exp(2/3).

**Argument.** H_k - log k decreases to Euler's γ, and H_k < log k + γ + 1/(2k). With c = 2/3,
H_(a-1) ≤ c n < H_a for a = a(n), so log(a - 1) + γ < c n < log a + γ + 1/(2a). Hence
log a(n) = c n - γ + o(1), and a(n+1)/a(n) = exp(c + o(1)) → exp(c).

Lean: [full proof](A226188/A226188_mathlib.lean).

### [A229068](A229068/): standard Young tableaux of height ≤ 12, a(n) ~ 12^n π^(−6) (12/n)^33 ∏ Γ(j/2)

**Source.** OEIS [A229068](https://oeis.org/A229068) (offset 0): number of standard Young tableaux with n
cells and at most 12 rows. Conjecture (V. Kotesovec, Sep 2013): "generally (for tableaux with height <= k),
a(n) ~ k^n/Pi^(k/2) * (k/n)^(k*(k-1)/4) * Product_{j=1..k} Gamma(j/2); set k=12 for this sequence."
(OEIS text, CC BY-SA 4.0; revision #18.) The same general conjecture is in A212916 (k = 10).

**Result.** True for every k ≥ 1, by a theorem of Regev (1981).

**Argument.** Identical to [`../A212916/README.md`](A212916/README.md): A. Regev, Adv. Math. 41 (1981)
115–136, Corollary 4.4, restated as Theorem 3.5 of arXiv:1004.4476, gives
S_k(n) ~ (√k)^{k(k−1)/2} (1/k!) n^{−k(k−1)/4} k^n Γ(3/2)^{−k} ∏_{j=1..k} Γ(1 + j/2) for the number S_k(n)
of standard Young tableaux with n cells and at most k rows. With
∏_{j=1..k} Γ(1 + j/2) = (k!/2^k) ∏_{j=1..k} Γ(j/2) and Γ(3/2)^{−k} = 2^k π^{−k/2} this is
k^n π^{−k/2} (k/n)^{k(k−1)/4} ∏_{j=1..k} Γ(j/2). For k = 12, ∏_{j=1..12} Γ(j/2) = (602791875/128) π^3,
which gives the entry's %F line a(n) ~ 602791875/128 · 12^{n+33} / (π^3 n^33).

Lean: —.

### [A029766](A029766/): a(n) = n!·A040039(n−1) holds on the data; the entry's name does not determine the sequence

**Source.** OEIS [A029766](https://oeis.org/A029766) (offset 0): "Unary-binary rooted trees with n nodes":
0, 1, 2, 12, 48, 360, 2160, 25200, ... (20 terms, a(0..19); reference Bergeron–Labelle–Leroux,
*Combinatorial Species and Tree-Like Structures*, p. 254). Conjecture (V. Kotesovec, Sep 2013): "for n > 0,
a(n) = n! * A040039(n-1)." The e.g.f. once printed in the entry is marked incorrect (it is the o.g.f. of
Motzkin numbers). (OEIS text, CC BY-SA 4.0; still a conjecture on 2026-11-05, revision #18.)

**Reading.** The name does not fix the data. Labelled rooted trees with every node of out-degree ≤ 2 give
1, 2, 9, 60, ... (A036774; differs at n = 3); with ordered (plane) children n!·Motzkin(n−1) = 1, 2, 12, 96, ...
(differs at n = 4). The book page was not available here, so which table column the data come from is not
known. One family matches all 19 terms: n! times the number u(n) of unlabelled unary-binary trees in which
the two branches of every binary node are equal (equivalently, such trees with labelled nodes and ordered
branches; these have no automorphisms, so each shape has n! labellings). A040039 is used as defined in its
entry: first differences of A033485 (A033485(1) = 1, A033485(n) = A033485(n−1) + A033485(⌊n/2⌋)).

**Result.** Partial. On the listed data the conjecture holds (n = 1..19). For all n it holds for the reading
above: u(n) = A040039(n−1). Whether that is the sequence the entry intends is not settled.

**Argument.** A tree of this kind with n ≥ 2 nodes is either a unary root over such a tree with n − 1
nodes, or (n odd) a binary root over two copies of such a tree with (n − 1)/2 nodes. So u(1) = 1,
u(n) = u(n−1) + [n odd]·u((n−1)/2). The sequence D(n) = A033485(⌊(n+1)/2⌋) satisfies the same recurrence
(for n = 2m+1, A033485(m+1) = A033485(m) + A033485(⌊(m+1)/2⌋)), and D(n) = A033485(n+1) − A033485(n) =
A040039(n−1) by the A033485 recurrence. (The entry of A040039 already lists this recurrence, attributed to
G. Wiseman, "using offset 1".)

Lean: [full proof](A029766/A029766_mathlib.lean).

### [A123365](A123365/): cubes mod n, partial result (two prime factors)

**Source.** OEIS [A123365](https://oeis.org/A123365): numbers k with A046530(k) = (k+2)/3, where
A046530(k) is the number of distinct cubes mod k (offset 1). Conjecture: apart from a(1) = 1 these are
exactly the primes p = 1 (mod 6). (OEIS text, CC BY-SA 4.0.)

**Result (partial; the conjecture stays open).** Write c(n) for the number of cubes mod n.
- If n has at most two distinct prime factors and 3c(n) = n + 2, then n = 1 or n is a prime = 1 (mod 6)
  (`three_c_eq_one_factor`, `three_c_ne_of_two_factors`).
- For primes p = 1 (mod 6), q = 2 (mod 3) and e >= 1, (p + 2) c(q^e) != p q^e + 2 (`cq_equation_no_solution`).
  This is the prime-power case of the second equation left by the local bounds.

**Argument.** Local bounds (method multiplicative-local-bounds) reduce every other term to the two exact
equations 3c(n) = n + 2 (all prime factors = 2 mod 3) and (p + 2) c(B) = pB + 2 (B built from such primes).
For two prime factors the cases split by residues mod 3: both 1 mod 3 fails by a ratio bound, both
2 mod 3 fails since 3(x-1)(y-1) >= xy + 2, and the mixed case reduces to the second equation with B a
prime power. There, (p + 2) s1 = p G with G = 1 + q + ... + q^(e-1) = 1 (mod q), and s1 mod q is 0, 1 or
q by e mod 3; this forces q = 2, e = 3t + 1 and (8^t - 1)(3p - 8) = 7, impossible.

Lean: [checked](A123365/A123365_mathlib.lean).

### [A010101](A010101/): a(10) ≤ 116 (upper bound improved from 117)

**Source.** OEIS [A010101](https://oeis.org/A010101), "Maximal size of binary code of length n and
asymmetric distance 2" (size of an optimal code correcting one error on the Z-channel). The entry
comment says the next three terms are known to lie in 112–117, 198–210 and 379–410. The same three
problems are N. J. A. Sloane's challenge graphs 1zc.1024, 1zc.2048, 1zc.4096
(<https://oeis.org/A265032/a265032.html>). (OEIS text, CC BY-SA 4.0.)

**Result.** a(10) ≤ 116, so a(10) ∈ [112, 116]. The upper bound 117 (Etzion–Östergård 1998, as quoted)
is improved by one. a(11) and a(12) are not improved (the same method gives exactly 210 and 410).

**Argument.** Let C be a length-10 code, a_w its number of words of weight w. Two words conflict when
max(N(x,y), N(y,x)) ≤ 1, N(x,y) = #{i : x_i = 1, y_i = 0}. Nine inequalities, each a double count of C
against cliques or subcubes, hold for every code:

| # | inequality | reason | multiplier |
|---|---|---|---|
| 1 | a_9 + 2 a_8 ≤ 10 | a weight-9 word and the 9 weight-8 words below it pairwise conflict; sum over the 10 weight-9 words | 1/10 |
| 2 | a_2 ≤ 5 | weight-2 words of C are disjoint pairs | 2/5 |
| 3 | a_8 ≤ 5 | complement of 2 | 4/5 |
| 4 | a_2 + a_3 ≤ 17 | fact F1 | 1/5 |
| 5 | a_3 + a_4 ≤ 35 | fact F2 | 1/5 |
| 6 | a_6 + a_7 ≤ 35 | complement of 5 | 1 |
| 7 | 45 a_0 + 36 a_1 ≤ 45 | in each of the 45 subcubes of dimension 8 through 0, words of weight ≤ 1 pairwise conflict | 1/45 |
| 8 | Σ_{w=1..5} w a_w ≤ 310 | for each coordinate i, words with x_i = 1 form a 9-cube in which weights 1..5 become 0..4; fact F3 there; sum over i | 1/5 |
| 9 | 9 a_9 + 10 a_10 ≤ 10 | in those 9-cubes, words of global weight 9, 10 pairwise conflict | 1/10 |

With the multipliers every a_w has total coefficient exactly 1 and the right-hand sides sum to
582/5 = 116.4, so |C| ≤ 116.

Facts (all at the stated length, for every code):
- **F1:** weights 2..3 at length 10 hold at most 17 words. Hand proof: weight-2 words form a matching M,
  weight-3 words a triangle packing of K_10 avoiding M; a packing has at most 13 triangles, and a
  13-triangle packing leaves 6 edges with odd degree everywhere, hence a vertex of degree 3, impossible
  if the leave contains a perfect matching; so |M| = 5 forces ≤ 12 triangles.
- **F2:** weights 3..4 at length 10 hold at most 35 words.
- **F3:** weights 0..4 at length 9 hold at most 31 words.

Lean: —.

