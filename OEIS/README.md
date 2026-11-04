# OEIS conjectures

Conjecture comments in the On-Line Encyclopedia of Integer Sequences (list: OEIS wiki, Talk:Conjectures/List). OEIS text is quoted under CC BY-SA 4.0 with the A-number as attribution.

124 entries: 110 resolved by this project, 14 answered elsewhere, 0 disputed or partial.

Of the 110 resolutions: 102 proved in full in Lean, 5 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 3 on paper only (re-derived by a second reader; 2 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A000040](A000040/) | trivial or misstated | prime(n) = (6f + (-1)^f - 3)/2 with f = floor(prime(n)/3) + 1 | [full proof](A000040/A000040.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md) |
| [A000120](A000120/) | trivial or misstated | columns of the base-b digit-sum triangle are constant | [full proof](A000120/A000120.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md) |
| [A004050](A004050/) | proved | only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways | [witness](A004050/A004050_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A005408](A005408/) | proved | one-coach primes and the first q odd numbers | [full proof](A005408/A005408_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A008578](A008578/) | proved | 1 and the primes are exactly the k with sigma(k) > k·Omega(k) | [full proof](A008578/A008578_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [A008676](A008676/) | proved | coefficients of 1/((1-x^3)(1-x^5)) as a floor formula | [full proof](A008676/A008676_mathlib.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A023402](A023402/) | disproved | T(n,3) and A023402 differ at n = 4 | [full proof](A023402/A023402_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A025060](A025060/) | trivial or misstated | with signs allowed, i·j + j·k + k·i takes every integer | [full proof](A025060/A025060.lean) | new (immediate) | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A029795](A029795/) | disproved | k and k^3 with the same digits are not eventually all integers | [full proof](A029795/A029795_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A051451](A051451/) | disproved | the "next twin pair above a(n)" form fails at n = 35 | [full proof](A051451/A051451_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A051924](A051924/) | disproved | a(n) ≡ n + 2 (mod n^2) also holds at n = 16843^2 | [full proof](A051924/A051924_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [known-theorem](../methods/known-theorem/README.md) |
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
| [A083452](A083452/) | trivial or misstated | n written n times exceeds n^n | [full proof](A083452/A083452.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A087324](A087324/) | disproved | no term has a perfect-square prime signature | [full proof](A087324/A087324_mathlib.lean) | partly-known | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A088104](A088104/) | proved | an n-digit prime beginning with prime(n) always exists | needs Mathlib | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A088120](A088120/) | disproved | the common difference is 2 at n = 12 | [full proof](A088120/A088120_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A088276](A088276/) | disproved | 10^k + 9351 is never prime, though 9351 ≡ 0 (mod 3) | [full proof](A088276/A088276_mathlib.lean) | known | [covering-congruences](../methods/covering-congruences/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
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
| [A104896](A104896/) | proved | counting integers below 10^n with no digit 0, 1, 2 | [full proof](A104896/A104896_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A105596](A105596/) | proved | the self-convolution with alternating signs is 1 mod 4 | [full proof](A105596/A105596_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A106249](A106249/) | proved | roots of x^n + 1 in the left half-plane (index shift by one) | [full proof](A106249/A106249_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A107363](A107363/) | proved | the nonnegative terms are exactly the Fibonacci numbers | [full proof](A107363/A107363_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md) |
| [A110320](A110320/) | proved | blocks in RNA secondary structures via Whitney numbers | [full proof](A110320/A110320_mathlib.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A110735](A110735/) | disproved | no digit insertion makes a multiple of 101 | [full proof](A110735/A110735.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A112992](A112992/) | proved | ceiling(2^r/3) is a Jacobsthal number or one more | [full proof](A112992/A112992.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A113249](A113249/) | proved | a(m, 2n+1) is a perfect square (the whole family) | [full proof](A113249/A113249.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113250](A113250/) | proved | a(m, 2n+1) is a perfect square (m = 4) | [full proof](A113250/A113250.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113251](A113251/) | proved | a(m, 2n+1) is a perfect square (m = 5) | [full proof](A113251/A113251.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113252](A113252/) | proved | a(m, 2n+1) is a perfect square (m = 6) | [full proof](A113252/A113252.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113253](A113253/) | proved | a(m, 2n+1) is a perfect square (m = 7) | [full proof](A113253/A113253.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113255](A113255/) | proved | a(m, 2n+1) is a perfect square (m = 9) | [full proof](A113255/A113255.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113256](A113256/) | proved | a(m, 2n+1) is a perfect square (m = 10) | [full proof](A113256/A113256.lean) | partly-known | [finite-identity](../methods/finite-identity/README.md) |
| [A113610](A113610/) | disproved | local minima of composite digit sums do not mark twin primes | [full proof](A113610/A113610.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A114534](A114534/) | proved | the Fibonacci matrix has rank 2 | [full proof](A114534/A114534_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A115038](A115038/) | proved | every prime is y^k − x^2 | [full proof](A115038/A115038.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A125148](A125148/) | proved | every x coprime to 10 has a prime x + 10m | [full proof](A125148/A125148_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md) |
| [A126142](A126142/) | trivial or misstated | squares of the terms are 6k+1 (trivial) | [full proof](A126142/A126142_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A129454](A129454/) | proved | p-adic valuation of a triple gcd product (true after an index shift) | [full proof](A129454/A129454_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
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
| [A165640](A165640/) | proved | a(n) = floor(4(n+4)/5) - floor(2(n+4)/3) | [full proof](A165640/A165640_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A167230](A167230/) | proved | entries of exp(Sierpiński triangle)/e are Bell numbers | [full proof](A167230/A167230_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
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
| [A182381](A182381/) | proved | Carmichael numbers divisible by 17 and 29 are 952n + 561 | [full proof](A182381/A182381_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182416](A182416/) | proved | (60k+13)(180k+37)(300k+61) is Carmichael whenever its factors are prime | [full proof](A182416/A182416_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182515](A182515/) | proved | Carmichael numbers divisible by 23 and 67 are 23·67·(66n+23) | [full proof](A182515/A182515_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182532](A182532/) | proved | Carmichael numbers divisible by 7 and 17: the four residue classes mod 120 | [full proof](A182532/A182532_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A188644](A188644/) | proved | (k^n + k^(-n))/2 is an integer for k = (√(x²-1) + x)² | [full proof](A188644/A188644_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188645](A188645/) | proved | (k^n + k^(-n))/2 is an integer for k = (√(x²+1) + x)² | [full proof](A188645/A188645_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188646](A188646/) | proved | a(n) = k a(n-1) - (k-1)/k^n is an integer sequence | [full proof](A188646/A188646_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188647](A188647/) | proved | a(n) = k a(n-1) - (k-1)/k^n is an integer sequence | [full proof](A188647/A188647_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A192205](A192205/) | proved | a(n)^(1/n) → 16√3/9 for the coefficient sum of (1-x-x^2+x^3)^n | [full proof](A192205/A192205_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A195507](A195507/) | proved | the recurrence a(n+1) = d a(n) - (d-1) n + 1 | [full proof](A195507/A195507_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A197521](A197521/) | proved | the constant 3.52133782... is 3 plus the constant of A197383 | [full proof](A197521/A197521_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A210445](A210445/) | proved | a(n) < n for n > 1 and a(n) < n/2 for n > 47 (least k with kn practical) | [full proof](A210445/A210445_mathlib.lean) | new | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A210529](A210529/) | proved | a(n) is defined for every n (Dirichlet) | [full proof](A210529/A210529_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md) |
| [A210826](A210826/) | proved | multiplicative with Dirichlet g.f. ζ(3s)/ζ(s) | [full proof](A210826/A210826_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A212843](A212843/) | proved | Carmichael numbers with prime factors ≡ 1 (mod 10) | [full proof](A212843/A212843_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A214305](A214305/) | disproved | Coman's residue conjecture for Poulet numbers fails | [full proof](A214305/A214305_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A214449](A214449/) | disproved | A214449 is not A118168 with two 1s deleted (first mismatch n = 188) | [full proof](A214449/A214449_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A214900](A214900/) | proved | every n is a sum of three squares and a fourth power | [witness](A214900/A214900.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A214970](A214970/) | proved | L(2k-1) and L(2k)+1 divide their base-φ → base-φ² images | [full proof](A214970/A214970_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A215461](A215461/) | proved | 2n is a prime plus an odd nonprime for every n > 5 | [full proof](A215461/A215461.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A215462](A215462/) | proved | 2n is a sum of two odd nonprimes for n > 19; eventual ordering | [witness](A215462/A215462_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A217448](A217448/) | proved | a(n) exists for every n (CRT) | [full proof](A217448/A217448_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A221650](A221650/) | proved | P(n,j,k) = [k \| j] p(n-j) counts partitions with at least j/k parts k | [full proof](A221650/A221650_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A225001](A225001/) | proved | floor(1/frac(e^(4/(5n)))) = A047203(n) for n > 1 | [full proof](A225001/A225001_mathlib.lean) | partly-known | [exact-arithmetic](../methods/exact-arithmetic/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226661](A226661/) | proved | 3x+k cycles with exactly n odd elements exist for every n | [full proof](A226661/A226661_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226676](A226676/) | proved | 3x-k cycles of every length N ≥ 3 exist | [full proof](A226676/A226676_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226677](A226677/) | proved | 3x-k cycles with exactly n odd elements exist for every n | [full proof](A226677/A226677_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A227553](A227553/) | proved | number of solutions of x^2 - y^2 - z^2 ≡ 1 (mod p^s) | [full proof](A227553/A227553_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228931](A228931/) | proved | the optimal ascending continued fraction of √2 - 1 follows a(k+1) = a(k)^2 - 2 | [full proof](A228931/A228931_mathlib.lean) | known | [units-pell](../methods/units-pell/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228933](A228933/) | proved | the optimal ascending continued fraction of 1/φ follows a(n) = a(n-1)^2 - 2 from the fourth term | [full proof](A228933/A228933_mathlib.lean) | partly-known | [units-pell](../methods/units-pell/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A229910](A229910/) | proved | primitive roots g with g + g⁻¹ primitive (proved); the finite-field version fails at q = 25, 121 | [witness](A229910/A229910.lean) | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A024812](A024812/) | proved | A024812(k) = (A024813(k) + k − 1)/2 | [full proof](A024812/A024812_mathlib.lean) | — | [exact-arithmetic](../methods/exact-arithmetic/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A071010](A071010/) | proved | if n is not a sum of two squares then 4 \| sigma(n) | [full proof](A071010/A071010_mathlib.lean) | — | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A085765b](A085765b/) | proved | a(n) mod 2 has period 7 | [witness](A085765b/A085765b.lean) | — | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A086449](A086449/) | proved | parity of a(n) and a(2^k − 2) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A088982](A088982/) | trivial or misstated | a prime between consecutive prime-indexed primes | — | — | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A088987](A088987/) | trivial or misstated | the number of primes between consecutive prime-indexed primes is odd | — | — | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A113599](A113599/) | proved | no term is zero (pigeonhole) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A121627](A121627/) | proved | divisibility of the "complex factorial" real parts | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A145878](A145878/) | proved | polynomial formulas for T(r+k, k), r = 3..7 (previous conjectures) | [witness](A145878/A145878.lean) | — | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A209260](A209260/) | proved | Jeffery's two conjectures (both proved in the entry's references) | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [A213257](A213257/) | proved | the excluded integers are the positions of 2 in a morphic word | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A213258](A213258/) | proved | terms are the positions of 2 in a morphic word (n = 2^(3t+2)·odd) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A226160](A226160/) | proved | a(n+1)/a(n) → exp(1/φ) = 1.855276958... (harmonic-number threshold) | [full proof](A226160/A226160_mathlib.lean) | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A226188](A226188/) | proved | a(n+1)/a(n) → exp(2/3) = 1.947734... (harmonic-number threshold) | [full proof](A226188/A226188_mathlib.lean) | — | [elementary-proof](../methods/elementary-proof/README.md) |

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

### [A029795](A029795/): k and k^3 with the same digits are not eventually all integers

**Source.** [A029795](https://oeis.org/A029795), comment by C. R. Greathouse IV (2011): "Conjecture: there
exists some m and N for which a(n) = m + n for all n >= N." (OEIS text, CC BY-SA 4.0.)

**Result.** False.

**Argument.** If a(n) = m + n for n ≥ N, every integer ≥ a(N) is a term. But for e ≥ 1, 10^e + 1 has
digits {0, 1} while (10^e + 1)^3 = 10^(3e) + 3·10^(2e) + 3·10^e + 1 has the digit 3 at position e. So
there are non-terms beyond every bound. (The same idea as M. Corneth's remark on A029797.)

Lean: [full proof](A029795/A029795_mathlib.lean).

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

**Result.** Both true.

**Argument.** - Conjecture 1. 9, 25, 35 are odd nonprimes with residues 0, 1, 2 mod 3, so for one of them c,
  d = 2n - c is divisible by 3; d is odd, and for n ≥ 22, d ≥ 9, so d is nonprime. n = 20: 40 =
  25 + 15; n = 21: 42 = 15 + 27.
- Conjecture 2. The n ordered pairs (2i+1, 2j+1) with i + j = n - 1 split as
  A002372(n) + A215461(n) + a(n) = n (stated in the entry). Let π' be the number of odd primes
  below 2n and G = A002372(n) (ordered prime pairs). Each odd prime p < 2n pairs with 2n - p, so
  A215461(n) = 2(π' - G) and a(n) = n - 2π' + G. Hence a(n) > A215461(n) iff n + 3G > 4π', true
  for large n since π' ~ 2n/log(2n) = o(n); and A215461(n) > G iff 2π' > 3G, true for large n
  since G ≪ n/log^2 n (Brun–Selberg sieve upper bound) while π' ≫ n/log n (Chebyshev).

Lean: [witness](A215462/A215462_mathlib.lean).

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

### [A121627](A121627/): divisibility of the "complex factorial" real parts

**Source.** [A121627](https://oeis.org/A121627) (a(n) = Re(∏_{k≤n} k(1+i))), comment: "Conjecture (1): Current nonzero
term divides next nonzero term ... Conjecture (2): If the term in (12, 8, 5, ...) is generated from a(n)/a(n-1) or
a(n)/a(n-2), then n divides each (12, 8, 5, ...)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. Derived in the entry from explicit formulas (H. Fischer, 2011); re-derived here.

**Argument.** a(n) = n!·Re((1+i)^n) = n!·2^(n/2)·cos(nπ/4). It vanishes iff n ≡ 2, 6 (mod 8), and otherwise
|a(n)| = n!·2^⌊n/2⌋. For consecutive nonzero indices m < n (n − m ∈ {1, 2}), a(n)/a(m) = ±(n!/m!)·2^(⌊n/2⌋−⌊m/2⌋),
an integer divisible by n.

Lean: —.

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

### [A226160](A226160/): a(n+1)/a(n) → exp(1/φ) = 1.855276958... (harmonic-number threshold)

**Source.** OEIS [A226160](https://oeis.org/A226160): least positive integer k with 1 + 1/2 + ... + 1/k > n/φ, φ the golden ratio.
Conjecture: "a(n+1)/a(n) converges to 1.8552..." (OEIS text, CC BY-SA 4.0.) The entry adds "Conjecture
confirmed" with limit exp(1/φ) = 1.855276958... (J.-F. Alcover, 2013, from the expansion of the harmonic numbers).

**Result.** True: a(n+1)/a(n) → exp(1/φ).

**Argument.** H_k - log k decreases to Euler's γ, and H_k < log k + γ + 1/(2k). With c = 1/φ,
H_(a-1) ≤ c n < H_a for a = a(n), so log(a - 1) + γ < c n < log a + γ + 1/(2a). Hence
log a(n) = c n - γ + o(1), and a(n+1)/a(n) = exp(c + o(1)) → exp(c).

Lean: [full proof](A226160/A226160_mathlib.lean).

### [A226188](A226188/): a(n+1)/a(n) → exp(2/3) = 1.947734... (harmonic-number threshold)

**Source.** OEIS [A226188](https://oeis.org/A226188): least positive integer k with 1 + 1/2 + ... + 1/k > 2n/3.
Conjecture: "a(n+1)/a(n) converges to 1.94..." (OEIS text, CC BY-SA 4.0.) The entry adds "Conjecture
confirmed" with limit exp(2/3) = 1.947734... (J.-F. Alcover, 2013, from the expansion of the harmonic numbers).

**Result.** True: a(n+1)/a(n) → exp(2/3).

**Argument.** H_k - log k decreases to Euler's γ, and H_k < log k + γ + 1/(2k). With c = 2/3,
H_(a-1) ≤ c n < H_a for a = a(n), so log(a - 1) + γ < c n < log a + γ + 1/(2a). Hence
log a(n) = c n - γ + o(1), and a(n+1)/a(n) = exp(c + o(1)) → exp(c).

Lean: [full proof](A226188/A226188_mathlib.lean).

