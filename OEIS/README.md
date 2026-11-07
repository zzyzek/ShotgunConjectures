# OEIS conjectures

Conjecture comments in the On-Line Encyclopedia of Integer Sequences (list: OEIS wiki, Talk:Conjectures/List). OEIS text is quoted under CC BY-SA 4.0 with the A-number as attribution.

405 entries: 280 resolved by this project, 113 answered elsewhere, 2 disputed or partial.

Of the 280 resolutions: 249 proved in full in Lean, 9 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 22 on paper only (re-derived by a second reader; 11 of these need Mathlib to formalise).

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
| [A008749](A008749/) | proved | a(n+2) is the first index where the minimal polyiamond perimeter reaches n + 4 | [full proof](A008749/A008749_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A023402](A023402/) | disproved | T(n,3) and A023402 differ at n = 4 | [full proof](A023402/A023402_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A024187](A024187/) | proved | e\_n(3, 4, ..., n+3) is A001711 | [full proof](A024187/A024187_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A025060](A025060/) | trivial or misstated | with signs allowed, i·j + j·k + k·i takes every integer | [full proof](A025060/A025060.lean) | new (immediate) | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A025191](A025191/) | proved | row half-sums of A025177 are first differences of A027914 and of A081673/2 | [full proof](A025191/A025191_mathlib.lean) | new (immediate) | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A026002](A026002/) | proved | Bergot's array with borders n(n−1)+1 has diagonal A026002 | [full proof](A026002/A026002_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A029795](A029795/) | disproved | k and k^3 with the same digits are not eventually all integers | [full proof](A029795/A029795_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A036284](A036284/) | proved | OEIS A036284 | [full proof](A037097/A037097_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A037096](A037096/) | proved | OEIS A037096 | [full proof](A037097/A037097_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A037097](A037097/) | proved | (x+1)- and (x^3+1)-power factors of periodic binary columns | [full proof](A037097/A037097_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A047926](A047926/) | trivial or misstated | sorted three-square representations of 3^(2n) (misindexed; reduced to r\_3(9^n)) | [full proof](A047926/A047926_mathlib.lean) | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A051451](A051451/) | disproved | the "next twin pair above a(n)" form fails at n = 35 | [full proof](A051451/A051451_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A051924](A051924/) | disproved | a(n) ≡ n + 2 (mod n^2) also holds at n = 16843^2 | [full proof](A051924/A051924_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A054096](A054096/) | proved | column 2 of A054090 is A006183 shifted right | [full proof](A054096/A054096_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A054120b](A054120b/) | proved | T(n,k) = A081577(n,k) − A081577(n−2,k−1) | [full proof](A054120b/A054120b_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md) |
| [A054656](A054656/) | proved | for n >= 23, a(n) = [n-6 prime] + [n-4 prime] + [n-1 prime] | [full proof](A054656/A054656_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A056142](A056142/) | corrected-and-proved | a(n) palindrome only if all digits of n are equal | [full proof](A056142/A056142_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A058347](A058347/) | proved | the double-support check counts are symmetric, T(n,k) = T(k,n) | [full proof](A058347/A058347_mathlib.lean) | new | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A059970](A059970/) | proved | nim-factorials of 2^n - 1 and 2^n + 2^(n-1) - 1 | needs Mathlib | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [A061002](A061002/) | proved | denominator(H(p)/H(p−1)) / numerator(H(p−1)/p^2) = p^3 | [full proof](A061002/A061002_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A065558](A065558/) | proved | a(2n) = 2 psi(n) (maximal irreducible degree of GL\_2(Z/2nZ)) | — | partly-known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A068991](A068991/) | proved | squarefree members k divide the denominator of B\_{2k} | [full proof](A068991/A068991_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A069187](A069187/) | proved | core(k) = ⌈√k⌉ exactly for k = 1 and k = n²(n²+1) with n²+1 squarefree | [full proof](A069187/A069187_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A072901](A072901/) | trivial or misstated | composites with disc Q(√n) = 4n are squarefree | [full proof](A072901/A072901_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A072939](A072939/) | proved | c(k) → ∞ exactly when n − 1 has odd 2-adic valuation, so a(n) = A036554(n) + 1 | [full proof](A072939/A072939.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [greedy-invariant](../methods/greedy-invariant/README.md) |
| [A074766](A074766/) | proved | p(2n) − 2p(n) < 2n for all n | needs Mathlib | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A075885](A075885/) | proved | limit a(n)^(1/n) = L (geometric-mean constant) | [full proof](A208060/A208060_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md) |
| [A076070](A076070/) | proved | no entry is zero | — | new | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A076072](A076072/) | proved | a multiple of n can always be formed from the digits of the next n numbers | — | new | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A077602](A077602/) | proved | M(n,1) ~ A077596(n) · sqrt(πn/2) for the Moebius polynomials | needs Mathlib | new | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A077739](A077739/) | proved | a(n) = 0 exactly for n = 11, 17, 19 | [full proof](A077739/A077739_mathlib.lean) | new (immediate) | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A077740](A077740/) | proved | a(n) = 0 iff n is 11, 17 or 19 | [full proof](A077739/A077739_mathlib.lean) | new (immediate) | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A078008](A078008/) | proved | even denominators in the rows of the Farey tree | [full proof](A078008/A078008_mathlib.lean) | partly-known | [reading-the-statement](../methods/reading-the-statement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A078122](A078122/) | proved | row sums of the M^3-shift matrix are the partitions of 3^n into powers of 3 | [full proof](A078122/A078122_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A078128](A078128/) | proved | partitions into cubes > 1 — a(n) → ∞ with explicit b(k) | [full proof](A078128/A078128_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A078173](A078173/) | proved | max t = n(n+2) and max s = 2n over solutions of rst = n(r+s+t) | [full proof](A078173/A078173_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A078537](A078537/) | proved | row sums of A078536 are the partitions of 4^n into powers of 4 | [full proof](A078537/A078537_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A079665](A079665/) | trivial or misstated | when is (b^s + 1)/(b^r + 1) an integer | [full proof](A079665/A079665_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A080674](A080674/) | proved | counting integers below 10^n with digits only in {6,7,8,9} | [full proof](A080674/A080674_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A081199](A081199/) | proved | collinear 4-tuples in the 4^n grid | [full proof](A081199/A081199_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081200](A081200/) | proved | collinear 5-tuples in the 5^n grid | [full proof](A081200/A081200_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081201](A081201/) | proved | collinear 6-tuples in the 6^n grid | [full proof](A081201/A081201_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081320](A081320/) | proved | 3-smooth part of Fibonacci numbers | [full proof](A081320/A081320_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A081532](A081532/) | disproved | T(n,3) and A023402 differ at n = 4 | [full proof](A081532/A081532_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A082981](A082981/) | proved | the six section conjectures | [full proof](A082981/A082981_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [units-pell](../methods/units-pell/README.md) |
| [A083219](A083219/) | proved | roots of x^n - x^(n-1) - ... - 1 in the left half-plane | [full proof](A129756/A129756_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A083452](A083452/) | trivial or misstated | n written n times exceeds n^n | [full proof](A083452/A083452.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A083942](A083942/) | proved | a(n) = Sum\_{k=1..2^n-1} Catalan(k) | [full proof](A083942/A083942_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A084043](A084043/) | proved | a(n) = 0 iff 10 divides n | [full proof](A084043/A084043_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A084044](A084044/) | proved | a(n) = 0 iff 10 divides n | [full proof](A084043/A084043_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A087324](A087324/) | disproved | no term has a perfect-square prime signature | [full proof](A087324/A087324_mathlib.lean) | partly-known | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A087726](A087726/) | proved | a(n) = n^2 if and only if n is squarefree | [full proof](A087726/A087726_mathlib.lean) | partly-known | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [parametric-family](../methods/parametric-family/README.md) |
| [A088104](A088104/) | proved | an n-digit prime beginning with prime(n) always exists | needs Mathlib | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A088120](A088120/) | disproved | the common difference is 2 at n = 12 | [full proof](A088120/A088120_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A088226](A088226/) | corrected-and-proved | a(n) = \|a(n-1) − a(n-2) − a(n-3)\| is half the smallest even distance from n − 1 to a square | [full proof](A088226/A088226_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A088276](A088276/) | disproved | 10^k + 9351 is never prime, though 9351 ≡ 0 (mod 3) | [full proof](A088276/A088276_mathlib.lean) | known | [covering-congruences](../methods/covering-congruences/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A088617](A088617/) | proved | mean number of U steps in a Schröder n-path is ~ n/√2 | [checked](A088617/A088617_mathlib.lean) | new (immediate) | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A089758](A089758/) | proved | the prime concatenation chain never stops | [full proof](A089758/A089758_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A090519](A090519/) | proved | some prime p has floor(10^n/p) prime | [full proof](A090519/A090519_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md) |
| [A094787](A094787/) | proved | every prime is a least prime p with p + n a perfect power | [full proof](A094787/A094787_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [parametric-family](../methods/parametric-family/README.md) |
| [A096123](A096123/) | disproved | a(n) = n!/(p-1)! for large n (p least prime with n ≤ 2p) is false | [full proof](A096123/A096123_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A096127](A096127/) | proved | a(n) = n+1 exactly when n is a prime power | [full proof](A096127/A096127_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A097406](A097406/) | trivial or misstated | primitive prime factors of 2^n − 1 are ≡ 1 (mod n) | [full proof](A097406/A097406_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A097945](A097945/) | proved | Sum mu(n)/phi(n) = 0 | [full proof](A097945/A097945_mathlib.lean) | partly-known | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A098016](A098016/) | trivial or misstated | the mean of consecutive primes is never prime | [full proof](A098016/A098016_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A100056](A100056/) | disproved | the A054065 permutations do not maximize the sum of differences | [full proof](A100056/A100056_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A100682](A100682/) | disproved | exception list of Greathouse's formula is incomplete | [full proof](A100682/A100682_mathlib.lean) | new | [exact-arithmetic](../methods/exact-arithmetic/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A101312](A101312/) | trivial or misstated | other weekday/day pairs do not give a shifted Friday-13th sequence | — | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A101462](A101462/) | disproved | 2^k − 509203 is never prime, so a(42228) does not exist | [full proof](A101462/A101462_mathlib.lean) | known | [covering-congruences](../methods/covering-congruences/README.md) |
| [A102237](A102237/) | proved | a(n) = 2^n for n > 5 | needs Mathlib | new | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A102613](A102613/) | trivial or misstated | π(n)/(n − π(n)) → 0 | [full proof](A102613/A102613_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md) |
| [A103990](A103990/) | proved | sqrt(pi) I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1) | [full proof](A103990/A103990_mathlib.lean) | new | [reading-the-statement](../methods/reading-the-statement/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
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
| [A113676](A113676/) | proved | row lengths of Golomb's sequence cut into rows = first differences of A014644 | [full proof](A113676/A113676_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A114534](A114534/) | proved | the Fibonacci matrix has rank 2 | [full proof](A114534/A114534_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A115038](A115038/) | proved | every prime is y^k − x^2 | [full proof](A115038/A115038.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A116731](A116731/) | proved | bubble sort produces (n^3 − 3n^2 + 5n)/3 distinct (flips, iterations) pairs | [full proof](A116731/A116731_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A119659](A119659/) | proved | consecutive prime-indexed primes form a triangle from (17, 31, 41) on | needs Mathlib | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [ordered-prime-gap-bound](../methods/ordered-prime-gap-bound/README.md) |
| [A123722](A123722/) | proved | multiples of 3 in the list are 3 and 3p (p prime), and every odd prime occurs | [full proof](A123722/A123722_mathlib.lean) | new (immediate) | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A123723](A123723/) | proved | multiples of 4 in the list, other than 4, are 4p with p prime | [full proof](A123723/A123723_mathlib.lean) | new (immediate) | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A124431](A124431/) | proved | Mathar's recurrence for Σ 2^k C(⌊(n+k)/2⌋, k) C(⌊(n+k+1)/2⌋, k) | [full proof](A124431/A124431_mathlib.lean) | new (immediate) | [creative-telescoping](../methods/creative-telescoping/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A125148](A125148/) | proved | every x coprime to 10 has a prime x + 10m | [full proof](A125148/A125148_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md) |
| [A126142](A126142/) | trivial or misstated | squares of the terms are 6k+1 (trivial) | [full proof](A126142/A126142_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A127749](A127749/) | proved | see A127750 | [full proof](A127750/A127750_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A127750](A127750/) | proved | row sums mod 2 are the Fredholm-Rueppel sequence | [full proof](A127750/A127750_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A129454](A129454/) | proved | p-adic valuation of a triple gcd product (true after an index shift) | [full proof](A129454/A129454_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A129756](A129756/) | proved | roots of x^n − x^(n−1) − … − x − 1 in the right half-plane | [full proof](A129756/A129756_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A131262](A131262/) | proved | least k with A130654(k) = n equals sigma(2^n) phi(2^n) | [full proof](A131262/A131262_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A132089](A132089/) | proved | the first column of L^(m+1) is the row-sum sequence of L^m (L = Losanitsch's triangle) | [full proof](A132089/A132089.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A132827](A132827/) | proved | the array is the dispersion of floor(n\*phi + n + 1); the entry's FORMULA is wrong from row 4 | [full proof](A132827/A132827_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A133212](A133212/) | proved | a(n) = 2\*A038503(n+3) for n > 0 | [full proof](A133212/A133212_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md) |
| [A134002](A134002/) | proved | n(n+5) = a(a+5) + b(b+5) is solvable iff n^2 + (n+5)^2 is composite | [full proof](A134002/A134002_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A134003](A134003/) | proved | n(n+5) = a(a+5) + b(b+5) has no positive solution when n^2 + (n+5)^2 is prime | [full proof](A134003/A134003_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A135499](A135499/) | trivial or misstated | equal digit sums at odd and even positions implies 11 \| n (trivial) | [full proof](A135499/A135499.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A135571](A135571/) | proved | differences of two positive triangular numbers in an odd number of ways | [full proof](A135571/A135571_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A135659](A135659/) | proved | every Mersenne prime > 3 is ≡ 7 (mod 24) | [full proof](A135659/A135659.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A137328](A137328/) | disproved | the prime 2 never occurs | [full proof](A137328/A137328_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A138808](A138808/) | proved | the row sums of A010766 are upper bounds | [full proof](A138808/A138808_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A139043](A139043/) | proved | sum of composites ≤ 10^n versus 10^n(10^n+1)/2 - 1 - (10^n)^2/(2 log 10^n - 1) | [witness](A139043/A139043_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md) |
| [A140869](A140869/) | proved | if h is not a term, then 4h + 5 is prime | [full proof](A140869/A140869.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A141419](A141419/) | proved | diagonal of S\_N^T S\_N (Chebyshev U sums) equals the triangle | [full proof](A141419/A141419_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A141459](A141459/) | proved | denominators of ∫\_0^1 log(1 - 1/x)^n dx | [full proof](A141459/A141459_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A144652](A144652/) | proved | if h is not a term, then 4h + 1 is prime (h ≥ 1) | [full proof](A144652/A144652.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A152718](A152718/) | proved | inverse Motzkin transform of A054393 | [full proof](A152718/A152718_mathlib.lean) | new | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A155005](A155005/) | disproved | a(5+5n) = 1125\*10^n for n > 0 | [full proof](A155005/A155005_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md) |
| [A156833](A156833/) | proved | for n > 1, a(n) = n iff n is prime | [full proof](A156834/A156834_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md) |
| [A156834](A156834/) | proved | for n > 1, a(n) = n iff n is prime | [full proof](A156834/A156834_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A156869](A156869/) | proved | T(2n + m, n + m) = T(2n, n) iff m >= 0 | [full proof](A156870/A156870_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A156870](A156870/) | proved | T(2n + m, n + m) = T(2n, n) iff m >= 0 | [full proof](A156870/A156870_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A156907](A156907/) | proved | integer series | [full proof](A183241/A156907_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A156908](A156908/) | proved | integer series | [full proof](A183241/A156907_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A157308](A157308/) | proved | a(m) is odd iff m = 0 or m is a power of 2 | [full proof](A157308/A157308_mathlib.lean) | new | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A157675](A157675/) | proved | integer series | [full proof](A183241/A157675_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A158233](A158233/) | proved | the terms are only 0, 3, 4, 6 | [full proof](A158233/A158233_mathlib.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A160217](A160217/) | proved | every greedy start m merges with A160217 | [full proof](A160217/A160217_mathlib.lean) | new | [greedy-invariant](../methods/greedy-invariant/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A163138](A163138/) | proved | exp(Σ (q^n + A)^n x^n/n) = A is an integer series for every integer q | [full proof](A163138/A163138_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A163921](A163921/) | proved | G(x) = exp(Σ G(L(n) x)^n x^n/n) is integral whenever exp(Σ L(n) x^n/n) is | [full proof](A163921/A163921_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A164754](A164754/) | proved | a(n) = 4n^2 - 11n + 5 for n >= 3 | [full proof](A164754/A164754_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A165300](A165300/) | proved | Layman's four rules for the 1,2-path sequence | [full proof](A165300/A165300_mathlib.lean) | new (immediate) | [greedy-invariant](../methods/greedy-invariant/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A165460](A165460/) | proved | Jacobi-bridge conjecture | [full proof](A165463/A165463_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A165462](A165462/) | proved | Jacobi-bridge conjecture | [full proof](A165463/A165463_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A165463](A165463/) | proved | Jacobi-bridge heights at the 1/3 and 1/2 points | [full proof](A165463/A165463_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A165640](A165640/) | proved | a(n) = floor(4(n+4)/5) - floor(2(n+4)/3) | [full proof](A165640/A165640_mathlib.lean) | new (immediate) | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A165886](A165886/) | proved | a(n)/A141459(n+1) = A006519(n+1) | [full proof](A165886/A165886_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A165940](A165940/) | proved | integer series | [full proof](A183241/A165940_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A166102](A166102/) | proved | a(n) = 3·A166103(n) | [full proof](A166103/A166103_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A166103](A166103/) | proved | odd k with k ∤ Σ{i ≤ k : J(i,k) = 1} are exactly 3·m², m ∈ A166104 | [full proof](A166103/A166103_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A166268](A166268/) | proved | Jacobi-bridge height identity for m = 12n+7 | [full proof](A166273/A166273_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A166269](A166269/) | proved | Jacobi-bridge height identity for m = 12n+7 | [full proof](A166273/A166273_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A166270](A166270/) | proved | Jacobi-bridge height identity for m = 12n+7 | [full proof](A166273/A166273_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A166271](A166271/) | proved | Jacobi-bridge height identity for m = 12n+7 | [full proof](A166273/A166273_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A166272](A166272/) | proved | the reduced denominator is always 3 | [full proof](A166272/A166272_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A166273](A166273/) | proved | Jacobi-bridge heights at m/6, m/3, m/2 for m = 12n+7 | [full proof](A166273/A166273_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A166407](A166407/) | proved | A166406(n)/(2n+1) is an integer except on A166101, where its denominator is 3 | needs Mathlib | new | [known-theorem](../methods/known-theorem/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A167230](A167230/) | proved | entries of exp(Sierpiński triangle)/e are Bell numbers | [full proof](A167230/A167230_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A170941](A170941/) | proved | involutions without adjacent transpositions, proportion → 1/e | [full proof](A170941/A170941_mathlib.lean) | new | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [creative-telescoping](../methods/creative-telescoping/README.md) |
| [A173643](A173643/) | disproved | the odd-part formula needs K = 0 (counterexample 3) | [full proof](A173643/A173643_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A174470](A174470/) | proved | integer series | [full proof](A183241/A174470_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A174846](A174846/) | proved | \|a(n)/n!\|^(-1/n) tends to pi/4 = 0.7853... | needs Mathlib | partly-known | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A176494](A176494/) | disproved | an odd prime p with \|2^m - p\| composite for every m ≥ 1 | [full proof](A176494/A176494.lean) | known | [covering-congruences](../methods/covering-congruences/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A176827](A176827/) | proved | the q-analogue a(n,q) is an integer for every positive integer q | [full proof](A176827/A176827_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A176948](A176948/) | proved | every n >= 4 except 6 has an n-gonal number that is not k-gonal for 3 <= k < n | [full proof](A176948/A176948_mathlib.lean) | new | [modular-obstruction](../methods/modular-obstruction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A177430](A177430/) | proved | exp(sum b(n)^m x^n/n) is integral exactly for even m >= 0 | [full proof](A177430/A177430_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A177431](A177431/) | proved | exp(sum a(n)^m x^n/n) integral only for even m >= 0 | [full proof](A177430/A177430_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A178473](A178473/) | proved | OEIS A178473 | [full proof](A178473/A178473_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A178612](A178612/) | proved | no term is a square (rank-0 elliptic curve) | [checked](A178612/A178612_mathlib.lean) | new (immediate) | [reduction-to-constant](../methods/reduction-to-constant/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A179873](A179873/) | proved | nondecreasing sequence of odd numbers | [full proof](A179874/A179874_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A179874](A179874/) | proved | integral antiharmonic means of the units mod h are odd and nondecreasing | [full proof](A179874/A179874_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A179902](A179902/) | proved | the parity pattern 1, 0, 1, 1 (period 4) holds | [full proof](A179902/A179902_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A180654](A180654/) | proved | Σ log(Σ\_k C(n,k)^p x^k)^n/(n! n^n) is an integer e.g.f. (Conjectures 1-3) | [full proof](A180654/A180654_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A180710](A180710/) | disproved | sigma(n) \| a(n) fails at n = 64 | — | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A181070](A181070/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A181074](A181074/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A181076](A181076/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A181078](A181078/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A181080](A181080/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A181082](A181082/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A181084](A181084/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A181316](A181316/) | proved | exp(Σ (q-1)((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series for every q > 1 | [full proof](A181316/A181316_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
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
| [A182372](A182372/) | proved | sets with perimeter n and two-sort partitions are equinumerous | [checked](A182372/A182372_mathlib.lean) | new | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182381](A182381/) | proved | Carmichael numbers divisible by 17 and 29 are 952n + 561 | [full proof](A182381/A182381_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182416](A182416/) | proved | (60k+13)(180k+37)(300k+61) is Carmichael whenever its factors are prime | [full proof](A182416/A182416_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A182515](A182515/) | proved | Carmichael numbers divisible by 23 and 67 are 23·67·(66n+23) | [full proof](A182515/A182515_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182532](A182532/) | proved | Carmichael numbers divisible by 7 and 17: the four residue classes mod 120 | [full proof](A182532/A182532_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A182963](A182963/) | proved | integer series | [full proof](A183241/A183241_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A183128](A183128/) | proved | integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A183129](A183129/) | proved | binomial-power Hanna series are integer series | [full proof](A183129/A183129_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A183241](A183241/) | proved | seven Hanna series are integer series | [full proof](A183241/A183241_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A187011](A187011/) | proved | det(\|p\_i − p\_j\|) over the first n primes | [full proof](A187011/A187011_growth_mathlib.lean) | partly-known | [selberg-sieve-polynomial](../methods/selberg-sieve-polynomial/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188644](A188644/) | proved | (k^n + k^(-n))/2 is an integer for k = (√(x²-1) + x)² | [full proof](A188644/A188644_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188645](A188645/) | proved | (k^n + k^(-n))/2 is an integer for k = (√(x²+1) + x)² | [full proof](A188645/A188645_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188646](A188646/) | proved | a(n) = k a(n-1) - (k-1)/k^n is an integer sequence | [full proof](A188646/A188646_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A188647](A188647/) | proved | a(n) = k a(n-1) - (k-1)/k^n is an integer sequence | [full proof](A188647/A188647_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A192062](A192062/) | proved | the prime chain T(2n) = A(n)T(n), A(3n) = A(n)B(n), B(5n) = B(n)C(n), ... has integer factors | needs Mathlib | new | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A192205](A192205/) | proved | a(n)^(1/n) → 16√3/9 for the coefficient sum of (1-x-x^2+x^3)^n | [full proof](A192205/A192205_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A193550](A193550/) | proved | sqrt((A(x) - 1)/x) is an integer series | [full proof](A193550/A193550_mathlib.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A195507](A195507/) | proved | the recurrence a(n+1) = d a(n) - (d-1) n + 1 | [full proof](A195507/A195507_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A195538](A195538/) | proved | denominators of Pythagorean approximations to √8 satisfy a(n) = 35a(n−2) − 35a(n−4) + a(n−6) | [full proof](A195538/A195538_mathlib.lean) | new (immediate) | [units-pell](../methods/units-pell/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A195539](A195539/) | proved | numerators of Pythagorean approximations to √8 satisfy b(n) = 34b(n−2) − b(n−4) | [full proof](A195539/A195539_mathlib.lean) | new (immediate) | [units-pell](../methods/units-pell/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A195608](A195608/) | proved | first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts | [full proof](A195608/A195608_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [A195609](A195609/) | proved | first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts | [full proof](A195608/A195608_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md) |
| [A195673](A195673/) | proved | p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x) | [full proof](A195673/A195673_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A195825](A195825/) | proved | plateaus of the columns of the generalized pentagonal-number array | [full proof](A195825/A195825_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A196226](A196226/) | disproved | the term 690 violates all three σ\_k congruences | [witness](A196226/A196226_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A197521](A197521/) | proved | the constant 3.52133782... is 3 plus the constant of A197383 | [full proof](A197521/A197521_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A197702](A197702/) | proved | least k with n = ±1 ±3 ± … ±(2k−1) | [full proof](A197702/A197702_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A202150](A202150/) | proved | the odd coefficients of the q-analog of π/2 sit exactly at 3n(n+1) | [full proof](A202150/A202150_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A202941](A202941/) | proved | Shevelev's generalized binomials at the first p-row | [full proof](A202941/A202941_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A202943](A202943/) | proved | a(n) is odd iff n has no 1-bit at an even position ≥ 2 | [full proof](A202943/A202943_mathlib.lean) | new (immediate) | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A203278](A203278/) | proved | OEIS A203278 | [full proof](A203278/A203278_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A203484](A203484/) | proved | OEIS A203484 | [full proof](A203484/A203484_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A203498](A203498/) | proved | OEIS A203498 | [full proof](A203498/A203498_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A203509](A203509/) | proved | OEIS A203509 | [full proof](A203509/A203509_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A207969](A207969/) | proved | exp(Σ 5 F(n)^(2k) x^n/n) is an integer series | [full proof](A207969/A207969_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A207970](A207970/) | proved | exp(Σ 5 F(n)^6 x^n/n) | [full proof](A207969/A207969_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A208034](A208034/) | proved | exp(Σ 2 Pell(n)^(2k) xⁿ/n) is an integer series; the odd-power and halved versions are not | [full proof](A208034/A208034_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A208060](A208060/) | proved | lim a(n)^(1/n) = 2L, L the Lüroth geometric mean | [full proof](A208060/A208060_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md) |
| [A209860](A209860/) | proved | A054429 commutes with the permutation A209861/A209862 | [full proof](A209860/A209860_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A209861](A209861/) | proved | A054429 commutes with the permutation A209861/A209862 | [full proof](A209860/A209860_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A209862](A209862/) | proved | A054429 commutes with the permutation A209861/A209862 | [full proof](A209860/A209860_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A210445](A210445/) | proved | a(n) < n for n > 1 and a(n) < n/2 for n > 47 (least k with kn practical) | [full proof](A210445/A210445_mathlib.lean) | new | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A210456](A210456/) | proved | periods of digital roots of n-step Fibonacci numbers (divisibility by 3, Helenius's closed forms) | needs Mathlib | new | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A210529](A210529/) | proved | a(n) is defined for every n (Dirichlet) | [full proof](A210529/A210529_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md) |
| [A210826](A210826/) | proved | multiplicative with Dirichlet g.f. ζ(3s)/ζ(s) | [full proof](A210826/A210826_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A211163](A211163/) | proved | numerators of (-1/π^n) ∫\_0^1 log(1-1/x)^n dx | [full proof](A141459/A141459_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A212392](A212392/) | proved | n divides a(n) for A(x) = (x + A(A(x)))^2 | [full proof](A212425/A212425_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A212425](A212425/) | proved | ((b−1)(n−1)+1) divides the coefficients of A(x) = (x + A(A(x)))^b | [full proof](A212425/A212425_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A212843](A212843/) | proved | Carmichael numbers with prime factors ≡ 1 (mod 10) | [full proof](A212843/A212843_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A214074](A214074/) | disproved | a(n) = 3 is not the residue class n ≡ 121 (mod 330) | [witness](A214074/A214074_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A214305](A214305/) | disproved | Coman's residue conjecture for Poulet numbers fails | [full proof](A214305/A214305_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A214449](A214449/) | disproved | A214449 is not A118168 with two 1s deleted (first mismatch n = 188) | [full proof](A214449/A214449_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A214900](A214900/) | proved | every n is a sum of three squares and a fourth power | [witness](A214900/A214900.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A214970](A214970/) | proved | L(2k-1) and L(2k)+1 divide their base-φ → base-φ² images | [full proof](A214970/A214970_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A215461](A215461/) | proved | 2n is a prime plus an odd nonprime for every n > 5 | [full proof](A215461/A215461.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A215462](A215462/) | proved | 2n is a sum of two odd nonprimes for n > 19; eventual ordering | [full proof](A215462/A215462_conj2_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [selberg-sieve-polynomial](../methods/selberg-sieve-polynomial/README.md) |
| [A215944](A215944/) | disproved | Coman's 5461(42k − 13) exception claim is false (counterexample 3048841) | [witness](A215944/A215944_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A216971](A216971/) | proved | every entry of row n is divisible by n | [full proof](A216971/A216971_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A217396](A217396/) | proved | 2^k − 2 twice a triangular or 3/2 a tetrahedral number only for k = 1, 2, 3, 5, 7, 13 | [witness](A217396/A217396_mathlib.lean) | partly-known | [units-pell](../methods/units-pell/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A217448](A217448/) | proved | a(n) exists for every n (CRT) | [full proof](A217448/A217448_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A217482](A217482/) | proved | tetrahedral numbers T with 3T/2 + 2 a power of 2 | [witness](A217396/A217396_mathlib.lean) | new | [units-pell](../methods/units-pell/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A217876](A217876/) | proved | adjacent transpositions in a random involution are asymptotically Poisson(1) | [checked](A217876/A217876_mathlib.lean) | new (immediate) | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A219197](A219197/) | proved | the square root of the A199033 g.f. has no coefficient = 3 (mod 4) | needs Mathlib | new | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A219431](A219431/) | proved | a(odd) ≡ 2 and a(even) ≡ 0 (mod 4) | [full proof](A219431/A219431_mathlib.lean) | partly-known | [modular-obstruction](../methods/modular-obstruction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A221650](A221650/) | proved | P(n,j,k) = [k \| j] p(n-j) counts partitions with at least j/k parts k | [full proof](A221650/A221650_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md) |
| [A225001](A225001/) | proved | floor(1/frac(e^(4/(5n)))) = A047203(n) for n > 1 | [full proof](A225001/A225001_mathlib.lean) | partly-known | [exact-arithmetic](../methods/exact-arithmetic/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A225004](A225004/) | proved | a(n) divides n² | [full proof](A225004/A225004_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md) |
| [A225660](A225660/) | proved | a(n) is odd for n > 9 | [full proof](A225660/A225660_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A225919](A225919/) | proved | the greedy harmonic-block sequence for f(k) = 1/(k+4) is linearly recurrent | — | new | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A226661](A226661/) | proved | 3x+k cycles with exactly n odd elements exist for every n | [full proof](A226661/A226661_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226676](A226676/) | proved | 3x-k cycles of every length N ≥ 3 exist | [full proof](A226676/A226676_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226677](A226677/) | proved | 3x-k cycles with exactly n odd elements exist for every n | [full proof](A226677/A226677_mathlib.lean) | partly-known | [parametric-family](../methods/parametric-family/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A227345](A227345/) | proved | a distinct-part partition of n with boundary size k exists iff 3k^2/4 <= n | [full proof](A227345/A227345_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [parametric-family](../methods/parametric-family/README.md) |
| [A227370](A227370/) | proved | an involution made of the transpositions (2k-1, 2k), k in A061887 | [checked](A227370/A227370_mathlib.lean) | new | [greedy-invariant](../methods/greedy-invariant/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A227500](A227500/) | proved | (b(n) - a(n))/c(n) is 0, 0 followed by the Fibonacci numbers | [full proof](A227500/A227500_mathlib.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A227553](A227553/) | proved | number of solutions of x^2 - y^2 - z^2 ≡ 1 (mod p^s) | [full proof](A227553/A227553_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A227786](A227786/) | proved | positions of 2 in A227761 | [full proof](A227786/A227786_mathlib.lean) | new | [greedy-invariant](../methods/greedy-invariant/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228095](A228095/) | proved | Sun's Legendre-symbol determinants vanish on residue classes | [full proof](A228095/A228095_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A228469](A228469/) | proved | least c with an alternating trace (Kimberling) | [full proof](A228469/A228469_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [greedy-invariant](../methods/greedy-invariant/README.md) |
| [A228471](A228471/) | proved | least c whose trace begins 1010... (Kimberling) | [full proof](A228469/A228469_mathlib.lean) | new | [elementary-proof](../methods/elementary-proof/README.md), [greedy-invariant](../methods/greedy-invariant/README.md) |
| [A228916](A228916/) | proved | indices of primes in A108300 are 1 and multiples of 3 | [full proof](A228916/A228916_mathlib.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228931](A228931/) | proved | the optimal ascending continued fraction of √2 - 1 follows a(k+1) = a(k)^2 - 2 | [full proof](A228931/A228931_mathlib.lean) | known | [units-pell](../methods/units-pell/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228933](A228933/) | proved | the optimal ascending continued fraction of 1/φ follows a(n) = a(n-1)^2 - 2 from the fourth term | [full proof](A228933/A228933_mathlib.lean) | partly-known | [units-pell](../methods/units-pell/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A228934](A228934/) | proved | the optimal ascending continued fraction of √44 − 6 follows a two-step recurrence | [full proof](A228934/A228934_mathlib.lean) | new (immediate) | [units-pell](../methods/units-pell/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A229910](A229910/) | proved | primitive roots g with g + g⁻¹ primitive (proved); the finite-field version fails at q = 25, 121 | [witness](A229910/A229910.lean) | known | [known-theorem](../methods/known-theorem/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A005376](A005376/) | proved | a(n) is approximately c\*n, c the real root of x^5 + x - 1 | — | known | [known-theorem](../methods/known-theorem/README.md), [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md) |
| [A007413](A007413/) | proved | counts of 1's between consecutive 2's of A076826 | [full proof](A007413/A007413_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A007645](A007645/) | proved | OEIS A007645 = A002383 ∪ A162471 (proved), and the A002383 intersection conjecture (open) | [full proof](A007645/A007645_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A007669](A007669/) | disproved | A007669(n) = A178717(n−1) − 1 is false (first failure n = 8) | [full proof](A007669/A007669_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A008683b](A008683b/) | proved | a moved-corner divisibility matrix has determinant μ(n) and A074206(n) nonzero terms | [witness](A008683b/A008683b.lean) | known | [reading-the-statement](../methods/reading-the-statement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A022344](A022344/) | proved | Fibonacci sequences in the Wythoff array and the product of characteristics | [witness](A022344/A022344.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A024812](A024812/) | proved | A024812(k) = (A024813(k) + k − 1)/2 | [full proof](A024812/A024812_mathlib.lean) | — | [exact-arithmetic](../methods/exact-arithmetic/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A029905](A029905/) | disproved | r(n) and h(n) are not complementary (row 120 of 3-row Chomp is in neither) | — | partly-known | [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md), [greedy-invariant](../methods/greedy-invariant/README.md) |
| [A030210](A030210/) | proved | coefficients of (η(q)η(q^5))^4 satisfy \|a(p)\| < 2p^(3/2) | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A053029](A053029/) | proved | which m have 4 (resp. 1) zeros in the Fibonacci numbers mod m | [full proof](A053029/A053029_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A053031](A053031/) | proved | m has one zero in the Fibonacci numbers mod m iff ... | [full proof](A053029/A053029_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A063289b](A063289b/) | trivial or misstated | newform dimension formula for Gamma\_1(16) (9n/4 is a typo for 9n/2) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A063305](A063305/) | trivial or misstated | newform dimension formula for Gamma\_1(32) (18n is missing the constant -41) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A063321](A063321/) | trivial or misstated | newform dimension formula for Gamma\_1(48) (the constant -72 was dropped) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A063337](A063337/) | trivial or misstated | newform dimension formula for Gamma\_1(64) (72n is missing the constant -155) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A064016](A064016/) | misstated | the limit comment is misstated; a(n)/10^(2n) → 1/2 − 3/π² (Mertens) | [full proof](A064016/A064016_mathlib.lean) | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A071010](A071010/) | proved | if n is not a sum of two squares then 4 \| sigma(n) | [full proof](A071010/A071010_mathlib.lean) | — | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A078130](A078130/) | proved | numbers with exactly one representation as a sum of cubes > 1 — last term 218 | [full proof](A078130/A078130_mathlib.lean) | known | [complete-table-scan](../methods/complete-table-scan/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A079128](A079128/) | proved | gcd(a(n), n) = 1 for permutations with relatively prime cycle lengths | [full proof](A079128/A079128_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A079267](A079267/) | proved | the number of short pairs in a random perfect matching of [2n] tends to Poisson(1) | [witness](A079267/A079267.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A081847](A081847/) | disproved | see A082235 | [full proof](A082235/A082235_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A082108](A082108/) | proved | a(n−1) is the largest integer keeping the partial sum below 1 | [full proof](A082108/A082108_mathlib.lean) | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A082235](A082235/) | disproved | the triangular numbers 1, 21, 28, 45, 78, 91 are never hit | [full proof](A082235/A082235_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A085765b](A085765b/) | proved | a(n) mod 2 has period 7 | [witness](A085765b/A085765b.lean) | — | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A086449](A086449/) | proved | parity of a(n) and a(2^k − 2) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A088982](A088982/) | trivial or misstated | a prime between consecutive prime-indexed primes | — | — | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A088987](A088987/) | trivial or misstated | the number of primes between consecutive prime-indexed primes is odd | — | — | [elementary-proof](../methods/elementary-proof/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A094913](A094913/) | proved | maximal number of distinct nonempty factors of a binary word of length n equals A006697(n) − 1 | — | known | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A095380](A095380/) | proved | the proportion of non-values of σ up to 2^n tends to 1 | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A097602](A097602/) | proved | the squares hit are exactly m² with 3 ∤ m | [full proof](A097602/A097602_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A098021](A098021/) | proved | former and current definitions agree | [full proof](A098021/A098021_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A103152](A103152/) | disproved | a(23) = 725 is not divisible by 3 | [witness](A103152/A103152_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A109926](A109926/) | trivial or misstated | "a(n+15) == 0 (mod 30) for n > 4" is false as printed; the mod 3 and mod 15 claims are out of reach | [full proof](A109926/A109926_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A111677](A111677/) | misstated | "a(n) = 0 iff n ≡ 3 (mod 5)" fails at n = 1 | [full proof](A111677/A111677_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A113599](A113599/) | proved | no term is zero (pigeonhole) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A115509](A115509/) | proved | a(n) = 0 for 2^(k+1) ≤ n < 3·2^k | [full proof](A115509/A115509_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A117414](A117414/) | trivial or misstated | an Euler triangle without a definition (row sums, columns 1 and 2) | needs Mathlib | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A118990](A118990/) | proved | A118990(n) = 2^n A086906(n-1) | [full proof](A118990/A118990_mathlib.lean) | known | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A121627](A121627/) | proved | divisibility of the "complex factorial" real parts | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A122957](A122957/) | trivial or misstated | "except for 1,2,3,4, this is the nonzero values of A066362" is false | [full proof](A122957/A122957_mathlib.lean) | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A123721](A123721/) | trivial or misstated | first occurrences of k in A123249(n) - 2n | [full proof](A123721/A123721_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A129364](A129364/) | known | a(n) divides A092287(n) (known) | — | known | [known-theorem](../methods/known-theorem/README.md), [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md) |
| [A131439](A131439/) | proved | 1, 7, then 4k + 14, and its inverse binomial transform | [full proof](A131439/A131439_mathlib.lean) | known | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A132293](A132293/) | trivial or misstated | maximal number of right angles in an n-gon (Mathar's correction) | — | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A132870](A132870/) | disproved | see A177390 | [witness](A177390/A177390.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A136269](A136269/) | proved | a(3k) = (3/4)10^(4k) + 5\*10^(k-1) - 1 | [full proof](A136269/A136269_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A138684](A138684/) | trivial or misstated | Layman's self-similarity conjecture has the wrong peak values; the corrected form holds | [full proof](A138684/A138684_mathlib.lean) | misstated | [greedy-invariant](../methods/greedy-invariant/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A138904](A138904/) | proved | rotational symmetries of a binary expansion | [full proof](A138904/A138904.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A140320](A140320/) | proved | a(n) = 2n\*3^(n-1) + 1 | [full proof](A140320/A140320_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A145878](A145878/) | proved | polynomial formulas for T(r+k, k), r = 3..7 (previous conjectures) | [witness](A145878/A145878.lean) | — | [finite-identity](../methods/finite-identity/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A158110](A158110/) | proved | exp(Σ q^(n^m) x^n/n) is an integer series (known; reproved in Lean) | [full proof](A158110/A158110_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A161579](A161579/) | proved | alternation of odious and evil solutions | [full proof](A161579/A161579_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A161580](A161580/) | proved | alternation for t(n) + t(n+3) = 1 | [full proof](A161579/A161579_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A161817](A161817/) | proved | alternation for t(n) = t(n+5) | [full proof](A161579/A161579_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A161890](A161890/) | proved | alternation for t(n) = t(n+9) | [full proof](A161579/A161579_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A162311](A162311/) | proved | alternation for t(n) = t(n+7) | [full proof](A161579/A161579_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A164848](A164848/) | proved | a(n) = A026741(n)/A051712(n+1) has period 24 | [full proof](A164848/A164848.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A168295](A168295/) | trivial or misstated | "Conjecture: Worpitzky forms" states no claim | — | misstated | [reading-the-statement](../methods/reading-the-statement/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A171871](A171871/) | proved | the last 2^(R-1) entries of column R are binary-code counts (A039754) | [full proof](A171871/A171871_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A171949](A171949/) | proved | P-positions of Mark-4 versus A217319 | [full proof](A217319/A217319.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A173989](A173989/) | proved | 2-adic valuations of A173300 follow A, A, A+1, A with A odd | [full proof](A173989/A173989_mathlib.lean) | known | [exact-arithmetic](../methods/exact-arithmetic/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A177390](A177390/) | disproved | Hanna's "integer triangle for every k" fails at k = 1 (and k = 3) | [witness](A177390/A177390.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A178482](A178482/) | proved | Kimberling's change-of-base conjecture for phi-antipalindromic numbers (known) | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [A178790](A178790/) | proved | integrality and the Apery-sum congruence mod p^2 are both proved (Sun; Wang-Sun) | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [A182484](A182484/) | disproved | the product is a square for p = 63, so "square iff prime" is false | [witness](A182484/A182484.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [A187941](A187941/) | trivial or misstated | a(n) = 2^n exactly for n prime or n = 1 (n ≥ 1); fails literally at n = 0 | [full proof](A187941/A187941_mathlib.lean) | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A192023](A192023/) | trivial or misstated | the determinant-2n matrix count does not match; a linear count does | [full proof](A192023/A192023_mathlib.lean) | misstated | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A193437](A193437/) | proved | p^floor(n/p) divides a(n) for primes p = 1 (mod 3) | — | known | [known-theorem](../methods/known-theorem/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A193438](A193438/) | proved | p^floor(n/p) divides a(n) for primes p = 1 (mod 3), resp. p = 1 (mod 4) | — | known | [known-theorem](../methods/known-theorem/README.md), [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md) |
| [A206912](A206912/) | proved | the differences of A206912 are 1s and 2s | [full proof](A206912/A206912_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A209260](A209260/) | proved | Jeffery's two conjectures (both proved in the entry's references) | — | — | [known-theorem](../methods/known-theorem/README.md) |
| [A209998](A209998/) | misstated | penultimate term of row n equals A199923(n) | [full proof](A209998/A209998_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A212346](A212346/) | proved | a(n) = (n+3)(n^2-4)/6 for n >= 3 | [full proof](A212346/A212346_mathlib.lean) | partly-known | [gf-coefficient-extraction](../methods/gf-coefficient-extraction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A212652](A212652/) | proved | a(n) = min of d + (h-1)/2 over n = d\*h with h odd, and n lies in row a(n) of A209260 | [full proof](A212652/A212652_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [reading-the-statement](../methods/reading-the-statement/README.md) |
| [A212916](A212916/) | proved | standard Young tableaux of height ≤ 10, a(n) ~ 10^n π^(−5) (10/n)^(45/2) ∏ Γ(j/2) | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A213257](A213257/) | proved | the excluded integers are the positions of 2 in a morphic word | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A213258](A213258/) | proved | terms are the positions of 2 in a morphic word (n = 2^(3t+2)·odd) | — | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A213507](A213507/) | proved | a(n) is never divisible by 2, 5, 13, 29, 31, 37, 41, 43, 53, 71, 97 | needs Mathlib | partly-known | [known-theorem](../methods/known-theorem/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A213648](A213648/) | proved | fixed points lie in A000057 | [checked](A213648/A213648_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A214724](A214724/) | proved | p \| a(n) for n >= p when p = m^2 + 1 is prime | — | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A214758](A214758/) | disproved | Coman's midpoint claim for Carmichael numbers is false (46657) | [witness](A214758/A214758_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A215010](A215010/) | disproved | equiangular polygons with sides in arithmetic progression are not only hexagons | [full proof](A215010/A215010_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A215672](A215672/) | disproved | Coman's q((r+1)q − r) claim for Poulet numbers is false (617093) | [witness](A215672/A215672_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A216371](A216371/) | proved | for odd primes with one coach, the top row is a permutation of 1, 3, ..., 2q-1 | [full proof](A216371/A216371_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A217319](A217319/) | proved | the P-positions of Mark-4 are 0 and the numbers with odd 4-adic valuation | [full proof](A217319/A217319.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A218483](A218483/) | proved | Coman's 8pn + p² conjectures are true (form ⇔ P ≡ 1 mod 8) | [full proof](A218483/A218483_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A218755](A218755/) | proved | differences are multiples of 36 | [full proof](A219543/A219543_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A219085](A219085/) | proved | jump points of x^(1/d) form a linear recurrence sequence | [full proof](A219085/A219085_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A219196](A219196/) | proved | a(15) = a(16) = 131070 and a(17..32) = 8589934590 | [full proof](A219196/A219196_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A219543](A219543/) | proved | Bernoulli denominators ≡ 3 or 6 (mod 9) differ by multiples of 36 | [full proof](A219543/A219543_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A220956](A220956/) | disproved | "a(n) = 0 iff n is an odd prime" is false; n = 16843² = 283686649 is a composite zero | [full proof](A220956/A220956_mathlib.lean) | partly-known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A221564](A221564/) | proved | a(3k+1) = 2k for the FO4C3 shuffle | [full proof](A221564/A221564_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A223577](A223577/) | proved | A223578(n) = 2·A223577(n) − n + 1 | [full proof](A223577/A223577_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A223578](A223578/) | proved | A223578(k) = 2·A223577(k) − k + 1 | [full proof](A223577/A223577_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [nth-enumeration](../methods/nth-enumeration/README.md) |
| [A223925](A223925/) | proved | a(2n) = 4^n divides A132049(2n) | needs Mathlib | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A224529](A224529/) | proved | a(np) ≡ a(n) mod p for (p/23) = 1 (proved by Osburn and Sahu) | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A225003](A225003/) | proved | a(n) = A047332(n) for n ≥ 2 | [full proof](A225003/A225003_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A225611](A225611/) | proved | Sun's Legendre-symbol determinant vanishes on a residue class | [full proof](A228095/A225611_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A226160](A226160/) | proved | a(n+1)/a(n) → exp(1/φ) = 1.855276958... (harmonic-number threshold) | [full proof](A226160/A226160_mathlib.lean) | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A226163](A226163/) | proved | Sun's Legendre-symbol determinant vanishes on a residue class | — | known | [known-theorem](../methods/known-theorem/README.md) |
| [A226187](A226187/) | proved | a(n+1)/a(n) → exp(1/3) | [full proof](A226187/A226187_mathlib.lean) | known | [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A226188](A226188/) | proved | a(n+1)/a(n) → exp(2/3) = 1.947734... (harmonic-number threshold) | [full proof](A226188/A226188_mathlib.lean) | — | [elementary-proof](../methods/elementary-proof/README.md) |
| [A227145](A227145/) | proved | a(F\_n) = F\_(n-2) | [full proof](A227145/A227145_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A227609](A227609/) | proved | OEIS A227609 | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A227781](A227781/) | proved | a(n) = 4 iff 8 \| n, a(n) = 3 iff n = 4 mod 8 | [full proof](A227784/A227784_mathlib.lean) | known | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A227784](A227784/) | misstated | -1 as a sum of fourth powers / squares mod n | [full proof](A227784/A227784_mathlib.lean) | partly-known | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [A227968](A227968/) | proved | OEIS A227968 | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A227971](A227971/) | proved | OEIS A227971 | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A228005](A228005/) | proved | OEIS A228005 | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A228304](A228304/) | proved | OEIS A228304 | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A229068](A229068/) | proved | standard Young tableaux of height ≤ 12, a(n) ~ 12^n π^(−6) (12/n)^33 ∏ Γ(j/2) | — | known | [known-theorem](../methods/known-theorem/README.md), [exact-arithmetic](../methods/exact-arithmetic/README.md) |
| [A229136](A229136/) | proved | a(n) = A131885(n) \* 2^(n-1) (proved in the entry, reproved in Lean) | [full proof](A229136/A229136_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [A230168](A230168/) | proved | every prime 45·2^n − 1 ends in 9 | [full proof](A230168/A230168_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [lean-certificate](../methods/lean-certificate/README.md) |

## Disputed or only partly answered (not counted as resolutions)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A029766](A029766/) | partial | a(n) = n!·A040039(n−1) holds on the data; the entry's name does not determine the sequence | [full proof](A029766/A029766_mathlib.lean) | new (immediate) | [reading-the-statement](../methods/reading-the-statement/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A123365](A123365/) | partial | cubes mod n, partial result (two prime factors) | [checked](A123365/A123365_mathlib.lean) | new | [multiplicative-local-bounds](../methods/multiplicative-local-bounds/README.md), [elementary-proof](../methods/elementary-proof/README.md) |

## Bounds improved (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A010101](A010101/) | bound improved | a(10) ≤ 116 (upper bound improved from 117) | — | new | [interval-layer-lp](../methods/interval-layer-lp/README.md) |

## Weaker results on open problems (the problem stays open)

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [A002383](A002383/) | partial | A002383 \ {3} = A085104 ∩ A059055 (open; inclusion ⊆ proved) | [checked](A007645/A007645_mathlib.lean) | new | [reading-the-statement](../methods/reading-the-statement/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A054979](A054979/) | partial | "every e-perfect number is divisible by 36" is equivalent to the open Straus-Subbarao question | — | partly-known | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A073117](A073117/) | partial | Cloitre's eventual-increment conjecture (partial: listed values confirmed) | [full proof](A073117/A073117.lean) | partly-known | [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md), [lean-certificate](../methods/lean-certificate/README.md) |
| [A094358](A094358/) | partial | Munafo's conjecture is equivalent to "all Fermat numbers are squarefree" | [full proof](A094358/A094358_mathlib.lean) | known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [A139250](A139250/) | partial | holes of the toothpick structure are rectangles (side lengths still open) | — | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A213381](A213381/) | partial | n^n mod (n+2) — zeros and the A176003 values (parts 3–4 open) | [full proof](A213381/A213381_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [A215926](A215926/) | partial | the power-of-2 conjectures reduce to almost perfect numbers | [witness](A215926/A215926_mathlib.lean) | new | [reduction-to-constant](../methods/reduction-to-constant/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [A219033](A219033/) | partial | the sequence is infinite; the 6\*A185208(n) ratio conjecture is false | [full proof](A219033/A219033_mathlib.lean) | new | [parametric-family](../methods/parametric-family/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [A227012](A227012/) | partial | the case g(n) = n^3, f(k) = 1/k | — | new | [exact-arithmetic](../methods/exact-arithmetic/README.md), [recurrence-asymptotics](../methods/recurrence-asymptotics/README.md) |

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

### [A008749](A008749/): a(n+2) is the first index where the minimal polyiamond perimeter reaches n + 4

**Source.** [A008749](https://oeis.org/A008749) (offset 0): expansion of (1+x^6)/((1-x)(1-x^2)(1-x^3)). Comment by
Winston C. Yang (Feb 05 2002): "Conjecture: For n >= 1, A067628(a(n+2)) appears for the first time in A067628."
[A067628](https://oeis.org/A067628) is the minimal perimeter of a polyiamond with T triangles; its FORMULA section
gives the Harary-Harborth (1976) value 2*ceiling((T + sqrt(6T))/2) - T. (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Reading.** "A067628(a(n+2)) appears for the first time" at index a(n+2): no T < a(n+2) has the same A067628
value. The entry's second sentence ("is the first T such that ... is a(n+2)") mixes index and value; the reading
proved here is the stronger one: A067628(a(n+2)) = n + 4 and a(n+2) is the least T with A067628(T) = n + 4.

**Result.** True for every n >= 1, given the Harary-Harborth formula.

**Argument.** Write p(T) = 2*ceil((T + sqrt(6T))/2) - T. For T >= 1 and v >= 2, p(T) = v iff v ≡ T (mod 2) and
v - 2 < sqrt(6T) <= v, i.e. (v-2)^2 < 6T <= v^2. Multiplying the g.f. out gives a(n+6) = a(n+5) + a(n+4) -
a(n+2) - a(n+1) + a(n) + [n = 0], and by induction 6 a(N) = N^2 + e(N mod 6) with e = 12, 5, 8, 9, 8, 5, and
a(N) ≡ N (mod 2), for N >= 1. Put N = n + 2 >= 3, A = a(N), v = n + 4 = N + 2. Then v ≡ A (mod 2),
(v-2)^2 = N^2 < 6A and 6A <= N^2 + 12 <= (N+2)^2, so p(A) = v. If T < A and p(T) = v, then T ≡ v ≡ A (mod 2),
so T <= A - 2 and 6T <= N^2 + e - 12 <= N^2 = (v-2)^2, a contradiction (T = 0 has p(0) = 0).

Lean: [full proof](A008749/A008749_mathlib.lean).

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

### [A036284](A036284/): OEIS A036284

Lean: [full proof](A037097/A037097_mathlib.lean).

### [A037096](A037096/): OEIS A037096

Lean: [full proof](A037097/A037097_mathlib.lean).

### [A037097](A037097/): (x+1)- and (x^3+1)-power factors of periodic binary columns

**Source.** Antti Karttunen's entries (OEIS text, CC BY-SA 4.0, checked 2026-11-06):
- [A037097](https://oeis.org/A037097): periodic vertical binary vectors of powers of 3, starting from bit column 2
  (halved), a(n) = Sum_{k=0..2^(n-1)-1} (floor(3^k/2^n) mod 2) 2^k. Comment, as corrected by Qiyuan Gu (Jul 24 2026):
  for n >= 3, a(n) as a GF(2)[X] polynomial is divisible by (x+1)^A000225(n-2). The scan record quotes the older
  exponent A000225(n-1).
- [A037096](https://oeis.org/A037096): the same over k < 2^n; conjecture: (x+1)^A055010(n-1) divides a(n), n >= 3.
- [A036284](https://oeis.org/A036284): periodic vertical binary vectors of Fibonacci numbers, k < 3*2^n; conjecture:
  (x^3+1)^A000225(n-1) divides a(n) for n >= 1; "Conjecture 2: there is also one extra (x^1 + 1) factor present".

**Reading.** "a(n) considered as a GF(2)[X]-polynomial": binary digit k of a(n) is the coefficient of x^k, so
a(n) is Sum_k bit_n(f(k)) x^k with f(k) = 3^k or F_k. A000225(j) = 2^j - 1, A055010(n-1) = 3*2^(n-2) - 1.

**Result.** - A037097: the corrected statement is true, with exact exponent 2^(n-2) - 1. The older exponent 2^(n-1) - 1 (the
  scan record's version) is false: a(3) = 12 = x^2 + x^3 = x^2 (x+1) and a(4) = 120 = x^3 (x+1)^3.
- A037096: true.
- A036284: both conjectures true.

**Argument.** Bit flips. For n >= 3, 3^(2^(n-2)) = 1 + 2^n u with u odd (induction by squaring), so
3^(k+M) = 3^k + 2^n (3^k u) and bit n of 3^k flips when k grows by M = 2^(n-2). For the Fibonacci numbers and
n >= 2, L = 3*2^(n-1) gives F_L = 2^(n+1) * odd and F_(L-1) = 1 + 2^n (mod 2^(n+1)) (induction with
F_2L = F_L (2F_(L+1) - F_L) and F_(2L-1) = F_L^2 + F_(L-1)^2), so F_(k+L) = F_k F_(L-1) + F_(k+1) F_L flips bit n
exactly when F_k is odd, i.e. 3 does not divide k.
Polynomials. If q_(k+M) = q_k + c_k then Sum_{k<2M} q_k x^k = A (1 + x^M) + x^M Sum_{k<M} c_k x^k with
A = Sum_{k<M} q_k x^k. Over GF(2), 1 + x^(2^j) = (1+x)^(2^j) and Sum_{k<2^j} y^k = (1+y)^(2^j - 1).
- A037097 (c = 1): a(n) = A (1+x)^M + x^M (1+x)^(M-1) = (1+x)^(M-1) (A(1+x) + x^M); the cofactor is 1 at x = 1.
- A037096: bit n has period 2^(n-1), so A037096(n) = A037097(n) (1+x)^(2^(n-1)), exponent 3*2^(n-2) - 1.
- A036284 (c_k = 1 iff 3 does not divide k, N = 2^(n-1)): Sum_{k<L} c_k x^k = (x + x^2)(1+x^3)^(N-1), so
  a(n) = A (1+x^3)^N + x^(L+1)(1+x)(1+x^3)^(N-1) = (1+x^3)^(N-1) (1+x) (A(1+x+x^2) + x^(L+1)).
  n = 1 directly: a(1) = x^3 + x^4.

Lean: [full proof](A037097/A037097_mathlib.lean).

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

### [A054096](A054096/): column 2 of A054090 is A006183 shifted right

**Source.** [A054096](https://oeis.org/A054096) (offset 2), "T(n,2), array T as in A054090", comment by
Ralf Stephan (Jan 15 2004): "Conjecture: sequence is A006183 shifted right." Array
[A054090](https://oeis.org/A054090): "T(n,0) = 1 for n >= 0, T(n,1) = r(n-1), T(n,k) = T(n,k-1) -
(-1)^k * r(n-k) for k = 2, 3, ..., n, n >= 2, r(h) = sum of the numbers in row h of T."
[A006183](https://oeis.org/A006183) (offset 1): "a(n) = (n+1)*a(n-1) + (2-n)*a(n-2)", data 1, 2, 6,
22, 98, ... (OEIS text, CC BY-SA 4.0; A054096 revision #6, A054090 #16, A006183 #33, checked
2026-11-06.)

**Reading.** The recurrence in the name of A006183 is written for a[0] = 1, a[1] = 2 (the entry's
Mathematica program); with the entry's offset 1 it reads a(1) = 1, a(2) = 2, a(n) = n a(n-1) +
(3-n) a(n-2) (the entry's Magma program), which reproduces the data. "Shifted right" means
A054096(n) = A006183(n-1) for n >= 2, which matches all 18 data terms.

**Result.** True: A054096(n) = A006183(n-1) for every n >= 2.

**Argument.** Write r(h) for the row sums.
1. For 2 <= k <= m+1: T(m+1,k) + T(m,k-1) = r(m). For k = 2 both sides equal T(m+1,1) = r(m)
   (the r(m-1) terms cancel); going from k to k+1 adds -(-1)^(k+1) r(m-k) - (-1)^k r(m-k) = 0.
2. Summing row m+1: r(m+1) = 1 + r(m) + sum_{k=2}^{m+1} (r(m) - T(m,k-1)) = 1 + r(m) + m r(m) -
   (r(m) - 1) = m r(m) + 2. (This recurrence for A054091 is stated in that entry by G. Detlefs, 2010,
   without proof.)
3. T(m+2,2) = T(m+2,1) - r(m) = r(m+1) - r(m). With b(m) = r(m+1) - r(m) we get b(0) = 1, b(1) = 2,
   and step 2 gives b(m+2) = (m+3) b(m+1) - m b(m) (the difference of the two sides is
   [r(m+3) - (m+2)r(m+2) - 2] - 2[r(m+2) - (m+1)r(m+1) - 2] + [r(m+1) - m r(m) - 2] = 0). This is the
   recurrence of A006183 at index m+3, so b(m) = A006183(m+1), i.e. A054096(n) = A006183(n-1).

Lean: [full proof](A054096/A054096_mathlib.lean).

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

### [A054656](A054656/): for n >= 23, a(n) = [n-6 prime] + [n-4 prime] + [n-1 prime]

**Source.** [A054656](https://oeis.org/A054656) (offset 0, Henry Bottomley, Apr 17 2000): "Number of primes <= n
which do not appear in any partitions of n into distinct primes." Comment in the entry: "Conjecture: if n >= 23
then a(n)=2 if both (n-6) and (n-4) are prime, a(n)=1 if one of (n-6), (n-4) or (n-1) is prime, a(n)=0
otherwise". (OEIS text, CC BY-SA 4.0, revision #8 of Feb 15 2022, checked 2026-11-06.)

**Result.** True for every n >= 23. The bound is sharp: a(22) = 1 (the prime 11) while the formula gives 0.

**Argument.** A prime p <= n is a part of some partition of n into distinct primes iff m = n - p is a sum of
distinct primes none equal to p ("m avoids p").

1. *Two primes in (x, 2x] for x >= 6.* For x >= 512 this is the Erdős proof of Bertrand's postulate with one extra
   factor: if q is the only prime in (x, 2x], then centralBinom x <= (2x)^sqrt(2x) 4^(2x/3) (2x), since q^v_q <= 2x;
   with 4^x < x centralBinom x this contradicts x (2x) (2x)^sqrt(2x) 4^(2x/3) <= 4^x, which holds for x >= 512
   (f(x) = 2 log x + log 2 + sqrt(2x) log(2x) - (log 4 / 3) x is concave, f(18) >= 0, f(512) <= 0). For
   6 <= x < 512 the chain 523, 521, 269, 263, 139, 137, 73, 71, 41, 37, 29, 23, 19, 17, 13, 11, 7 (each term at
   most twice the term two places later) gives two primes, and x = 6 has 7, 11. So for any p, (x, 2x] holds a
   prime other than p.
2. *Richert-type induction.* Claim: if m > 27, r >= 31 and m <= 27 + r, then m is a sum of distinct primes, all
   below r and none equal to p. For m <= 87 an explicit table gives two or three representations with parts below
   max(31, m - 27) and no part common to all of them, so one avoids p. For m >= 88 take x = (m - 28)/2 >= 30 and a
   prime q != p in (x, 2x] (step 1); then 27 < m - q <= 27 + q and q >= 31, so by induction m - q is a sum of
   distinct primes below q avoiding p; add q (and q < r because q <= m - 28).
3. *All m.* With r = m + 31, every m > 27 avoids every p. For m <= 27 the table shows that m avoids p unless m is
   1, 4 or 6 (no representation at all) or (m, p) is one of (2,2), (3,3), (8,3), (8,5), (9,2), (9,7), (10,3),
   (11,11), (12,7). In each of these pairs m + p <= 22.
4. *Count.* For n >= 23 the prime p <= n is missing from every partition iff n - p is 1, 4 or 6, so
   a(n) = [n-1 prime] + [n-4 prime] + [n-6 prime]. For n >= 23, n-1 is never prime together with n-4 or n-6 (one of
   the two is even and larger than 2), which gives the three cases of the conjecture.

Lean: [full proof](A054656/A054656_mathlib.lean).

### [A056142](A056142/): a(n) palindrome only if all digits of n are equal

**Source.** [A056142](https://oeis.org/A056142), Henry Bottomley, Jun 15 2000: "Concatenate n, floor[n/10],
floor[n/100] ... (but do not continue if floor[.]=0)." Comments: D. Wasserman (May 23 2005) states that for
3-digit n, a(n) is a palindrome iff n is, and for 4 or 5 digits iff all digits of n are equal; F. T. Adams-Watters
(Sep 07 2006) conjectures "if n has 3 or more digits, a(n) is a palindrome only if all the digits of n are the
same" and notes that such a palindrome uses at most 2 distinct digits. (OEIS text, CC BY-SA 4.0, revision #9 of
Jul 11 2020, checked 2026-11-06.)

**Reading.** Palindrome means the decimal string reads the same backwards (`Nat.digits 10 m` equals its reverse).
The words "3 or more" conflict with Wasserman's 3-digit comment; the intended range is 4 or more digits.

**Result.** As stated the conjecture is false: n = 101 has 3 digits and a(101) = 101101 is a palindrome (every
3-digit palindrome n is a counterexample, as Wasserman's comment already implies). For 4 or more digits it is
true: if n has d >= 4 digits, a(n) is a palindrome iff all digits of n are equal.

**Argument.** Write n = x_1 ... x_d, u_k = x_1 ... x_k and T(k) = k(k+1)/2. Then a(n) is the word
w = u_d u_(d-1) ... u_1 of length T(d), and its reverse is rev(u_1) rev(u_2) ... rev(u_d).

1. *Reduction.* If w is a palindrome, its first d letters equal those of the reverse, so for 3 <= i <= d,
   x_i = x_(T(m)+1-i) where T(m-1) < i <= T(m); the index on the right is smaller than i. Hence x is determined
   by x_1, x_2: x_i = phi(X_i), where X is the word over {a, b} with X_1 = a, X_2 = b and X_p = X_(T(m)+1-p) for
   T(m-1) < p <= T(m), and phi(a) = x_1, phi(b) = x_2. If x_1 = x_2 all digits are equal. Otherwise phi is
   injective, and the word for X_1 ... X_d must itself be a palindrome. X begins abaabaaababaab...
2. *Palindrome gives a near-square.* For the word of X_1 ... X_d the reverse is X_1 ... X_T(d) (block m of X,
   positions T(m-1)+1 .. T(m), is X_m ... X_1). Positions d+1 .. 2d-1 of w hold u_(d-1) = X_1 ... X_(d-1), so a
   palindrome gives S(d): X_(d+i) = X_i for 1 <= i <= d-1.
3. *S(r) fails for every r >= 4*, by strong induction. For r <= 105 by direct computation. For r >= 106 let K be
   such that T(K-1) < r <= T(K); block K+1 of X (positions T(K)+1 .. T(K+1)) lies in r+1 .. 2r-1. Set
   e = T(K+1) - r, so K+1 <= e <= 2K. Block K+1 is X_(K+1) ... X_1, and S(r) moves it to positions e-K .. e:
   X_t = X_(e+1-t) for 1 <= t <= K+1. Let T(k) <= e < T(k+1) and o = e - T(k), 0 <= o <= k; then
   5 <= k and 2k <= K+1. Reading block k (or block k-1 when o = 0) of X inside this mirrored copy gives
   X_t = X_(t-o) for o+1 <= t <= o+k (and X_t = X_(t-k) for k+1 <= t <= 2k-1 when o = 0). If o = 0 this is S(k);
   if o >= 4 it contains S(o); both have 4 <= index < r, contradicting the induction hypothesis. If o = 1, 2, 3 it
   gives X_2 = X_1, X_4 = X_2 or X_8 = X_5, all false (X_1 ... X_8 = abaabaaa).
4. Conversely, if all digits are equal, a(n) is a string of one repeated digit.

Lean: [full proof](A056142/A056142_mathlib.lean).

### [A058347](A058347/): the double-support check counts are symmetric, T(n,k) = T(k,n)

**Source.** [A058347](https://oeis.org/A058347) (M. R. C. van Dongen, 2000): "Array T(n,k), n,k nonnegative: the
total number of checks required by a "double-support" algorithm to find out which rows and columns of each of the
n by k zero-one matrices are nonzero." Comment: "Conjecture: T(n,k) = T(k,n)." Formula line: T(0,k) = T(n,0) = 0,
T(n,k) = (2^(k+1) - 2)2^((n-1)k) + 2^((n-1)(k-1))((k-2)2^k + 2) + (n-1)(2^k - 1)2^((n-2)k+1) + T(n-1,k)
+ 2^(n-1)(2^k - 1)T(n-1,k-1) for n, k > 0. (OEIS text, revision #12 of Aug 04 2022, checked 2026-11-06.)

**Reading.** The algorithm is specified in van Dongen's technical report; the entry's data are generated by the
formula line, so T is taken to be defined by that recurrence. For n = 1 the third term is 0.

**Result.** True. With S(n,k) = Σ_M rank(M), the sum of the GF(2)-ranks of all n x k 0-1 matrices,
T(n,k) = 2^(nk)(2n + 2k − n·2^(1−k) − k·2^(1−n)) − 2 S(n,k), and both parts are symmetric (rank(Mᵀ) = rank(M)).
Equivalently the expected number of checks is 2n + 2k − n·2^(1−k) − k·2^(1−n) − 2·E[rank].

**Argument.** 1. *Rank sums.* Condition on the first row r of M. If r = 0 (one choice), rank(M) is the rank of the other n−1
   rows. If r ≠ 0 (2^k − 1 choices), rank(M) = 1 + rank of the other rows modulo r, and modulo r those rows are
   uniform in GF(2)^k/⟨r⟩ ≅ GF(2)^(k−1), each image hit 2^(n−1) times. So
   S(n,k) = S(n−1,k) + (2^k − 1)(2^((n−1)k) + 2^(n−1) S(n−1,k−1)), S(0,k) = S(n,0) = 0.
2. *Symmetry of S without linear algebra.* By induction on n, S also satisfies the column recurrence
   S(n,k) = S(n,k−1) + (2^n − 1)(2^(n(k−1)) + 2^(k−1) S(n−1,k−1)); the step is the linear combination
   r1 + c1 − r2 + (2q − 4pq)·rX + (4pq − 2p)·cX of two row and two column instances (p = 2^n, q = 2^k).
   Then S(n,k) = S(k,n) by induction on n + k.
3. *Closed form.* C(n,k) = 2^(nk)(2n + 2k) − n·2^((n−1)k+1) − k·2^(n(k−1)+1) is symmetric, and C − 2S satisfies
   the recurrence of T with the same boundary values (a polynomial identity in 2^n, 2^k, 2^(nk), n, k). Hence
   T = C − 2S and T(n,k) = T(k,n).

The closed form was found by fitting T(n,k)/2^(nk) for fixed k (linear in n plus a polynomial in 2^(−n)) and
recognising the remainder as k − E[rank].

Lean: [full proof](A058347/A058347_mathlib.lean).

### [A059970](A059970/): nim-factorials of 2^n - 1 and 2^n + 2^(n-1) - 1

**Source.** [A059970](https://oeis.org/A059970) (John W. Layman, 2001): nim-factorials, a(1) = 1, a(n) = n ⊗ a(n-1)
(⊗ nim multiplication). "Conjectures: (1) Nim-Factorial(2^n-1)=1 (verified for n=1,2,3,...,16). (2)
Nim-Factorial(2^n+2^(n-1)-1)=2 (verified for n=1,2,3,...,15)." (OEIS text, revision #19 of Mar 24 2025, checked
2026-11-06.)

**Result.** Both are true for every n >= 1.

**Argument.** Standard facts (Conway, *On Numbers and Games*, ch. 6; Lenstra, "Nim multiplication"): F_k = [0, 2^(2^k))
is a subfield of the nimbers of size q_k = 2^(2^k); x_k = 2^(2^k) satisfies x_k ⊗ x_k = x_k ⊕ α_k with
α_k = 2^(2^k - 1) = x_0 ⊗ ... ⊗ x_(k-1) ∈ F_k; and a ⊕ (b ⊗ x_k) = a + b·2^(2^k) for a, b ∈ F_k, so
[0, 2^(2^k + j)) = F_k ⊕ [0, 2^j) ⊗ x_k. The Frobenius t ↦ t^(q_k) of F_(k+1) over F_k maps x_k to the other root
x_k ⊕ 1, so x_k^(q_k) ⊕ x_k = 1. For W ⊆ F_k and b ∈ F_k, b ≠ 0: Π_{a∈F_k} (a ⊕ b x_k) = b^(q_k) Π_c (x_k ⊕ c) =
b (x_k^(q_k) ⊕ x_k) = b.
1. *Claim (1).* Let P(V) be the nim product of the nonzero elements of V. For V = F_k ⊕ W x_k the elements with b = 0
   give P(F_k) = 1 (Wilson in a field of characteristic 2) and the rest give Π_{b∈W, b≠0} b, so P(V) = P(W). Hence
   P([0, 2^(2^k + j))) = P([0, 2^j)) and by induction P([0, 2^n)) = 1 = a(2^n - 1).
2. *Claim (2).* a(2^n + 2^(n-1) - 1) = P([0, 2^n)) ⊗ y(n) with y(n) = Π_{c < 2^(n-1)} (2^n ⊕ c). For n = 2^k + j with
   1 <= j < 2^k, the same computation gives y(n) = y(j). For n = 2^k (k >= 1) write F' = F_(k-1), x' = x_(k-1),
   m = 2^(k-1), W = [0, 2^(m-1)); then y(2^k) = Π_{w∈W} (s ⊕ w) = L_W(s) with s = x_k^(2^m) ⊕ x_k, while
   y(2^(k-1)) = L_W(x'), where L_W(t) = Π_{w∈W}(t ⊕ w) is additive. Since x_k^(2^l) = x_k ⊕ Σ_{i<l} α_k^(2^i) and
   α_k = x' ⊗ α', with α' = α_(k-1): s = x' ⊗ Tr(α') ⊕ e_2, where Tr(α') = Σ_{l<m} α'^(2^l) = 1 (t^2 + t + α' is
   irreducible over F') and e_2 = Σ_{i<l<m} α'^(2^i + 2^l) is fixed by Frobenius, so e_2 ∈ {0, 1} ⊆ W (k >= 2; for
   k = 1, e_2 = 0). Hence y(2^k) = y(2^(k-1)) = ... = y(1) = 2 and a(2^n + 2^(n-1) - 1) = 2.

Lean: needs Mathlib.

### [A061002](A061002/): denominator(H(p)/H(p−1)) / numerator(H(p−1)/p^2) = p^3

**Source.** [A061002](https://oeis.org/A061002), comment by G. Detlefs (2013): "Conjecture: If p is the n-th
prime and H(n) is the n-th harmonic number, then denominator(H(p)/H(p-1))/numerator(H(p-1)/p^2) = p^3.
A193758(p)/a(n) = p^3, p > 3." (OEIS text, CC BY-SA 4.0.)

**Result.** True for all primes p ≥ 5.

**Argument.** Write H(p−1) = a/b in lowest terms. Wolstenholme: p^2 | a; also p ∤ b. Then
H(p)/H(p−1) = 1 + b/(pa) = (pa + b)/(pa), and gcd(pa + b, p) = gcd(b, p) = 1, gcd(pa + b, a) = gcd(b, a) = 1,
so the denominator is pa. H(p−1)/p^2 = (a/p^2)/b in lowest terms, numerator a/p^2. Ratio pa/(a/p^2) = p^3.

Lean: [full proof](A061002/A061002_mathlib.lean).

### [A065558](A065558/): a(2n) = 2 psi(n) (maximal irreducible degree of GL_2(Z/2nZ))

**Source.** [A065558](https://oeis.org/A065558): a(n) is the maximal degree of an irreducible complex representation of
G_n = GL_2(Z/nZ). The entry notes that a is multiplicative and a(p) = p + 1 for odd primes p. Conjecture (Ralf
Stephan, Mar 26 2004): a(2n) = 2*A001615(n), with A001615 the Dedekind psi function psi(n) = n prod_{p | n} (1 + 1/p).
Data: n = 1..24. (OEIS text, checked 2026-11-06.)

**Result.** True. Precisely: a(p^r) = p^(r-1)(p+1) for every prime power p^r except a(2) = 2, so a(n) = psi(n) for
odd n, and a(2n) = 2 psi(n) for all n >= 1.

**Argument.** 1. Multiplicativity: G_(mn) = G_m x G_n for coprime m, n (CRT), and irreducibles of a direct product are tensor
   products, so maximal degrees multiply.
2. Odd p: the irreducible representations of GL_2(Z/p^r) (p odd) are known (Nagornyi 1976; also Kutzko, Stasinski
   arXiv:0807.4684): twists of representations of GL_2(Z/p^(r-1)) and new ones of degrees p^(r-1)(p+1),
   p^(r-1)(p-1), p^(r-2)(p^2-1). Hence a(p^r) = p^(r-1)(p+1).
3. p = 2, r >= 2: a(2^r) = 3 * 2^(r-1). Let G = GL_2(Z/2^r), K_j = 1 + 2^j M_2 (mod 2^r), l = ceil(r/2), N = K_l
   (abelian). Characters of N are psi_beta(1 + 2^l x) = exp(2 pi i tr(beta x)/2^(r-l)), beta in M_2(Z/2^(r-l)),
   permuted by conjugation. For an irreducible pi containing psi_beta, Clifford theory gives
   dim pi = [G : G_beta] dim sigma, with G_beta the stabiliser and sigma an irreducible of G_beta over psi_beta.
   - beta scalar mod 2 (beta = a + 2 beta'): psi_(aI) = chi(det) on N for a character chi of (Z/2^r)^*
     (det(1 + 2^l x) = 1 + 2^l tr x mod 2^r), so pi (x) chi(det)^(-1) is trivial on K_(r-1) and has the degree of an
     irreducible of GL_2(Z/2^(r-1)): at most max(2, 3 * 2^(r-2)) by induction.
   - beta not scalar mod 2: beta-bar is cyclic, its centraliser is F_2[beta-bar], and G_beta = C K_(r-l) with
     C = (Z/2^r[beta~])^*, beta~ a lift. With |G| = 3 * 2^(4r-3) and |C| = 2^(2r-2), 3 * 2^(2r-2), 2^(2r-1) in the
     split (char. poly x(x+1)), irreducible (x^2+x+1) and nilpotent (x^2 or (x+1)^2) cases,
     [G : G_beta] = 3 * 2^(2r-1-2l), 2^(2r-1-2l), 3 * 2^(2r-2-2l).
     psi_beta extends to a linear character Theta of M = C K_l (C abelian and stabilises psi_beta), so every sigma
     lies in Ind_M^(G_beta) Theta' and dim sigma <= [G_beta : M], which is 1 for r even and 4 for r odd.
     r even: dim pi = [G : G_beta] <= 3 * 2^(r-1). r odd (r >= 3): irreducible case <= 2^(r-2) * 4 = 2^r, nilpotent
     case <= 3 * 2^(r-3) * 4 = 3 * 2^(r-1); split case: C = 1 + 2 Z[beta~] (units of Z/2^r x Z/2^r are odd), so with
     j = 1 + 2^(l-1) x and c = 1 + 2u, c^(-1) j c j^(-1) = 1 + 2^l c^(-1)[x, u] mod 2^r and
     tr(beta c^(-1) [x, u]) = 0 because beta, c, u commute. Hence M is normal in G_beta, every extension Theta is
     G_beta-stable, G_beta/M is (Z/2)^2, and Theta([j1, j2]) = (-1)^tr(beta-bar [x1, x2]) is a non-degenerate
     commutator form on it; so sigma is unique of degree 2 and dim pi = 3 * 2^(r-2) * 2 = 3 * 2^(r-1).
   - Lower bound: split beta-bar = diag(0, 1) gives degree exactly 3 * 2^(r-1) (r even: dim sigma = 1; r odd: 2).
   So a(2^r) = 3 * 2^(r-1) = psi(2^r) for r >= 2, and a(2) = 2 (GL_2(F_2) = S_3).
4. For n = 2^j m, m odd: a(2n) = a(2^(j+1)) a(m) = 3 * 2^j psi(m) = 2 psi(2^j) psi(m) = 2 psi(n) for j >= 1, and
   a(2m) = 2 psi(m) for j = 0.

Lean: —.

### [A068991](A068991/): squarefree members k divide the denominator of B_{2k}

**Source.** [A068991](https://oeis.org/A068991) (Benoit Cloitre, Apr 06 2002): "Numbers k such that
Sum_{d divides k} sigma(d)/phi(d) is an integer." Comment: "Conjecture: if k is in the sequence and k is
squarefree then the denominator of the 2k-th Bernoulli's number contains k." (OEIS text, CC BY-SA 4.0,
revision #35 of Sep 08 2022, checked 2026-11-06.)

**Reading.** "Contains k" means k divides the denominator of B_{2k} (the entry's example uses A002445(2310),
the denominator of B_{4620}).

**Result.** True.

**Argument.** For squarefree k with prime set P, multiplicativity gives
f(k) = Sum_{d|k} σ(d)/φ(d) = Π_{p∈P} 2p/(p−1) = 2^|P| k / D, with D = Π(p−1). By von Staudt–Clausen, k divides
den(B_{2k}) iff (p−1) | 2k for all p ∈ P. Remove the largest prime M of k, k = k'M. Since M divides neither D(k')
nor M−1, the integer F = f(k) is a multiple of M, and k' is again a member, with precisely
F·h = M·F(k') where M = 2h+1 (M = 2 forces k = 2). Induction on the number of prime factors carries three facts:
(i) (p−1) | 2k for every p | k; (ii) k odd ⇒ F odd; (iii) 4 | F ⇒ (k, F) ∈ {(2, 4), (6, 12), (42, 28)}.
For (i) at M one needs h | k' with h | F(k'): write h = 2^a u, u odd; u | k' because F(k') | 2^n k'; a = 0 if k'
is odd (F(k') odd by (ii)); a ≤ 1 ≤ v2(k') if k' is even and 4 ∤ F(k'); otherwise (iii) leaves three explicit
cases, checked by listing the divisors h of 4, 12, 28 with 2h+1 prime. (ii) and (iii) follow from F·h = M·F(k')
in the same way (in (iii), M = 3 for k' = 2, M = 7 for k' = 6, none for k' = 42).

Lean: [full proof](A068991/A068991_mathlib.lean).

### [A069187](A069187/): core(k) = ⌈√k⌉ exactly for k = 1 and k = n²(n²+1) with n²+1 squarefree

**Source.** [A069187](https://oeis.org/A069187), numbers k with core(k) = ⌈√k⌉ (core = squarefree part).
Comment by R. Stephan (Aug 18 2004): "Conjecture: sequence is A071253 minus those entries of A071253 that have
their index in A049532, i.e., a(n) is of form n^2*(n^2+1) for all n not in A049532." (OEIS text, CC BY-SA 4.0,
read 2026-11-06.) A071253(n) = n²(n²+1) (offset 0); A049532 = n with n²+1 not squarefree.

**Result.** True, with one correction at the start: the terms are 1 and the n²(n²+1) with n ≥ 1 and n²+1
squarefree. A071253(0) = 0 is not a term and 1 is not in A071253.

**Argument.** Write k = b²a with a squarefree; then core(k) = a. ⌈√k⌉ = a means (a−1)² < b²a ≤ a². The right
inequality gives b² ≤ a. If a ≥ b² + 2 then b²a ≤ (a−2)a < (a−1)², a contradiction. So a = b² (squarefree forces
b = 1, k = 1) or a = b² + 1 (k = b²(b²+1) with b²+1 squarefree). Conversely both kinds satisfy the inequalities.

Lean: [full proof](A069187/A069187_mathlib.lean).

### [A072901](A072901/): composites with disc Q(√n) = 4n are squarefree

**Source.** [A072901](https://oeis.org/A072901) (composite n with discriminant of Q(√n) equal to 4n),
comment by V. Librandi and M. Marcus: "Conjecture: All terms are squarefree." (OEIS text, CC BY-SA 4.0.)

**Result.** True; trivial.

**Argument.** Write n = d·s^2 with d squarefree (d > 1, as n is not a square). Q(√n) = Q(√d) has
discriminant d (d ≡ 1 mod 4) or 4d (d ≡ 2, 3 mod 4), at most 4d. If s ≥ 2 this is < 4n. So
discriminant 4n forces s = 1 (and n ≡ 2, 3 mod 4).

Lean: [full proof](A072901/A072901_mathlib.lean).

### [A072939](A072939/): c(k) → ∞ exactly when n − 1 has odd 2-adic valuation, so a(n) = A036554(n) + 1

**Source.** OEIS [A072939](https://oeis.org/A072939) (B. Cloitre, 2002): c(1) = 1, c(2) = n,
c(k+2) = (c(k+1) + c(k))/2 if c(k+1), c(k) have the same parity, otherwise |c(k+1) − 2c(k)|; the sequence lists
the n with lim c(k) = ∞. Comment: "Conjecture: a(n) = A036554(n)+1." (V. Jovovic, Apr 01 2003). A036554 lists
the numbers whose binary expansion ends in an odd number of zeros. (OEIS text, CC BY-SA 4.0, revision #32 of
Apr 22 2025; a later comment by R. Stephan states the formula without proof.)

**Reading.** n ranges over n ≥ 1 (the listed terms; n = 0 also diverges: 1, 0, 2, 1, 3, 2, ...).

**Result.** True: for n ≥ 1, c(k) → ∞ iff n − 1 = 2^v·u with u odd and v odd. Hence a(n) = A036554(n) + 1, and
the entry's m(n) is u, the odd part of n − 1. Otherwise c(k) is eventually 1.

**Argument.** Work with pairs (c(k), c(k+1)). Write up(a, E) = (a, a+E) and down(b, E) = (b+E, b).
1. *Halving.* up(a, 2D) ↦ (a+2D, a+D) = down(a+D, D) and down(a, 2D) ↦ (a, a+D) = up(a, D) (same parity:
   average). From (1, n) = up(1, 2^v u), after v steps the pair is up(1+cu, u) for v even or down(1+cu, u) for v
   odd, for some c ≥ 0 (every move adds a multiple of u).
2. *Odd gap, descending.* For odd m: down(b, m) = (b+m, b) ↦ (b, b+2m) ↦ (b+2m, b+m) = down(b+m, m). So
   c grows by m every two steps and tends to ∞.
3. *Odd gap, ascending.* For odd u, two steps take up(x, u) to up(x−u, u) if x > u, and up(x, u) to
   up(u−x, x) if x ≤ u. From up(1+cu, u): c subtractions reach up(1, u), then up(u−1, 1), then
   up(x, 1) ↦ up(x−1, 1) down to up(0, 1) = (0, 1) ↦ (1, 1), which is fixed. So c(k) is eventually 1.
4. n = 1 is the fixed pair (1, 1). For n ≥ 2 write n − 1 = 2^v u; steps 1–3 decide by the parity of v.

Lean: [full proof](A072939/A072939.lean).

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

### [A075885](A075885/): limit a(n)^(1/n) = L (geometric-mean constant)

Lean: [full proof](A208060/A208060_mathlib.lean).

### [A076070](A076070/): no entry is zero

Lean: —.

### [A076072](A076072/): a multiple of n can always be formed from the digits of the next n numbers

**Source.** [A076072](https://oeis.org/A076072) (largest) and [A076070](https://oeis.org/A076070) (smallest multiple of n
formed by using the digits of the next n numbers, or 0 if none), Amarnath Murthy, Oct 2002. Both: "Conjecture: No
entry is zero." "Next n numbers" means T(n-1)+1, ..., T(n) with T(n) = n(n+1)/2 (M. F. Hasler's comment). (OEIS
text, revisions #14 of Jan 17 2020 and #12 of Mar 18 2025, checked 2026-11-06.)

**Reading.** "Formed by using the digits": a permutation of the multiset of all decimal digits of the n numbers,
read as a decimal number without a leading zero (the entries' terms are of this form).

**Result.** True for every n >= 1: some arrangement of the digits is a multiple of n.

**Argument.** For n < 1200 by computer (below). Let n >= 1200, n = 2^a 5^b N' with gcd(N', 10) = 1, e = max(a, b),
and H = gcd(9, N')·Z/N', a cyclic group of order h = N'/gcd(9, N') <= n.
1. *Digit counts.* Among n consecutive integers each digit value occurs as units digit at least n/10 - 1 times, as
   tens digit at least n/10 - 10 times and as hundreds digit at least n/10 - 100 times (complete blocks of 10, 100,
   1000). So every digit value occurs at least 3n/10 - 111 times. Reserve e zeros and one digit 1. The pairs
   (0,1), (2,3), (4,5), (6,7), (8,9) then give at least 5(3n/10 - 111) - e - 1 >= n - 1 >= h - 1 disjoint pairs
   (v, v+1), because e <= log2 n and n >= 1200.
2. *Arrangement.* From the right: the e zeros; then h - 1 pairs at positions (e+2t, e+2t+1); then the other digits;
   the reserved 1 in front. Every such number is divisible by 2^a 5^b. Swapping the two digits of pair t changes
   the value by ±9·10^(e+2t), a generator of H in Z/N'.
3. *Subset sums.* If A ⊆ H and x generates H, then A ∪ (A + x) is larger than A unless A = H. So the h - 1 optional
   swaps reach V0 + H mod N', where V0 is the value with no swap.
4. *The residue mod 9.* Every arrangement is congruent mod 9 to the digit sum, hence to the sum of the n numbers,
   n(n^2 + 1)/2. If 3 | N' then 3 | n and 3 | n(n^2+1)/2; if 9 | N' then 9 | n(n^2+1)/2. So V0 ∈ H and some choice of
   swaps gives 0 mod N'. With step 2 the number is divisible by n, and its leading digit is 1.

Lean: —.

### [A077602](A077602/): M(n,1) ~ A077596(n) · sqrt(πn/2) for the Moebius polynomials

**Source.** [A077602](https://oeis.org/A077602) (decimal expansion of lim M(n,1)/2^n = 1.5301914...). Comment:
"Conjecture: M(n,1) ~ A077596(n) * sqrt(Pi*n/2), where A077596(n) is the largest coefficient of the n-th
Moebius polynomial, M(n,x)." (OEIS text, CC BY-SA 4.0, read 2026-11-06.) M(1,x) = 1 and
M(n,x) = 1 + x Σ_{m<n} ⌊n/m⌋ M(m,x) ([A074586](https://oeis.org/A074586)); [A077596](https://oeis.org/A077596)(n)
is the coefficient of x^(k0), k0 = ⌈n/2⌉ − 1 (the entry calls it the largest coefficient).

**Result.** True, for both readings of A077596(n) (the coefficient of x^(k0), or the largest coefficient).
Equivalently A077596(n) ~ c 2^n/√n with c = L √(2/π) = 1.2209161..., L = lim M(n,1)/2^n (Kotesovec's
numerical constant in A077596).

**Argument.** 1. *Recurrence.* ⌊n/m⌋ − ⌊(n−1)/m⌋ = [m | n], so for n ≥ 2
   M(n) − M(n−1) = x M(n−1) + x Σ_{d|n, d<n} M(d), i.e. M(n) = (1+x) M(n−1) + G(n) with G(n) = x Σ_{d|n,d<n} M(d).
   Unrolling, M(n) = Σ_{j=1}^{n} (1+x)^(n−j) G(j) with G(1) = 1. Every G(j) has nonnegative coefficients
   and degree ≤ j/2; write g_j = G(j,1).
2. *Sizes.* M(n,1) = 2M(n−1,1) + g_n and g_n ≤ Σ_{d ≤ n/2} M(d,1); induction gives M(n,1) ≤ 3^n, hence
   g_j ≤ (3/2)·3^(j/2) and Σ_j g_j 2^(−j) converges geometrically (ratio √3/2). So
   M(n,1)/2^n = Σ_{j≤n} g_j 2^(−j) → L = Σ_j g_j 2^(−j) > 0.
3. *Coefficients.* [x^k] M(n) = Σ_j Σ_i [x^i]G(j) · C(n−j, k−i). Let B(m) = C(m, ⌊m/2⌋) ~ 2^m √(2/(πm)).
   Upper bound for every k: [x^k] M(n) ≤ Σ_j g_j B(n−j). Split at j = n/2: for j ≤ n/2,
   B(n−j)/(2^(n−j) √(2/(πn))) ≤ √2·(1 + o(1)), so dominated convergence gives
   Σ_{j≤n/2} g_j B(n−j) = (L + o(1)) 2^n √(2/(πn)); for j > n/2, Σ g_j 2^(n−j) ≤ 2^n·O((√3/2)^(n/2)) = o(2^n/√n).
   Lower bound at k0: for fixed J and j ≤ J, the indices k0 − i are (n−j)/2 + O(J), and C(m, m/2 + O(1)) ~ B(m);
   so [x^(k0)] M(n) ≥ (Σ_{j≤J} g_j 2^(−j) − o(1)) 2^n √(2/(πn)), then J → ∞.
   Hence [x^(k0)] M(n) ~ max_k [x^k] M(n) ~ L 2^n √(2/(πn)) ~ M(n,1)/√(πn/2).

Lean: needs Mathlib.

### [A077739](A077739/): a(n) = 0 exactly for n = 11, 17, 19

**Source.** [A077739](https://oeis.org/A077739) (offset 1), Amarnath Murthy, Nov 20 2002: "Smallest multiple of n
beginning and ending in n and having a digit sum of n, or 0 if no such number exists." Comment: "Conjecture: a(n) = 0
if and only if n is 11, 17 or 19." [A077740](https://oeis.org/A077740) is A077739(n)/n with the same conjecture
(Ray Chandler, Sep 05 2003). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** N is admissible for n when n | N, the decimal string of N starts with that of n and ends with it
(overlap allowed, so N = n counts for n ≤ 9), and the digit sum of N is n. This reading reproduces the data of
A077739 for n ≤ 40 (certificate/brute.py).

**Result.** True. For n ≥ 1 an admissible N exists iff n ∉ {11, 17, 19}; so A077739(n) = 0 and A077740(n) = 0 iff
n ∈ {11, 17, 19}.

**Argument.** Write ds for the decimal digit sum.
- n = 19. N contains the digits 1, 9 at both ends. If the two copies of "19" do not overlap, ds(N) ≥ 20. They cannot
  overlap in one digit (9 ≠ 1); full overlap gives N = 19 with ds = 10.
- n = 17. As for 19, N = 17·10^(k+2) + 100·c + 17 where c has digits summing to 1 (the middle part), so c = 10^j.
  Then 17 | 100·10^j, impossible.
- n = 11. The two lowest digits of N are 1, 1, and ds(N) = 11, so the remaining digits sum to 9. The alternating
  digit sum of N equals that of the remaining digits, an odd number in [−9, 9], so it is not divisible by 11.
- n ≥ 63, construction. Let s = ds(n), r = n − 2s. By pigeonhole, 10^(i+P) ≡ 10^i (mod n) for some i and P ≥ 1. Let
  q = n / gcd(n, 10^i), so n | 10^i·q. Pick V = q·(m0 + 9k) with V ≡ r (mod 9) (possible since r ≡ −n (mod 9) and
  q | n) and r < V ≤ r + 18q; write V − r = 9y and y = 11z + v with v ≤ 10. Put u = r − v − z (≥ 0 because
  s ≤ 9 + n/10 and n ≥ 63). Let M = 10^i·Σ_t 10^(3P·t)·b_t where the blocks b_t are u copies of 1, v copies of 10 and
  z copies of 100. Each block has 3P ≥ 3 digits, so ds(M) = u + v + z = r, and modulo n,
  M ≡ 10^i·(u + 10v + 100z) = 10^i·V ≡ 0. Finally N = n + 10^D·(M + 10^M·n) (D = number of digits of n) begins and
  ends with n, is divisible by n, and has digit sum 2s + r = n.
- 1 ≤ n ≤ 62, n ∉ {11, 17, 19}: explicit witnesses (certificate/witnesses.txt), the least multiple for n ≤ 49 and
  n = 56, 58, 59, and a digit-DP witness of the form n·10^(L+D) + mid·10^D + n otherwise.

Lean: [full proof](A077739/A077739_mathlib.lean).

### [A077740](A077740/): a(n) = 0 iff n is 11, 17 or 19

Lean: [full proof](A077739/A077739_mathlib.lean).

### [A078008](A078008/): even denominators in the rows of the Farey tree

**Source.** [A078008](https://oeis.org/A078008), expansion of (1-x)/((1+x)(1-2x)) = 1, 0, 2, 2, 6, 10, 22, ...
Comment (Adamson, 2003): "Conjecture: a(n) = the number of fractions in the infinite Farey row of 2^n terms with
even denominators. Compare the Salamin & Gosper item in the Beeler et al. link" (HAKMEM item 54: a random
rational has even denominator with probability 1/3). (OEIS text checked 2026-11-06.)

**Reading.** The "infinite Farey row of 2^n terms" is row n of the Stern-Brocot (Farey) tree of (0,1): row 0 is
{1/2}, row 1 is {1/3, 2/3}, row 2 is {1/4, 2/5, 3/5, 3/4}; each fraction is the mediant of its two Farey neighbours
and row n holds the 2^n fractions inserted at step n+1 of the mediant construction. This reading reproduces
1, 0, 2, 2. (In the full Stern-Brocot tree of (0, infinity), rooted at 1/1, the count is A001045(n) instead;
A078008(n) there counts fractions with odd numerator and odd denominator.)

**Result.** True: for every n >= 0 row n has exactly a(n) = (2^n + 2(-1)^n)/3 fractions with even denominator.

**Argument.** Store a node as its neighbours a/b < c/d (fraction (a+c)/(b+d)); then bc - ad = 1, preserved by the
children (a/b, (a+c)/(b+d)) and ((a+c)/(b+d), c/d). So b, d are not both even. The children have denominators
2b+d = d and b+2d = b (mod 2), so the number of even-denominator children is [b even] + [d even] = 1 - [b+d even].
Summing over row n: E(n+1) = 2^n - E(n), E(0) = 1. The recurrence a(n+2) = a(n+1) + 2a(n), a(0) = 1, a(1) = 0
gives a(n+1) + a(n) = 2^n, so E(n) = a(n).

Lean: [full proof](A078008/A078008_mathlib.lean).

### [A078122](A078122/): row sums of the M^3-shift matrix are the partitions of 3^n into powers of 3

**Source.** [A078122](https://oeis.org/A078122) (Paul D. Hanna): "Infinite lower triangular matrix, M, that satisfies
[M^3](A078122/i,j) = M(i+1,j+1) for all i,j>=0 ... with M(0,k)=1 and M(k,k)=1 for all k>=0." Comment: "Conjecture: the
sum of the n-th row equals the number of partitions of 3^n into powers of 3 (A078125)." Formula line, also
marked conjecture: "M(n, k) = the coefficient of x^(3^n - 3^(n-k)) in the power series expansion of
1/Product_{j=0..n-k}(1-x^(3^j)) whenever 0<=k<n". (OEIS text, revision #10 of Mar 17 2023, checked 2026-11-06.)

**Reading.** "M(0,k)=1" is read as M(k,0) = 1 (first column of ones), as the data 1; 1,1; 1,3,1; 1,12,9,1 show.
Such an M is unique: column 0 and the diagonal are given, and row i+1 (columns ≥ 1) is row i of M^3, which only
involves rows ≤ i of M.

**Result.** True, together with the formula line. M(n,k) is the number of partitions of 3^n into powers of 3
whose largest part is exactly 3^(n-k); summing over k = 0..n gives all partitions of 3^n into powers of 3. The
same argument works for every base m ≥ 2 (Hanna's M^2 and M^4 analogues A078121 and A078536 with partitions of
2^n and 4^n), checked numerically below.

**Argument.** Let N(n,k) (0 ≤ k ≤ n) count partitions of 3^n into powers of 3 with largest part 3^(n-k), and
N(n,k) = 0 for k > n. Then N(n,0) = N(n,n) = 1. It remains to show [N^3](A078122/i,j) = N(i+1,j+1); uniqueness then gives
M = N.

1. *Splitting.* Take a partition of 3^(i+1) into powers of 3 with largest part 3^(i-j) ≤ 3^i, parts listed in
   decreasing order. Before a part 3^r is added, the running sum is a multiple of 3^r (all earlier parts are), so
   the running sums never jump over a multiple of 3^i. Hence the list splits uniquely into three consecutive
   blocks A, B, C (largest parts first), each summing to 3^i, with min A ≥ max B and min B ≥ max C. Conversely
   any such triple concatenates to such a partition, and its split returns the triple.
2. *Counting the blocks.* Let max C = 3^(i-a) and max B = 3^(i-b), so i ≥ a ≥ b ≥ j. C is a partition of 3^i
   with largest part 3^(i-a): N(i,a) choices. B has all parts ≥ 3^(i-a), so B / 3^(i-a) is a partition of 3^a
   with largest part 3^(a-b): N(a,b) choices. A / 3^(i-b) is a partition of 3^b with largest part 3^(b-j):
   N(b,j) choices. So N(i+1,j+1) = Σ_{a,b} N(i,a) N(a,b) N(b,j) = [N^3](A078122/i,j).
3. N(n,k) = [x^(3^n - 3^(n-k))] 1/Π_{t=0..n-k}(1 - x^(3^t)) (remove one copy of the largest part), which is the
   formula line, and Σ_k N(n,k) = A078125(n).

Lean: [full proof](A078122/A078122_mathlib.lean).

### [A078128](A078128/): partitions into cubes > 1 — a(n) → ∞ with explicit b(k)

**Source.** [A078128](https://oeis.org/A078128) (offset 1), "Number of ways to write n as sum of cubes > 1".
Comment (Reinhard Zumkeller): "Conjecture (lower bound): for all k exists b(k) such that a(n)>k for n>b(k); see
b(0)=A078129(83)=154 and b(1)=A078130(63)=218." (OEIS text, CC BY-SA 4.0; still marked conjecture in revision #18,
Jun 17 2025, checked 2026-11-06.)

**Result.** True: a(n) ≥ m + 1 whenever n ≥ 216m + 182, so b(k) = 216k + 181 works. The quoted values are sharp:
a(154) = 0 and a(n) ≥ 1 for n > 154; a(218) = 1 and a(n) ≥ 2 for n > 218. (Numerically the least b(k) are
154, 218, 255, 282, 319, 335 for k = 0..5; 216k + 181 is only an upper bound.)

**Argument.** Every r ≥ 182 is 8x + 27y (y = 3r mod 8; 181 is the Frobenius number of 8 and 27). For
n ≥ 216m + 182 write n − 216m = 8x + 27y; the partitions with x + 27j eights and y + 8(m − j) twenty-sevens,
j = 0..m, are m + 1 different partitions of n into cubes > 1 (they differ in the number of 8s). For the sharp values:
for n < 512 the parts are among 8, 27, 64, 125, 216, 343 and a partition is fixed by its multiplicities, so a(n) is a
coin-change count, evaluated for n < 398; the bound above covers n ≥ 182 (k = 0) and n ≥ 398 (k = 1).

Lean: [full proof](A078128/A078128_mathlib.lean).

### [A078173](A078173/): max t = n(n+2) and max s = 2n over solutions of rst = n(r+s+t)

**Source.** OEIS [A078173](https://oeis.org/A078173) (John W. Layman, Nov 20 2002): a(n) = max(min(r,s,t)) over
positive integer solutions of r*s*t = n*(r+s+t). Comment: "Conjecture: max(t) = n*(n+2) and max(s) = 2*n,"
maxima over all positive integer solutions r <= s <= t. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True for every n >= 1.

**Argument.** Let r <= s <= t be positive with rst = n(r+s+t). Then t(rs - n) = n(r+s) > 0, so d = rs - n >= 1.
- *max t.* If r = 1 the equation is (s - n)(t - n) = n(n+1) with s - n >= 1, so t <= n + n(n+1) = n(n+2).
  If r >= 2 then (r-2)(s-2) >= 0 gives 2(r+s) <= rs + 4 = n + d + 4, so 2td <= n(n+d+4). If t >= n(n+2)+1
  this gives d(2n^2 + 3n + 2) <= n^2 + 4n, impossible for d >= 1 as n^2 - n + 2 > 0.
  Attained by (1, n+1, n(n+2)).
- *max s.* From t >= s, s(rs - n) <= t(rs - n) = n(r+s), so s(rs - 2n) <= nr. If s >= 2n+1 then
  rs - 2n >= r(2n+1) - 2n >= r, so s(rs - 2n) >= (2n+1)r > nr. Hence s <= 2n, attained by (1, 2n, 2n+1).

Lean: [full proof](A078173/A078173_mathlib.lean).

### [A078537](A078537/): row sums of A078536 are the partitions of 4^n into powers of 4

**Source.** [A078537](https://oeis.org/A078537) (Paul D. Hanna, 2002): number of partitions of 4^n into powers of 4.
"Conjecture: a(n) = sum of the n-th row of lower triangular matrix A078536." [A078536](https://oeis.org/A078536):
the infinite lower triangular matrix M with [M^4](A078537/i,j) = M(i+1,j+1), "M(0,k)=1 and M(k,k)=1"; the entry also
conjectures M(n,k) = [x^(4^n - 4^(n-k))] 1/Prod_{j=0..n-k}(1 - x^(4^j)) for 0 <= k < n. (OEIS text, revisions #21 of
Nov 28 2017 and #10 of Oct 20 2019, checked 2026-11-06.)

**Reading.** "M(0,k)=1" read as M(k,0) = 1 (column 0; the entry's data and Mathematica program use this). The
matrix product of lower-triangular infinite matrices is the finite sum over l <= i.

**Result.** True, for every base q >= 2 (q = 4 here; q = 2, 3 are A078121, A078122). Write t(m, c) for the number
of partitions of c q^m into 1, q, ..., q^m. Then M(n,k) = t(n-k, q^k - 1) (the entry's conjectured formula), more
generally [M^s](A078537/n,k) = t(n-k, s q^k - 1) for s >= 1, and row n sums to the number of partitions of q^n into powers of q.

**Argument.** 1. *Convolution identity.* For A >= 1, b >= 0: sum_{j=0..m} t(m-j, A q^j - 1) t(j, b) = t(m, A + b). Induction on m and
   b, using t(m+1, c+1) = t(m+1, c) + t(m, q(c+1)) and t(0, c) = 1. For b = 0 it reads
   sum_j t(m-j, A q^j - 1) = t(m, A) (classify partitions of A q^m by the largest part).
2. *Powers.* Let P_s(n,k) = t(n-k, s q^k - 1). With A = q^k and b = s q^k - 1, step 1 gives P_1 P_s = P_(s+1).
   Hence P_1^q = P_q, and P_q(i,j) = t(i-j, q^(j+1) - 1) = P_1(i+1, j+1); also P_1(n,0) = P_1(n,n) = 1.
3. *Uniqueness.* The defining relations fix row i+1 from rows <= i, so A078536 = P_1.
4. *Row sum.* sum_k t(n-k, q^k - 1) = t(n, 1) by the b = 0 case with A = 1, and t(n, 1) counts partitions of q^n into
   powers of q (parts are <= q^n).

Lean: [full proof](A078537/A078537_mathlib.lean).

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

### [A082981](A082981/): the six section conjectures

**Source.** [A082981](https://oeis.org/A082981) (John W. Layman, May 28 2003): start with S(0) = {1,1}; S(k) =
I(S(k-1)), where I inserts a(i)+a(i+1) between a(i) and a(i+1) whenever 4a(i+1) <= 5a(i); the sequence is the limit
of S(k). Conjectures in the entry: (1) a(2n+1) is A077442 ("2*a(n)^2 + 7 is a square"); (2) a(4n+1) is A038761;
(3) a(4n+2) is A077444 ("numbers k such that (k^2 + 4)/2 is a square"); (4) a(4n+2)/2 is A002315; (5) a(4n+4) is
A005319; (6) a(4n+4)/4 is A001109. Also "It appears that a(n) = 6*a(n-4) - a(n-8)" and Colin Barker's empirical
g.f. (OEIS text, CC BY-SA 4.0, revision #22 of Dec 24 2025, checked 2026-11-06.)

**Reading.** "ax^2+7" in conjecture (1) is a typo for 2x^2+7 (the A077442 definition). Offsets: A077442,
A038761, A002315, A005319, A001109 have offset 0, A077444 offset 1; so the claims are a(2n+1) = A077442(n),
a(4n+1) = A038761(n), a(4n+2) = A077444(n+1), a(4n+2)/2 = A002315(n), a(4n+4) = A005319(n+1), a(4n+4)/4 =
A001109(n+1) for n >= 0. A077442 and A077444 are read as their definitions (increasing enumerations of the
solution sets), so (1) and (3) include that the sections hit every solution.

**Result.** All six are true. Moreover a(4j+t) = 4c_j + t d_j (t = 1..4, with 4c_{j+1} = 4c_j + 4d_j for t = 4),
where (c_0, d_0) = (0, 1) and (c, d) -> (c + d, 4c + 5d); this gives a(n) = 6a(n-4) - a(n-8) and the g.f.

**Argument.** 1. *Locality.* I acts on each adjacent pair separately, so the list grown from a pair (x, y) satisfies
   F_{k+1}(x,y) = F_k(x, x+y) ++ tail F_k(x+y, y) if 4y <= 5x, and F_k(x,y) = [x, y] for all k otherwise.
2. *Leftmost live pair.* If x < 4y <= 5x the pair (x, x+y) is dead, so F_{k+1}(x,y) = x :: F_k(x+y, y). If
   4y <= x, F_k(x, x+y) is a prefix of F_{k+1}(x,y).
3. *Blocks.* For A < d (and 4d <= 5A when starting at A itself), the pairs (A + id, d), i = 0..3, are in the first
   case and output A, A+d, A+2d, A+3d; the pair (A+4d, d) is in the second case and hands over to the pair
   (A', d') = (A+4d, A+5d), which again has A' < d' and 4d' <= 5A'. Starting from (1,1) = (0 + 1, 1), the stable
   prefix of S(k) is 1, 2, 3, 4, 9, 14, 19, 24, 53, ..., with A_j = 4c_j, d_j as above.
4. *Recurrences.* (c, d) -> (c + d, 4c + 5d) has trace 6 and determinant 1, so c_j, d_j and every fixed linear
   combination satisfy x(j+2) = 6x(j+1) - x(j). This gives (2) 4c+d, (4) 2c+d, (5) 4c, (6) c from the first two
   terms.
5. *Pell sets.* d^2 - 4cd - 4c^2 = 1 for all j. Then 2(4c+d)^2 + 7 = (3d-2c)^2, 2(4c+3d)^2 + 7 = (2c+5d)^2 and
   (4c+2d)^2 + 4 = 2(2d)^2. Conversely, a solution of 2x^2 + 7 = y^2 with x >= 6 descends to (3x - 2y, 3y - 4x),
   a smaller positive solution; by induction it is 4c_j + d_j or 4c_j + 3d_j, and x = 3x' + 2y' is then
   4c_{j+1} + d_{j+1} or 4c_{j+1} + 3d_{j+1}; x <= 5 leaves x = 1, 3. Likewise k^2 + 4 = 2y^2 with k >= 6 descends
   to (3k - 4y, 3y - 2k), and k <= 5 leaves k = 2. The sections are strictly increasing, so they are the
   increasing enumerations of the solution sets: (1) and (3).

Lean: [full proof](A082981/A082981_mathlib.lean).

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

### [A083942](A083942/): a(n) = Sum_{k=1..2^n-1} Catalan(k)

**Source.** [A083942](https://oeis.org/A083942) (A. Karttunen): positions of the breadth-first-wise encodings
(A002542) of the complete binary trees (A084107) in A014486. Conjecture (A. Adamchuk, Nov 10 2007, in the entry):
a(n) = Sum_{k=1..2^n-1} A000108(k), equivalently a(n) = A014138(2^n - 2) for n > 0. (OEIS text, checked 2026-11-06.)

**Reading.** [A014486](https://oeis.org/A014486) lists the totally balanced numbers in increasing order, offset 0
(0 = empty word). The breadth-first code of the complete binary tree with s = 2^n - 1 internal nodes lists the s
internal nodes (1) and then the leaves (0), the last leaf dropped: 1^s 0^s = (2^s - 1) 2^s in binary
(A002542: 0, 2, 56, ...). a(n) is the number of totally balanced numbers below it. This reproduces the data
(certificate/check.py).

**Result.** True: a(n) = Sum_{k=1..2^n-1} C_k. More generally, the position of 1^s 0^s in A014486 is
Sum_{k=1..s} C_k for every s.

**Argument.** Totally balanced numbers with 2k binary digits are the Dyck words of semilength k, so there are C_k of
them, and they lie in [2^(2k-1), 2^(2k)). Among words with s ones and 2s digits, 1^s 0^s is the largest. So the words
below 1^s 0^s are 0, all words of semilength 1..s-1, and all but one of semilength s:
1 + C_1 + ... + C_(s-1) + (C_s - 1) = C_1 + ... + C_s.

Lean: [full proof](A083942/A083942_mathlib.lean).

### [A084043](A084043/): a(n) = 0 iff 10 divides n

**Source.** [A084043](https://oeis.org/A084043) (Amarnath Murthy, 2003): smallest palindromic multiple of n in
which the digit string of n appears "sandwiched between at least a pair of digits", or 0 if none exists.
[A084044](https://oeis.org/A084044) (Murthy and Meenakshi Srikanth, 2003): smallest palindromic multiple of n in
which n is a substring anywhere, or 0. Both: "Conjecture: a(n) = 0 iff n = 10k." (OEIS text, CC BY-SA 4.0, A084043
revision #5 of Dec 05 2013, A084044 revision #7 of Aug 23 2014, checked 2026-11-06.)

**Result.** True for both: for n >= 1 a palindromic multiple of n containing n with a digit on each side exists iff
10 does not divide n (hence also one containing n anywhere).

**Argument.** 1. *10 | n.* A positive multiple of 10 ends in 0; a palindrome would then start with 0. No such multiple exists.
2. *10 does not divide n.* Write n = g m with g = 2^a 5^b and gcd(m, 10) = 1. Let e = a + b + 1, so g | 10^e and
   g < 10^e; let E be the decimal string of g padded with leading zeros to length e. Since 10 does not divide
   g, the last digit of g is nonzero. Let s be the decimal string of n and
   Y = rev(E) s rev(s) E (a palindrome whose first digit is the last digit of g, nonzero, and whose value is
   g mod 10^e, hence divisible by g). Let L = |Y|, M = m (10^L - 1), k = 2 phi(M) >= 2, and P = Y repeated k
   times. P is a palindrome, P = Y (1 + 10^L + ... + 10^{L(k-1)}), and 10^{Lk} == 1 (mod M) by Euler (10^L is
   coprime to m and to 10^L - 1), so m divides the repunit factor; g divides Y. So n | P, and the copy of s in the
   second block of P has digits on both sides.

Lean: [full proof](A084043/A084043_mathlib.lean).

### [A084044](A084044/): a(n) = 0 iff 10 divides n

Lean: [full proof](A084043/A084043_mathlib.lean).

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

### [A087726](A087726/): a(n) = n^2 if and only if n is squarefree

**Source.** [A087726](https://oeis.org/A087726) (offset 1), Yuval Dekel, Sep 28 2003: "Number of elements X in the
matrix ring M_2(Z_n) such that X^2 == 0 mod n." Comment: "Conjecture: a(n)=n^2 if and only if n is squarefree. [Ben
Branman, Mar 22 2013]". Further comments: the squarefree direction is true (Eric M. Schmidt, Mar 23 2013); a
conjectured prime-power formula a(p^k) = (1+3p^2+2k(p^2-1)+(-1)^k(p^2-1)) p^(2k-2)/4 "would imply the conjecture"
(Robert Israel, Jun 10 2015); a proof for k = 1 (Manfred Scheucher, linked pdf). (OEIS text, CC BY-SA 4.0, revision
#27 of Jun 11 2015, checked 2026-11-06.)

**Result.** True: for n >= 1, a(n) = n^2 iff n is squarefree. Moreover a(n) >= n^2 for all n >= 1, and
a(p^k) > p^(2k) for every prime p and k >= 2. Israel's formula is also true: for every prime p and k >= 1,
a(p^k) = p^(4 floor(k/2)) + ceil(k/2) p^(2k-2) (p^2 - 1) = (1+3p^2+2k(p^2-1)+(-1)^k(p^2-1)) p^(2k-2)/4.

**Argument.** 1. *Multiplicative.* For coprime m, n the ring isomorphism Z/mn = Z/m x Z/n, applied entrywise, maps square-zero
   matrices bijectively onto pairs of square-zero matrices.
2. *Primes.* Over the field F_p, X^2 = 0 forces det X = 0 and then tr(X) X = 0, so X = [[a, b], [c, -a]] with
   a^2 + bc = 0. If b != 0, c = -a^2/b (p(p-1) matrices); if b = 0 then a = 0 and c is free (p matrices, including 0).
   So a(p) = p^2.
3. *Prime powers, k >= 2.* In Z/p^k three disjoint families of square-zero matrices:
   - [[a, u], [-a^2/u, -a]] with u a unit: p^k phi(p^k) matrices (entry (0,1) a unit);
   - [[pt, -(pt)^2/u], [u, -pt]] with u a unit, 0 <= t < p^(k-1): p^(k-1) phi(p^k) (entry (1,0) a unit, entry (0,1)
     a multiple of p);
   - matrices with entries (0,0), (1,0), (1,1) multiples of p^h, h = ceil(k/2), and entry (0,1) a multiple of
     p^l, l = floor(k/2) >= 1: every entry of X^2 is a multiple of p^(2h) or p^(h+l) = p^k, so X^2 = 0;
     p^(3l+h) matrices (entries (0,1), (1,0) non-units).
   For even k the third family alone has p^(2k) elements; for odd k = 2m+1 the sum is
   p^(4m)(p(p-1) + (p-1) + p) = p^(4m)(p^2 + p - 1) > p^(2k). Either way a(p^k) > p^(2k).
4. By 1-3 and induction over the factorisation, a(n) = prod a(p^k) >= prod p^(2k) = n^2, with equality iff every
   exponent is 1.

5. *Exact count (Israel's formula).* Split the square-zero X mod p^(m+2) by whether some entry is a unit.
   - Primitive X: X^2 = tr(X) X - det(X) I and X mod p is a non-scalar nilpotent, so tr X = det X = 0. If the
     (0,1) entry is a unit, X is in the first family of step 3; if not, the (1,0) entry is a unit (otherwise
     a^2 = -bc and d^2 = -bc are non-units, so no entry is a unit), and a^2 = -bc forces p | a: the second family.
     Count p^(m+2) phi + p^(m+1) phi = p^(2m+2)(p^2 - 1).
   - Non-primitive X: every entry is p w + p^(m+1) t with w mod p^m and 0 <= t < p, uniquely. Then
     X^2 = p^2 W^2 mod p^(m+2), so X^2 = 0 iff W^2 = 0 mod p^m: p^4 a(p^m) matrices.
   So a(p^(m+2)) = p^(2m+2)(p^2-1) + p^4 a(p^m), with a(1) = 1 and a(p) = p^2. Induction gives
   a(p^k) = p^(4 floor(k/2)) + ceil(k/2) p^(2k-2)(p^2-1), which equals Israel's expression for both parities.

Lean: [full proof](A087726/A087726_mathlib.lean).

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

### [A096123](A096123/): a(n) = n!/(p-1)! for large n (p least prime with n ≤ 2p) is false

**Source.** OEIS [A096123](https://oeis.org/A096123), "Least product n*(n-1)*(n-2)*...*(n-k+1) divisible by (n-k)!", conjecture by Amarnath Murthy in the entry: a(n) = n!/(p-1)! for all sufficiently large n, where p is the least prime such that n <= 2*p. The entry adds that A096974 (the n where equality holds) indicates the conjecture is most probably false.

**Reading.** a(n) = n!/(n-k)! for the least k ≥ 0 with (n-k)! dividing n!/(n-k)!. This reproduces all 24 listed terms (`certificate/check.gp`). The entry's PARI program uses divisor (n-k+1)! instead; the argument below works for that reading too (k = p qualifies there because (p+1)!·p! divides (2p)!, as (2p)!/(p!·(p+1)!) is a Catalan number).

**Result.** False. For every prime p, a(2p) ≤ (2p)!/p! < (2p)!/(p-1)!, and p is the least prime with 2p ≤ 2p. So the conjecture fails at n = 2p for every prime p.

**Argument.** For n = 2p, k = p qualifies: (2p)!/p! is divisible by p! because p!·p! divides (2p)! (the binomial coefficient C(2p, p) is an integer). The least qualifying k is at most p, and the product n(n-1)...(n-k+1) grows with k, so a(2p) ≤ (2p)!/p!. The conjectured value is (2p)!/(p-1)! = p·(2p)!/p!, larger since p ≥ 2. Any prime q with 2p ≤ 2q has q ≥ p, so the least such prime is p.

Lean: [full proof](A096123/A096123_mathlib.lean).

### [A096127](A096127/): a(n) = n+1 exactly when n is a prime power

**Source.** [A096127](https://oeis.org/A096127) (offset 2), Amarnath Murthy, Jul 03 2004: "a(n) is the largest k
such that (n^2)!/(n!)^k is an integer." Comment: "Conjecture: a(n)=n+1 only when n is prime or a power of a prime.
[Verified for n=2..5000. - _Amiram Eldar_, Apr 06 2021]" (OEIS text, revision #13 of Apr 06 2021, checked
2026-11-06.)

**Result.** True. For n ≥ 2, a(n) ≥ n+1 always, and a(n) = n+1 if and only if n is a prime power.

**Argument.** Fix a prime p, write s(m) for the base-p digit sum of m, and use Legendre's formula
(p-1) v_p(m!) = m - s(m). Then (n!)^k divides (n^2)! iff for every prime p,
k (n - s(n)) ≤ n^2 - s(n^2).

1. *Digit sums.* s(a+b) ≤ s(a) + s(b), because a! b! divides (a+b)! (apply Legendre to both sides). Also
   s(p m) = s(m). Writing m = (m mod p) + p (m div p) gives s(mn) ≤ (m mod p) s(n) + s(m div p) s(n), so by
   induction s(mn) ≤ s(m) s(n); in particular s(n^2) ≤ s(n)^2. Finally 1 ≤ s(n) ≤ n for n ≥ 1, and s(n) = 1
   exactly when n is a power of p.
2. *k = n+1 always works.* With t = s(n), 1 ≤ t ≤ n: (n+1)(n-t) = n^2 - t^2 - (t-1)(n-t) ≤ n^2 - t^2 ≤
   n^2 - s(n^2).
3. *k = n+2 works when n is not a prime power.* Then n is not a power of p, so 2 ≤ t ≤ n and
   (n+2)(n-t) = n^2 - t^2 - (t-2)(n-t) ≤ n^2 - s(n^2).
4. *k = n+2 fails for n = p^m, m ≥ 1.* Here s(n) = s(n^2) = 1, and (n+2)(n-1) > n^2 - 1 for n ≥ 2.

Since (n!)^k | (n^2)! is downward closed in k, steps 2-4 give a(n) = n+1 iff n is a prime power.

Lean: [full proof](A096127/A096127_mathlib.lean).

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

### [A097945](A097945/): Sum mu(n)/phi(n) = 0

**Source.** OEIS A097945, a(n) = mu(n)·phi(n) (G. McGarvey, 2004). Comment: "Conjecture:
Sum_{n>=1} mu(n)/phi(n) = Sum_{n>=1} a(n)/phi(n)^2 = 0", followed by a pairing argument for
exponents s > 1 and a second conjecture, Sum mu(n)/phi(n)^z = 0 for Re(z) > 1 (entry checked
2026-11-06, last edit Apr 08 2026; the conjecture is unchanged). Listed in the OEIS wiki page
Talk:Conjectures/List.

**Reading.** a(n)/phi(n)^2 = mu(n)/phi(n), so both series are the same. For s = 1 the series
does not converge absolutely (Sum |mu(n)|/phi(n) diverges); "= 0" is read as convergence of the
partial sums Sum_{n<=N} in the natural order to 0. For Re(z) > 1 the series converges absolutely.

**Result.** 1. For every complex z with Re z > 1, Sum mu(n)/phi(n)^z = 0 (absolutely convergent).
   Unconditional, proved in Lean.
2. Sum_{n<=N} mu(n)/phi(n) → 0. Proved in Lean from the hypothesis Sum_{m<=N} mu(m)/m → 0,
   which is the classical theorem of von Mangoldt (1897) and Landau (1899), equivalent to the
   prime number theorem and not in Mathlib.
So both conjectures in the entry are true. The entry's own argument is incomplete (its bound
Sum_{j=N/2..N} 1/phi(j)^s, which also needs the pairing to be exact, does not apply at s = 1, where
the tail Sum_{N/2<j<=N} 1/phi(j) does not tend to 0).

**Argument.** 1. f(n) = mu(n)/phi(n)^z is multiplicative and |f| is summable for Re z > 1: the nonnegative
   multiplicative |f| has prime-power sums 1 + 1/(p−1)^σ, and Sum_p 1/(p−1)^σ < ∞, so its partial
   sums are bounded by the Euler product over smooth numbers. The Euler product
   Sum f = Prod_p (1 + f(p)) then holds, and its factor at p = 2 is 1 − 1/1^z = 0.
2. Write mu/phi = k * g (Dirichlet convolution) with g(m) = mu(m)/m and k = (mu/phi) * (1/id)
   (since (1/id) * (mu/id) = δ). k is multiplicative with k(p^e) = −1/((p−1)p^e) for e ≥ 1, so
   Sum |k(d)| = Prod_p (1 + 1/(p−1)^2) < ∞. Then
   Sum_{n<=N} mu(n)/phi(n) = Sum_{d<=N} k(d)·A(N/d), A(M) = Sum_{m<=M} mu(m)/m.
   A(M) → 0 and A is bounded, so each term tends to 0 and is dominated by B|k(d)|; Tannery's
   theorem gives the limit 0.

Lean: [full proof](A097945/A097945_mathlib.lean).

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

### [A102237](A102237/): a(n) = 2^n for n > 5

**Source.** [A102237](https://oeis.org/A102237) (Giovanni Teofilatto, 2005; corrected and extended by Ray Chandler):
smallest number equal to the product of n primes which is also equal to the sum of n distinct primes. Comment:
"Conjecture: a(n) = 2^n for n>5. - Ray Chandler Feb 25 2005". Data 2, 9, 12, 36, 48, 64, 128, ... (OEIS text,
CC BY-SA 4.0, revision #7 of Nov 01 2019, checked 2026-11-06.)

**Reading.** "Product of n primes" counts multiplicity (a(2) = 9 = 3·3). Every product of n primes is ≥ 2^n, so
a(n) = 2^n iff 2^n is a sum of n distinct primes.

**Result.** True: for every n ≥ 6, 2^n is a sum of n distinct primes, so a(n) = 2^n.

**Argument.** Parity: for even n use n odd primes summing to 2^n; for odd n use 2 plus n − 1 odd primes summing to
2^n − 2. Call S(k, N): N is a sum of k distinct odd primes.
1. *Step.* Suppose S(k, N') holds for every N' ≡ k (mod 2) in [L_k, B_k], with L_k ≥ 2·396738. Let N ≡ k+1 (mod 2),
   2L_k/(1 − ε) ≤ N ≤ 2B_k, where ε = 1/(25 ln² L_k). By Dusart (2010, Prop. 6.8: for x ≥ 396738 there is a prime
   in (x, x(1 + 1/(25 ln² x))]) with x = N/2 ≥ L_k there is a prime p with N/2 < p ≤ (N/2)(1 + ε) ≤ N − L_k. Then
   N − p ∈ [L_k, B_k] has the parity of k, so it is a sum of k distinct odd primes, each ≤ N − p < N/2 < p. Adding p
   gives S(k+1, N). So the statement holds with L_{k+1} = 2L_k/(1 − 1/(25 ln² L_k)), B_{k+1} = 2B_k.
2. *Base.* k₀ = 22, L₂₂ = 3774874 ≈ 0.9·2^22, B₂₂ = 2^23: every even N in this range is the sum of the first 20 odd
   primes (3..73) and two distinct primes > 73 (computer check).
3. *Growth.* Then B_k = 2^{k+1} and L_k/2^k increases to about 0.9035 < 0.95 (computed to k = 10^5, with the tail
   bounded by exp(Σ ε_j) ≤ exp(8.5·10^−7)). So for even k ≥ 22 both 2^k and 2^{k+1} − 2 lie in [L_k, B_k]: 2^n is a
   sum of n distinct odd primes for even n ≥ 22, and 2^n = 2 + (sum of n − 1 distinct odd primes) for odd n ≥ 23.
4. *Small n.* For 6 ≤ n ≤ 23 explicit representations (e.g. 64 = 3 + 5 + 7 + 13 + 17 + 19,
   128 = 2 + 3 + 5 + 7 + 11 + 17 + 83).

Lean: needs Mathlib.

### [A102613](A102613/): π(n)/(n − π(n)) → 0

**Source.** [A102613](https://oeis.org/A102613), comment: "Conjecture: The ratio Pi(x)/(n-Pi(x)) tends to 0 as n
tends to infinity. ... but unfortunately not proof." (OEIS text, CC BY-SA 4.0.)

**Result.** True; a direct consequence of π(n)/n → 0.

**Argument.** π(n)/(n − π(n)) = (π(n)/n)/(1 − π(n)/n), and π(n)/n → 0 (Chebyshev, or an elementary sieve:
the proportion of integers ≤ n coprime to the first k primes tends to ∏(1 − 1/p), which is arbitrarily small).

Lean: [full proof](A102613/A102613_mathlib.lean).

### [A103990](A103990/): sqrt(pi) I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1)

**Source.** [A103990](https://oeis.org/A103990) (Eric W. Weisstein, Feb 23 2005): "Reduced numerators of the
hypercube line-picking integrand sqrt(Pi)*I(n,0)"; [A103991](https://oeis.org/A103991): the denominators. Comment in
A103990: "Conjecture: Let b(n) be A103991(n), then a(n)/b(n) = (2/3)*(n^3-n^2+2*n+1)/(2*n+1). - _Gerald McGarvey_,
Aug 11 2009". Data: 20 terms. The integrand comes from MathWorld's
[Hypercube Line Picking](https://mathworld.wolfram.com/HypercubeLinePicking.html), which credits M. Trott (personal
communication, 2005) with an algorithm that reduces the mean distance Delta(n) in the unit n-cube to
Delta(n) = Int_0^oo I_n(x) dx and prints I_1, ..., I_4. (OEIS text, CC BY-SA 4.0, revision #10 of Feb 16 2025;
MathWorld checked 2026-11-06.)

**Reading.** Trott's algorithm is not published. We read I_n as follows. With d(u) = Int_0^1 Int_0^1
e^{-u^2 (x-y)^2} dx dy = (e^{-u^2} - 1 + sqrt(pi) u erf u)/u^2 (MathWorld Eq. 10), Delta(n) =
(1/sqrt(pi)) Int_0^oo (1 - d(u)^n)/u^2 du (Eq. 8 with s = 1). I_n is the unique element of the span of
e^{-k x^2} erf(x)^l / x^(l mod 2) (k >= 1) that differs from (1/sqrt(pi)) (1 - d^n)/u^2 by a derivative of a
function of the same kind (integration by parts; the allowed functions are u^b e^{-k u^2} erf(u)^l with k >= 1, or
k = 0 and b != 0). This reading reproduces MathWorld's four integrands I_1, ..., I_4 term by term and all 20 data
terms of A103990/A103991 (certificate/check_trott.py).

**Result.** True under this reading: sqrt(pi) I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1) for every n >= 1.
Equivalently sqrt(pi) I(n,0) = (4n^2 - 6n + 11)/12 - 1/(4(2n+1)).

**Argument.** Write t = u^2, X = e^{-u^2}, W = sqrt(pi) erf(u)/u (so d = W - (1 - X)/t) and use monomials
t^j X^k W^l.
1. *Relations.* For h = u t^j X^k W^l, D h = (1 + 2j - l) t^j X^k W^l - 2k t^(j+1) X^k W^l + 2l t^j X^(k+1) W^(l-1);
   h is allowed unless k = 0 and l = 2j + 1. The basis is X^(g-l) W^l t^(floor(l/2)) (0 <= l < g), with value
   at 0 equal to 1 (l = 0), 2 (l = 1), 0 (l >= 2).
2. *The value functional.* For fixed (k >= 1, l), the relation at j links V(j), V(j+1) and V(j, k+1, l-1).
   Fixing V on the basis (at j0 = floor(l/2)) and solving upwards and downwards in j uses every relation
   exactly once, so this V kills all relations; for k = 0 the relation defines V(j, 0, l). Hence the value at 0
   of the canonical form of f is V(f), canonical forms are unique (the same construction with other anchor
   values separates the basis), and sqrt(pi) I(n,0) = V((1 - d^n)/t). Below the anchor, V(-tau, k, l) =: Vn
   obeys (1 - 2tau - l) Vn(tau, k, l) = 2k Vn(tau-1, k, l) - 2l Vn(tau, k+1, l-1), Vn(tau, k, 0) =
   (-2)^tau k^tau/(2tau-1)!!, Vn(0, k, l) = 2^l l.
3. *Polynomiality.* By that recursion Vn(tau, ., l) is a polynomial in k of degree <= tau. Expanding
   (1 - d^n)/t = t^-1 - Sum C(n,i) C(i,m) (-1)^(i+m) t^-(i+1) X^m W^(n-i), the sum over m is an i-th forward
   difference of a polynomial of degree i+1, so only its two top coefficients survive:
   sqrt(pi) I(n,0) = -Sum_i C(n,i) q(i, n-i), with q(tau,l) = Delta^tau Vn(tau+1, ., l)(0) and
   a(tau,l) = Delta^tau Vn(tau, ., l)(0) obeying first-order recursions in (tau, l).
4. *Closed forms.* With I(alpha,beta) = Int_0^1 r^(alpha+beta) (r-2)^alpha dr:
   a(tau,l) = (-1)^tau l 2^l - 2^(l+1) tau I(tau-1, l) (tau >= 1), a(0,l) = l 2^l (l >= 1), a(0,0) = 1, and
   q(tau,l) = (-1)^tau 2^l (-l(2l + 3tau)/6) + 2^l ((l^2 - 2l tau - 5l - 3tau^2 - 3tau)/3) I(tau,l).
   They satisfy the recursions by two integration-by-parts relations for I (found from the generating functions
   G = 1 + 2y e^{-x+2y} - 2x e^{-x+2y} J and K, J = Int_0^1 e^{x s^2 - 2ys} ds, which solve the first-order PDEs
   of the recursions; certificate/pde_check.py, certificate/series_check.py).
5. *Diagonal sum.* Sum_i C(n,i) 2^(n-i) I(i, n-i) w(i) = Int_0^1 r^n Sum_i C(n,i) w(i) (r-2)^i 2^(n-i) dr, and the
   binomial moments give -Sum_i C(n,i) q(i,n-i) = (n^2 - 3n + 2)/3 + n(n+1)/(2n+1)
   = (2/3)(n^3 - n^2 + 2n + 1)/(2n+1).

Lean: [full proof](A103990/A103990_mathlib.lean).

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

### [A113676](A113676/): row lengths of Golomb's sequence cut into rows = first differences of A014644

**Source.** [A113676](https://oeis.org/A113676) (Floor van Lamoen and Paul D. Hanna, Nov 06 2005): take Golomb's
sequence [A001462](https://oeis.org/A001462) with one fewer 2 (1, 2, 3, 3, 4, 4, 4, 5, ...) and cut it into rows: row 1
is [1], row n has as many elements as the row sum of row n-1; a(n) = number of elements of row n (1, 1, 2, 6, 27,
234, ...). Comments: "Conjecture: a(n) for n>1 gives first differences of Lionel Levine's sequence A014644(n) for
n>=3." and "Conjecture: Final elements of the rows form A014644 except for duplicate 2."
[A014644](https://oeis.org/A014644): array starting with {1,1}, the i-th term of a row gives the number of i's in the
next row; final term of each row. (OEIS text, CC BY-SA 4.0, A113676 revision #9 of Mar 05 2025, checked 2026-11-06.)

**Reading.** Conjecture 1: a(n) = A014644(n+2) - A014644(n+1) for n ≥ 2 (n = 2: 3 - 2 = 1). Conjecture 2: row 1 ends
in A014644(1) = 1 and row n ≥ 2 ends in A014644(n+1), so the final elements are A014644 with one of its two 2s removed.

**Result.** Both conjectures are true.

**Argument.** Let Γ map a list (c_1, ..., c_m) to c_1 copies of 1, then c_2 copies of 2, and so on; A014644's rows
are R_1 = (1,1), R_{k+1} = Γ R_k, and A014644(n) is the last term of R_n.
1. Golomb's sequence G is nondecreasing and each n occurs G(n) times, so Γ(G(1..m)) = G(1..G(1)+...+G(m)). Since
   R_2 = (1,2) = G(1..2), every R_k (k ≥ 2) is a prefix of G, and |R_{k+1}| = sum R_k, last(R_{k+1}) = |R_k|, so
   A014644(m+1) = |R_m|.
2. Let S_n = a(1) + ... + a(n). Claim: S_n + 1 = |R_{n+1}| (true for n = 1, 2). The triangle's rows 1..n are the
   first S_n terms of G with the second term removed. If the claim holds for n-1 and n, then G(1..S_n+1) = R_{n+1}
   and G(1..S_{n-1}+1) = R_n, so R_{n+1} is R_n followed by row n, hence sum(row n) = sum R_{n+1} - sum R_n = |R_{n+2}| - |R_{n+1}|, and
   S_{n+1} + 1 = S_n + sum(row n) + 1 = |R_{n+2}|.
3. Hence a(n) = |R_{n+1}| - |R_n| = A014644(n+2) - A014644(n+1) for n ≥ 2, and the last element of row n is the
   last term of R_{n+1}, which is A014644(n+1).

Lean: [full proof](A113676/A113676_mathlib.lean).

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

### [A116731](A116731/): bubble sort produces (n^3 − 3n^2 + 5n)/3 distinct (flips, iterations) pairs

**Source.** [A116731](https://oeis.org/A116731), "Number of permutations of length n which avoid the patterns
321, 2143, 3124; or avoid the patterns 132, 2314, 4312, etc." Comment: "Conjecture: also counts the distinct
pairs (flips, iterations) that a bubble sort program generates when sorting all permutations of 1..n. [From
Wouter Meeussen, Dec 13 2008]". Formula (Franklin T. Adams-Watters, 2006): a(n) = (n^3 − 3n^2 + 5n)/3; the
entry's g.f. comes from L. Pudwell, *Systematic Studies in Pattern Avoidance* (2005). (OEIS text, CC BY-SA
4.0, checked 2026-11-06.)

**Reading.** Bubble sort: repeat left-to-right passes swapping adjacent out-of-order entries until a pass makes
no swap. Flips = total swaps; iterations = number of passes that swapped. Counting the final no-swap pass too,
or shrinking the scanned range after each pass, gives the same number of distinct pairs (each is an injective
relabelling of the pairs; `certificate/check.py` confirms all four variants for n ≤ 9). The Meeussen program is
not in the entry; this is the standard algorithm.

**Result.** True for every n ≥ 1: the pairs are exactly (0, 0) and (i, b) with 1 ≤ b ≤ n − 1 and
b ≤ i ≤ M(b), where M(b) = Σ_{j<n} min(b, j); there are (n^3 − 3n^2 + 5n)/3 of them.

**Argument.** Let c(v) be the number of entries greater than v to the left of v. One pass lowers every
positive c(v) by exactly 1 (the running maximum carried right is greater than v exactly when c(v) > 0, and it
jumps over v) and makes one swap per v with c(v) > 0. Hence iterations = b = max c(v) and flips = Σ c(v)
(the inversion number). Since c(v) ≤ n − v, b ≤ Σ c ≤ Σ_v min(b, n − v) = M(b) and b ≤ n − 1. Conversely every
table c with c(v) ≤ n − v is realised (insert n, n−1, …, 1, putting v at position c(v) among the larger
values), and a greedy table with c(1) = b, c(v) ≤ min(b, n − v) reaches every total i in [b, M(b)]. With
2M(b) = 2bn − b^2 − b, Σ_{b<n} (M(b) − b + 1) = (n^3 − 3n^2 + 5n)/3 (the b = 0 term is the pair (0, 0)).

Lean: [full proof](A116731/A116731_mathlib.lean).

### [A119659](A119659/): consecutive prime-indexed primes form a triangle from (17, 31, 41) on

**Source.** OEIS [A119659](https://oeis.org/A119659), floor of the area of consecutive prime-indexed-prime
triangles. Comment: "Conjecture: The triples (3,5,11), (5,11,17), (11,17,31) are the only consecutive PIP
triples that cannot form a triangle." (OEIS text, CC BY-SA 4.0.)

**Reading.** q_n = p_{p_n} (A006450: 3, 5, 11, 17, 31, 41, …). (q_n, q_{n+1}, q_{n+2}) forms a
(non-degenerate) triangle iff q_n + q_{n+1} > q_{n+2}, since the sequence is increasing.

**Result.** True: q_n + q_{n+1} > q_{n+2} for every n ≥ 4, and fails exactly for n = 1, 2, 3.

**Argument.** Let m = p_n and M = p_{n+2}.
- n ≤ 62 (p_n ≤ 293): direct computation (`certificate/check.py` checks n ≤ 10⁵).
- n ≥ 63, so m ≥ 307. Nagura (1952): for x ≥ 25 there is a prime in (x, 6x/5), so p_{k+1} < 1.2 p_k when
  p_k ≥ 25, and M < 1.44 m. Rosser–Schoenfeld (1962, (3.13)): p_k < k(ln k + ln ln k) for k ≥ 6; the right
  side increases in k, so q_{n+2} = p_M < 1.44m(ln 1.44m + ln ln 1.44m). Rosser (1938): p_k > k ln k, so
  2q_n = 2p_m > 2m ln m. Finally 2m ln m − 1.44m(ln 1.44m + ln ln 1.44m) = m·h(m) with
  h(m) = 0.56 ln m − 1.44 ln 1.44 − 1.44 ln ln 1.44m; h′(m) > 0 once ln 1.44m > 1.44/0.56, and
  300·h(300) = 21.77 > 0. Hence q_{n+2} < 2q_n < q_n + q_{n+1}.

Lean: needs Mathlib.

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

### [A127749](A127749/): see A127750

Lean: [full proof](A127750/A127750_mathlib.lean).

### [A127750](A127750/): row sums mod 2 are the Fredholm-Rueppel sequence

**Source.** [A127749](https://oeis.org/A127749) (Paul Barry, Jan 28 2007): "Inverse of number
triangle A(n,k) = 1/(2n+1) if k <= n <= 2k, 0 otherwise." Comment: "Conjectures: row sums modulo 2
are the Fredholm-Rueppel sequence A036987; row sums of triangle modulo 2 are A111982. Row sums are
A127750." [A127750](https://oeis.org/A127750): row sums of A127749; "Conjecture: a(n) mod 2 gives
Fredholm-Rueppel sequence A036987" (verified to n = 2048 by A. Karttunen, 2018). R. J. Mathar (2021)
notes A127749(n,k) = (2k+1) A111967(n,k), A111967 the inverse of the 0/1 triangle
[k <= n <= 2k] (A101688), and that the first conjecture is equivalent to the conjectured row sums
of A111967. (OEIS text CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** A036987(n) = 1 if n = 2^m - 1, else 0. "Row sums of triangle modulo 2" = the sum over
k of (A127749(n,k) mod 2), compared with A111982(n) = sum over k of |A111967(n,k)|.

**Result.** Both conjectures are true, and so is the A111967 row-sum conjecture: the row sums of
A111967 are exactly A036987, and every entry of A111967 is -1, 0 or 1.

**Argument.** Let M(n,k) = [k <= n <= 2k]. Its inverse t (A111967) satisfies, for each column k,
sum_{j = ceil(n/2)..n} t(j,k) = [n = k]. Comparing the windows for n and n - 1 gives the recursion
t(n,k) = [n = k] - [n - 1 = k] + [n odd] t((n-1)/2, k), t(0,k) = [k = 0]. Hence t is lower
triangular, column k reads 1 at row k, -1 at row k + 1 (k > 0), and below that copies
t(n,k) = t((n-1)/2,k) for odd n and 0 for even n; so all entries are -1, 0, 1. Row sums
R(n) = sum_k t(n,k) satisfy R(0) = 1, R(n) = [n odd] R((n-1)/2), so R(n) = 1 exactly when
n + 1 is a power of 2. A127749 = t times diag(2k+1) (inverse of diag(1/(2n+1)) M), so
A127750(n) = R(n) + 2 sum_k k t(n,k) ≡ R(n) (mod 2), and (2k+1) t(n,k) mod 2 = |t(n,k)|.

Lean: [full proof](A127750/A127750_mathlib.lean).

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

### [A131262](A131262/): least k with A130654(k) = n equals sigma(2^n) phi(2^n)

**Source.** [A131262](https://oeis.org/A131262) (Adamchuk, 2007): a(n) = least index k with A130654(k) = n, where
A130654(k) is the exponent of 2 in A092505(k) = A002430(k)/A046990(k) (numerators of the Taylor coefficients of
tan x and of log(1/cos x)). Conjecture in the entry: a(n) = sigma(2^n) phi(2^n) = 2^(2n) - floor(2^n/2).
(OEIS text checked 2026-11-06; still marked conjecture; A130654 notes records at 1, 3, 14, 60, 248, 1008, ...
"strongly suggesting" the formula, Karttunen 2019.)

**Reading.** A130654(k) is read as the 2-adic valuation of A092505(k) (OEIS formula A130654 = A007814(A092505),
Karttunen). This equals the defining "m with 2^m = A092505(k)" whenever A092505(k) is a power of 2 (a separate
conjecture in A130654, true for k <= 1100 by certificate/check.py; not needed here).

**Result.** True: a(0) = 1 and a(n) = 2^(n-1)(2^(n+1) - 1) = sigma(2^n) phi(2^n) = 4^n - 2^(n-1) for n >= 1.

**Argument.** Let t_k = 2^(2k)(2^(2k) - 1)|B_(2k)|/(2k)! be the coefficient of x^(2k-1) in tan x, and
c_k = t_k/(2k) that of x^(2k) in log(1/cos x).
1. v2(B_(2k)) = -1 (von Staudt-Clausen at 2), 2^(2k) - 1 is odd, and v2((2k)!) = 2k - s2(k) (Legendre, s2 = binary
   digit sum). So v2(t_k) = s2(k) - 1 >= 0 and v2(c_k) = s2(k) - 2 - v2(k).
2. For a rational q, v2(numerator q) = max(v2 q, 0). Hence A130654(k) = v2(num t_k) - v2(num c_k)
   = min(s2(k) - 1, 1 + v2(k)).
3. A130654(k) >= n >= 1 forces 2^(n-1) | k and s2(k) >= n + 1. Write k = 2^(n-1) m; s2(m) = s2(k) >= n+1 and
   m + 1 >= 2^(s2 m), so k >= 2^(n-1)(2^(n+1) - 1). At k = 2^(n-1)(2^(n+1) - 1): v2 = n - 1, s2 = n + 1, value n.

Lean: [full proof](A131262/A131262_mathlib.lean).

### [A132089](A132089/): the first column of L^(m+1) is the row-sum sequence of L^m (L = Losanitsch's triangle)

**Source.** OEIS [A132089](https://oeis.org/A132089), triangle T = L^2 where L is Losanitsch's triangle
A034851 (G. McGarvey, Oct 2007). Comment: "Conjectures: (1) The first column equals the row sums of
Losanitsch's triangle (which equals A005418). (2) Let L^n denote the n-th power of Losanitsch's triangle. Then
the first column of L^(n+1) equals the row sums of L^n." (OEIS text, CC BY-SA 4.0, revision #2 of Mar 30 2012,
still conjecture on 2026-11-06.)

**Reading.** L(n, k) = (C(n, k) + C(n mod 2, k mod 2) C(⌊n/2⌋, ⌊k/2⌋))/2, rows and columns from 0 (the entry's
PARI program). L is lower triangular, so powers are well defined as infinite matrices and agree with the
entry's truncated s × s computation.

**Result.** True, both parts; (1) is (2) with power 1. The identification "row sums of L = A005418" in (1) is
the known name of A005418 (Losanitsch).

**Argument.** L(j, 0) = (1 + 1·1)/2 = 1 for every j. So L^(m+1)(n, 0) = sum_j L^m(n, j) L(j, 0) =
sum_j L^m(n, j), the n-th row sum of L^m.

Lean: [full proof](A132089/A132089.lean).

### [A132827](A132827/): the array is the dispersion of floor(n*phi + n + 1); the entry's FORMULA is wrong from row 4

**Source.** [A132827](https://oeis.org/A132827) (offset 0, keywords tabl, uned): "Table based upon insertion points
of n into sequence A132828 and having a specific formula", read by antidiagonals, 36 data terms 1, 3, 2, 8, 6, 4,
21, 16, 11, 5, 55, 42, 29, 14, 7, ... The FORMULA line reads A(i,j) = (b(i)+1)*F(2j) + (i-b(i))*F(2j+1) with
b = A005206 (Hofstadter G). Conjecture (Clark Kimberling, Jun 03 2011): the array is the dispersion of
f(n) = floor(n*x + n + 1), x the golden ratio. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** The insertion construction through [A132828](https://oeis.org/A132828) is not well defined (A132828
says "I am not certain this sequence is accurate"; A132827 says "I had an error in the program"), so the array is
taken to be what the entry lists: the 36 data terms, rows i >= 0, columns j >= 1, read by antidiagonals
(row 0 is 1, 3, 8, 21, 55, ...; column 1 is 1, 2, 4, 5, 7, 9, 10, 12). Dispersion as in
[A191426](https://oeis.org/A191426): with t the complement of {f(n) : n >= 1} in the positive integers, listed
increasingly, row i is t(i), f(t(i)), f(f(t(i))), ...

**Result.** - True. The dispersion D of f satisfies D(i,j) = (b(i)+1) F(2j) + (i - b(i)) F(2j+1) for all i >= 0, j >= 1, with
  b(i) = 2i - floor(i*phi) = i - floor(i/phi) (0, 1, 1, 2, 2, 2, 3, 3, 4, ...), and its first 36 antidiagonal
  terms are the entry's data.
- The entry's FORMULA with b = A005206 is wrong for every row i >= 4: it gives A(4,1) = 6, the data have 7. With
  b(i) = i - floor(i/phi) in place of A005206 it is correct.

**Argument.** f(n) = floor(n*phi) + n + 1 = floor(n*phi^2) + 1. By Rayleigh's theorem (1/phi + 1/phi^2 = 1) the
sets {floor(n*phi)} and {floor(n*phi^2)} (n >= 1) partition the positive integers, so the complement of the range
of f is {1} together with {floor(i*phi) + 1 : i >= 1}, i.e. t(i) = floor(i*phi) + 1. Put a = floor(i*phi),
p = b(i) + 1 = 2i - a + 1, q = i - b(i) = a - i, X_j = p F(2j) + q F(2j+1). Then X_1 = p + 2q = a + 1 = t(i).
From F(m+2) - F(m) - phi F(m) = F(m+1) - phi F(m) = psi^m (psi = 1 - phi = -1/phi):
X_{j+1} - X_j - phi X_j = psi^(2j) (p + q psi) = e. From a <= i*phi < a + 1 one gets 1 <= p + q psi =
i + 1 - (a - i) phi < phi^2, and 0 < psi^(2j) <= psi^2 = 1/phi^2, so 0 < e < 1. Hence floor(phi X_j) =
X_{j+1} - X_j - 1 and f(X_j) = X_{j+1}: the closed form is the dispersion. For the FORMULA: A005206(i) =
floor((i+1)/phi) while b(i) = ceil(i/phi^2), and these agree only for i <= 3; D(i,1) = 2i - b(i) + 1 is
strictly decreasing in b, so every row i >= 4 is wrong.

Lean: [full proof](A132827/A132827_mathlib.lean).

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

### [A138808](A138808/): the row sums of A010766 are upper bounds

**Source.** [A138808](https://oeis.org/A138808) (Jonas Wallgren, May 16 2008): "Number of integer
pairs (x,y), x > 0, y > 0, such that x <= p, y <= q for any factorization n = p*q." Comment:
"Conjecture: the row sums of the plane partitions A010766 are upper bounds. - R. J. Mathar, Aug 06
2008". [A010766](https://oeis.org/A010766): row n is floor(n/k), k = 1..n. (OEIS text CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** "for any factorization" means "for some factorization" (the example a(8) = 20 is the
union of the rectangles 1 x 8, 2 x 4, 4 x 2, 8 x 1). The conjecture: a(n) <= sum_{k=1..n} floor(n/k)
(= A006218(n)).

**Result.** True for every n >= 1.

**Argument.** If x <= p, y <= q and pq = n then xy <= n. So every counted pair lies in
{(x,y) : x, y >= 1, xy <= n}, which has sum_{x=1..n} floor(n/x) elements (for fixed x the y are
1..floor(n/x)).

Lean: [full proof](A138808/A138808_mathlib.lean).

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

### [A141419](A141419/): diagonal of S_N^T S_N (Chebyshev U sums) equals the triangle

**Source.** [A141419](https://oeis.org/A141419) (Roger L. Bagula, Aug 05 2008): "Triangle read by rows: T(n, k) =
A000217(n) - A000217(n - k) with 1 <= k <= n." Comment by L. Edson Jeffery (Jan 20 2012): "Conjecture. Let N=2*n+1
and k=1,...,n. ... Then t(n,k) = [X_N]_(k-1,k-1) ... Hence t(n,k) is the sum of squares t(n,k) =
sum[m=1,...,n (U_(k-1)(cos((2*m-1)*Pi/N)))^2]." (OEIS text, CC BY-SA 4.0, revision #105 of Sep 17 2026, checked
2026-11-06.)

**Reading.** The conjecture is the identity for the diagonal entries; X_N = S_N^T S_N has (k-1, k-1) entry
Σ_m U_{k-1}(cos θ_m)^2 by definition. The closing remark about A057059 (X_N as a combination of unit-primitive
matrices) is a separate statement and is not treated here.

**Result.** True: Σ_{m=1}^{n} U_{k-1}(cos((2m−1)π/N))^2 = k(2n−k+1)/2 = T(n, k) for 1 ≤ k ≤ n.

**Argument.** With θ_m = (2m−1)π/N, U_{k-1}(cos θ) = sin(kθ)/sin θ, so the sum is g(k) = Σ_m sin²(kθ_m)/sin²θ_m.
The identity sin²((k+1)θ) − 2 sin²(kθ) + sin²((k−1)θ) = 2 cos(2kθ) sin²θ gives g(k+1) − 2g(k) + g(k−1) =
2 Σ_m cos(2kθ_m), and the telescoping 2 sin α Σ_{m<n} cos((2m+1)α) = sin(2nα) with α = 2kπ/N (so 2nα = 2kπ − α,
sin α ≠ 0 for 0 < k < N) gives Σ_m cos(2kθ_m) = −1/2. With g(0) = 0, g(1) = n: g(k) = nk − k(k−1)/2.

Lean: [full proof](A141419/A141419_mathlib.lean).

### [A141459](A141459/): denominators of ∫_0^1 log(1 - 1/x)^n dx

**Source.** [A141459](https://oeis.org/A141459): a(n) = Π_{p odd prime, p-1 | n} p (a(0) = 1). Comment:
"Conjecture: a(n) = denominator of integral_{0..1}(log(1-1/x)^n) dx" (J.-F. Alcover, Feb 01 2013).
[A211163](https://oeis.org/A211163) (J.-F. Alcover, Jan 30 2013): numerator of
(-1/Pi^n) * integral_{0..1} (log(1-1/x)^n) dx, n ≥ 2; "Conjecture: sequence of denominators is A141459."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** On (0,1), 1 - 1/x < 0, so log is the principal complex logarithm (the reading behind the
entries' data: for n = 2 the integral is -2π²/3). The integral is a rational multiple of (πi)^n, and
"denominator" is the denominator of that rational; for A211163 it is the denominator of the rational
number (-1/π^n)·∫ (which is 0 for odd n ≥ 3).

**Result.** True: ∫_0^1 log(1 - 1/x)^n dx = 2^n B'_n (πi)^n for all n ≥ 0 (B'_n the Bernoulli numbers
with B'_1 = +1/2), and den(2^n B'_n) = A141459(n). Hence both conjectures hold (A211163 for n ≥ 2, where
(-1/π^n)·∫ = -2^n B'_n i^n is rational).

**Argument.** 1. With x = 1/(1+e^t), 1 - 1/x = -e^t and log(-e^t) = t + πi, so the integral is
   ∫_ℝ ρ(t)(t + πi)^n dt with ρ(t) = e^t/(1+e^t)^2 (logistic density).
2. Moments μ_j = ∫ ρ t^j: μ_0 = 1, μ_odd = 0 (ρ is even), and for j = 2k ≥ 2,
   μ_2k = 2∫_0^∞ ρ(s) s^2k ds = 2 Σ_m (-1)^(m+1) m ∫_0^∞ s^2k e^(-ms) ds = 2 (2k)! η(2k)
   = (-1)^(k+1)(2^2k - 2) π^2k B_2k (η(2k) = (1 - 2^(1-2k)) ζ(2k)). In one formula,
   μ_j = -(2^j - 2) B'_j (πi)^j.
3. Binomial expansion: ∫ = (πi)^n Σ_j C(n,j)(2 - 2^j) B'_j, and Σ_j C(n,j)(2 - 2^j) B'_j = 2^n B'_n
   (exponential generating functions: e^x(2B'(x) - B'(2x)) = B'(2x) with B'(x) = x e^x/(e^x - 1)).
4. von Staudt–Clausen: for k ≥ 1 the denominator of B_2k is Π_{p-1 | 2k} p, each prime once; the
   factor 2^2k removes p = 2 and leaves the odd primes. For odd n ≥ 3, B'_n = 0 (denominator 1, and no
   odd p has p - 1 | n); n = 0, 1 give 1.

Lean: [full proof](A141459/A141459_mathlib.lean).

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

### [A155005](A155005/): a(5+5n) = 1125*10^n for n > 0

**Source.** [A155005](https://oeis.org/A155005), "Smallest number having exactly n divisors that are contained in
its decimal representation" (Reinhard Zumkeller, 2009). "Conjecture: a(5+5n)=1125*10^n for n>0. [Robert G.
Wilson v, Jan 23 2009]" (OEIS text, CC BY-SA 4.0, revision #7, checked 2026-11-06.)

**Reading.** A121041(m) = number of divisors d of m whose decimal string is a contiguous substring of that of m;
a(n) = least m with A121041(m) = n. This reproduces the entry's examples (A121041(110) = 4 etc.).

**Result.** False. It holds for n = 1, 2 (a(10) = 11250, a(15) = 112500, in the entry's data) and fails at n = 3:
A121041(1125000) = 19, so a(20) is not 1125000. The entry's own data list a(19) = 1125000 and a(20) = 3124800.

**Argument.** 1125000 = 2^3 * 3^2 * 5^6 has 84 divisors; exactly 19 of them occur in the string "1125000":
1, 2, 5, 12, 25, 50, 125, 250, 500, 1125, 1250, 2500, 5000, 11250, 12500, 25000, 112500, 125000, 1125000.
Since a(20) has exactly 20 such divisors, a(20) != 1125000. (Numerically A121041(1125*10^k) = 4k + 7 for
k = 2..8, which equals 5k + 5 only at k = 2, so the pattern does not recover later.)

Lean: [full proof](A155005/A155005_mathlib.lean).

### [A156833](A156833/): for n > 1, a(n) = n iff n is prime

Lean: [full proof](A156834/A156834_mathlib.lean).

### [A156834](A156834/): for n > 1, a(n) = n iff n is prime

**Source.** [A156834](https://oeis.org/A156834) = A156348 * A000010 and [A156833](https://oeis.org/A156833) =
A054525 * A156348 * [1, 2, 3, ...], both by Gary W. Adamson (Feb 2009). Both entries: "Conjecture: for n>1, a(n) = n
iff n is prime." A156348(n, k) = C(n/k - 2 + k, k - 1) if k | n (else 0); A054525(n, k) = mu(n/k) if k | n (else 0).
A156834 has the formula a(n) = Sum_{d|n} phi(d) C(d + n/d - 2, d - 1) (Seiichi Manyama, 2021). (OEIS text, entries
revision #20 of Jun 02 2025 and #11 of Jul 22 2025, checked 2026-11-06.)

**Result.** Both conjectures are true: for n > 1, A156834(n) >= n and A156833(n) >= n, with equality iff n is prime.

**Argument.** Write C_k(e) = C(e + k - 2, k - 1), so A156348(n, k) = C_k(n/k) for k | n.

1. *A156834.* a(n) = sum_{k | n} phi(k) C_k(n/k). Every C_k(e) >= 1 and sum_{k | n} phi(k) = n, so a(n) >= n. For
   prime p the divisors give 1 + (p - 1) = p. For composite n take k | n with 1 < k < n; then n/k >= 2 and
   C_k(n/k) >= C(k, k - 1) = k >= 2, so the term phi(k) C_k(n/k) exceeds phi(k) and a(n) > n.
2. *A156833.* a(n) = sum_{j | n} mu(n/j) sum_{k | j} k C_k(j/k). Put j = k e: a(n) = sum_{k | n} k I(k, n/k) with
   I(k, M) = sum_{e | M} mu(M/e) C_k(e). Then I(k, 1) = 1; I(1, M) = sum_{d | M} mu(d) = 0 for M > 1; and for k >= 2,
   (k - 1)! C_k(e) = e (e + 1) ... (e + k - 2) = sum_r c_r e^r with natural c_r and c_{k-1} = 1, so
   (k - 1)! I(k, M) = sum_r c_r J_r(M) with the Jordan totients J_r(M) = sum_{e | M} mu(M/e) e^r = M^r prod_{p | M}
   (1 - p^-r), which are >= 0 and > 0 for r >= 1. Hence I(k, M) > 0 for k >= 2. The k = n term gives n, the k = 1 term
   gives 0, every other term is > 0. So a(p) = p for primes and a(n) > n for composite n.

Lean: [full proof](A156834/A156834_mathlib.lean).

### [A156869](A156869/): T(2n + m, n + m) = T(2n, n) iff m >= 0

Lean: [full proof](A156870/A156870_mathlib.lean).

### [A156870](A156870/): T(2n + m, n + m) = T(2n, n) iff m >= 0

**Source.** [A156869](https://oeis.org/A156869): T(n,k) = number of nondecreasing sequences of n positive integers with
reciprocals adding up to k (1 <= k <= n). [A156870](https://oeis.org/A156870): a(n) = T(2n, n). Both entries state the
conjecture "A156869(2n + m, n + m) = a(n) if and only if m >= 0". A156869 also has the comment (F. T. Adams-Watters,
Feb 20 2009) that the diagonals are constant for n <= 2k, since such a sequence must contain a 1, and removing it gives a
sequence for (n-1, k-1). (OEIS text, checked 2026-11-06.)

**Reading.** m ranges over integers with n + m >= 1, so that T(2n+m, n+m) is an entry of the triangle.

**Result.** True in both directions: T(2n+m, n+m) = T(2n, n) for m >= 0, and T(2n+m, n+m) < T(2n, n) for m < 0.

**Argument.** Let S(N, K) be the set of sequences counted by T(N, K).
1. Prepending 1 maps S(N, K) injectively into S(N+1, K+1), so T(N, K) <= T(N+1, K+1) (all sets are finite: the least
   entry x of a sequence of length N with reciprocal sum s satisfies x <= N/s, and induct on N).
2. A sequence with no 1 has reciprocal sum at most (length)/2. So when N <= 2K every element of S(N+1, K+1) starts
   with 1, the map of step 1 is onto, and T(N+1, K+1) = T(N, K). Iterating from (2n, n) gives the "if" direction
   (this is Adams-Watters' remark).
3. For N = 2K - 1 the sequence of 2K twos lies in S(2K, K) and does not start with 1, so T(2K-1, K-1) < T(2K, K).
4. For m = -d < 0: T(2n-d, n-d) <= T(2n-1, n-1) by d-1 uses of step 1, and T(2n-1, n-1) < T(2n, n) by step 3.

Lean: [full proof](A156870/A156870_mathlib.lean).

### [A156907](A156907/): integer series

Lean: [full proof](A183241/A156907_mathlib.lean).

### [A156908](A156908/): integer series

Lean: [full proof](A183241/A156907_mathlib.lean).

### [A157308](A157308/): a(m) is odd iff m = 0 or m is a power of 2

**Source.** [A157308](https://oeis.org/A157308) (Paul D. Hanna): g.f. A(x) with F(x) = A(x F(x)), F the g.f. of
[A155585](https://oeis.org/A155585) (e.g.f. exp(x)/cosh(x)); also A(x) = x / serreverse(x F(x)). Conjecture in the
entry: "a(m) == 1 (mod 2) iff m is a power of 2 or m=0" (Hanna, Mar 17 2009). (OEIS text, checked 2026-11-06.)

**Reading.** The %N line describes A by a zero pattern; the formulas and both programs compute A(x) =
x/serreverse(x F(x)), i.e. A is the unique series with A(x F(x)) = F(x). That is the definition used. It reproduces
the data (certificate/check.py, 28 terms).

**Result.** True.

**Argument.** Work mod 2.
1. F(x) = 1 + x (mod 2). From cosh(x) E(x) = exp(x): sum_{j even} C(n,j) f(n-j) = 1. By induction f(i) is odd only for
   i <= 1, so for n >= 2 the recurrence gives f(n) = 1 + [n even] + n [n odd] = 0 (mod 2).
2. Hence A(x + x^2) = 1 + x over GF(2). Put B = A - 1, so B(x + x^2) = x, and B is determined (x + x^2 has a
   compositional inverse).
3. T(x) = sum_{k>=0} x^(2^k) solves it: by Frobenius, T(x + x^2) = sum_k (x^(2^k) + x^(2^(k+1))) = x (telescoping).
   So A = 1 + T (mod 2), which is the claim.
Coefficientwise (the form checked in Lean): sum_{m<=n} a(m) C(m, n-m) = [n <= 1] mod 2, a triangular system, and
b(m) = [m = 0 or m = 2^k] solves it because C(2^k, j) is even for 0 < j < 2^k.

Lean: [full proof](A157308/A157308_mathlib.lean).

### [A157675](A157675/): integer series

Lean: [full proof](A183241/A157675_mathlib.lean).

### [A158233](A158233/): the terms are only 0, 3, 4, 6

**Source.** [A158233](https://oeis.org/A158233) (offset 1), Paul Curtz, Mar 14 2009, edited by R. J. Mathar:
"a(n) = A120070(n+1)*A120070(n+2) mod 9." Comment: "Conjecture: this contains only the numbers 0,3,4,6 (verified
for the first 5000 terms)." [A120070](https://oeis.org/A120070) (offset 2) is the triangle T(m,l) = m^2 - l^2,
1 <= l <= m-1, read by rows: 3, 8, 5, 15, 12, 7, ... (OEIS text, CC BY-SA 4.0, A158233 revision #6 of Feb 03 2019,
checked 2026-11-06.)

**Reading.** A120070(i) for i >= 2 is the i-th entry of the triangle read row by row, exactly as in the entry's
Maple program (A120070flat). With this reading the entry's data a(1..105) is reproduced.

**Result.** True: a(n) is 0, 3, 4 or 6 for every n >= 1, and all four values occur. Moreover a(n) = 4 exactly when
3 does not divide the product.

**Argument.** Two consecutive terms of A120070 are either in one row, T(m,l) and T(m,l+1) with l+1 <= m-1, or the
end of row m = l+1 and the start of row l+2, that is 2l+1 and (l+2)^2 - 1 = (l+1)(l+3).
- Across rows: (2l+1)(l+1)(l+3) is divisible by 3 (if l = 0 mod 3 then 3 | l+3, if l = 2 then 3 | l+1, if
  l = 1 then 3 | 2l+1). So the residue mod 9 is 0, 3 or 6.
- In a row: if 3 divides (m^2 - l^2)(m^2 - (l+1)^2), the residue is 0, 3 or 6. Otherwise m^2 differs mod 3 from
  both l^2 and (l+1)^2. Squares mod 3 are 0 or 1, so l^2 = (l+1)^2 mod 3, forcing l = 1 mod 3 and then m = 0 mod 3.
  Then the product is l^2 (l+1)^2 = (l(l+1))^2 mod 9, and l(l+1) = 2 mod 9 for l = 1, 4, 7 mod 9, so the residue is 4.

Lean: [full proof](A158233/A158233_mathlib.lean).

### [A160217](A160217/): every greedy start m merges with A160217

**Source.** [A160217](https://oeis.org/A160217) (Vladimir Shevelev, May 04 2009): "Minimal increasing sequence with
a(1)=3 and the property that a(n) and n are both in or both not in A003159." Comment: "Conjecture: Let m>3 belong
to A003159. Define the sequence b(n) to be the minimal increasing sequence with b(1)=m and the property that b(n)
and n are both in or both not in A003159. Then a(n)=b(n) for all n larger than some m-dependent minimum index."
(OEIS text, CC BY-SA 4.0, revision #15 of Dec 15 2018, checked 2026-11-06.) A003159: n whose 2-adic valuation is
even.

**Result.** True.

**Argument.** Write χ(x) = 1 if v₂(x) is even. b(n+1) is the least y > b(n) with χ(y) = χ(n+1).
1. a(n) = 2n+1 if χ(n) = 1, a(n) = 2n+2 otherwise (the formula in the entry); so a advances by 2 at χ(n)=χ(n+1)=1,
   by 3 at χ(n)=1, χ(n+1)=0, by 1 at χ(n)=0.
2. From any x with χ(x) = 1 the next member is within 2 and the next non-member within 3 (an odd number or a
   number ≡ 2 mod 4 is close by); from χ(x) = 0 (x even) the next member is x+1. Since χ(b(n)) = χ(n), b advances
   at most as much as a, so d(n) = b(n) − a(n) never increases; d ≥ 0 because the greedy step is monotone in its
   start. Hence d is eventually a constant D.
3. D odd: at an odd n, b(n) = 2n+1+D is even, so b advances by at most 1 (next step member) or 2 (b ≡ 0 mod 4,
   next step non-member), less than a. Contradiction.
4. D = 2e > 0: pick t large with χ(t) = 1 and χ(t+e) = 0 (if e = 2^f g, g odd: t = 2^f(4N+g) for f even,
   t = 2^(f+1)(2N+1) for f odd). Then z = 2(t+e) is a member, b(t) = 2t+1+2e = z+1, and b(t−1) ≤ 2t+2e = z.
   If b(t−1) < z the greedy step to b(t) would stop at z; if b(t−1) = z then χ(t−1) = 0 but χ(z) = 1. Contradiction.
So D = 0.

Lean: [full proof](A160217/A160217_mathlib.lean).

### [A163138](A163138/): exp(Σ (q^n + A)^n x^n/n) = A is an integer series for every integer q

**Source.** [A163138](https://oeis.org/A163138) (P. D. Hanna, Aug 2009), A(x) = exp(Σ_{n≥1} (2^n + A(x))^n x^n/n).
"Conjecture: if q is an integer, then A(x,q) is a power series in x with integer coefficients." for
A(x,q) = exp(Σ (q^n + A(x,q))^n x^n/n). (OEIS text, CC BY-SA 4.0, rev #2 of Mar 30 2012, read 2026-11-06.)

**Result.** True for every integer q (q = 0: Catalan numbers, q = 1: large Schröder numbers, q = 2: A163138).

**Argument.** Three-variable form: with H(t, y, x) = 1/(1 - t(y + A(x))) = exp(Σ_n t^n (y + A)^n/n), the
log of A equals Φ(log H) where Φ is the linear map t^n y^r x^s ↦ q^(nr) x^(n+s): indeed
(y + A)^n = Σ_r C(n,r) y^r A^(n-r) and (q^n + A)^n = Σ_r C(n,r) q^(nr) A^(n-r). Monomials of H have r ≤ n and
n ≥ 1, so finitely many lie below any x-degree n+s; c(n, r) = nr is quadratic: c(jv) = j^2 c(v) ≥ 0.
If A is integral up to degree N-1, so is H (in the relevant range), and H = Π_v (1 - T^v)^(e_v), e_v ∈ ℤ.
Then exp(Φ log H) = Π_v E_v^(-e_v), E_v = exp(Σ_j q^(j^2 c_v) z^j/j) with z = x^(n_v + s_v). Each E_v is
integral by Dwork: β(j) = q^(c j^2) satisfies β(m p^a) ≡ β(m p^(a-1)) (mod p^a) (p ∤ q: Euler, since
φ(p^a) | c m^2 p^(2a-2)(p^2-1); p | q, c ≥ 1: both terms divisible by p^(p^(2a-2)) and p^(2a-2) ≥ a;
c = 0: constant). The degree-N coefficient of A depends only on lower coefficients, so A is integral by
induction. (Same lemma as in [../A183241/README.md](A183241/README.md), item 4.)

Lean: [full proof](A163138/A163138_mathlib.lean).

### [A163921](A163921/): G(x) = exp(Σ G(L(n) x)^n x^n/n) is integral whenever exp(Σ L(n) x^n/n) is

**Source.** [A163921](https://oeis.org/A163921) (P. D. Hanna, Sep 2009), g.f. A(x) = exp(Σ A(σ(n) x)^n x^n/n).
"Conjecture: if F(x) = exp( Sum_{n>=1} L(n)*x^n/n ) is an integer series, then the g.f. that satisfies:
G(x) = exp( Sum_{n>=1} G( L(n)*x )^n*x^n/n ) is also an integer series." (OEIS text, CC BY-SA 4.0, rev #2
of Mar 30 2012, read 2026-11-06.)

**Result.** True for every such L. A163921 (L = σ, with
exp(Σ σ(n) x^n/n) = Π_k (1 - x^k)^(-1)) and A157675 (L = 2^n) are special cases.

**Argument.** 1. F ∈ 1 + xℤ[[x]] ⟺ L(n) ∈ ℤ satisfies the Gauss congruences L(m p^a) ≡ L(m p^(a-1)) (mod p^a) (Dwork).
2. log G = Φ(log H) with H(x, y) = 1/(1 - y x G(x)) = exp(Σ_n y^n (xG)^n/n) and Φ the linear map
   x^m y^n ↦ L(n)^(m-n) x^m (m ≥ n ≥ 1), since [x^m](x G(L(n) x))^n = L(n)^(m-n) [x^m](A163921/xG)^n.
3. Suppose G is integral up to degree N-1; then so is H, and H = Π_{(m,n)} (1 - x^m y^n)^(e_(m,n)) with
   e ∈ ℤ. Group by primitive w = (m0, n0): log H = -Σ e_v Σ_j x^(jm) y^(jn)/j, and
   Φ(Σ_j x^(jm) y^(jn)/j) = Σ_j u(j)^(jc) x^(jm)/j with u(j) = L(jn), c = m - n ≥ 0.
4. β(j) = u(j)^(jc) satisfies Gauss congruences: u does (subsequence of L). Let M = m p^(a-1), N = m p^a.
   c = 0: β ≡ 1. If p ∤ u(M): u(N) ≡ u(M) (mod p^a) gives u(N)^(Nc) ≡ u(M)^(Nc), and
   u(M)^((N-M)c) ≡ 1 since φ(p^a) | m p^(a-1)(p-1)c. If p | u(M): p | u(N), and Mc ≥ p^(a-1) ≥ a, so both
   terms are ≡ 0 (mod p^a).
5. So each exp(Φ(Σ_j ...)) lies in ℤ[[x]] (Dwork), and exp(Φ log H) = Π_v E_v^(-e_v) is integral; its degree-N
   coefficient depends only on G below degree N, so G is integral up to degree N. Induction.

Lean: [full proof](A163921/A163921_mathlib.lean).

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

### [A165460](A165460/): Jacobi-bridge conjecture

Lean: [full proof](A165463/A165463_mathlib.lean).

### [A165462](A165462/): Jacobi-bridge conjecture

Lean: [full proof](A165463/A165463_mathlib.lean).

### [A165463](A165463/): Jacobi-bridge heights at the 1/3 and 1/2 points

**Source.** Antti Karttunen, Oct 2009 (OEIS text, CC BY-SA 4.0, checked 2026-11-06):
- [A165460](https://oeis.org/A165460)(n) = Sum_{i=0..4n+2} J(i, 12n+7) (J = Jacobi symbol). "Conjecture: a(2n) =
  2*A165605(2n) and a(2n+1) = (2/3)*A165605(2n+1)", where [A165605](https://oeis.org/A165605)(n) =
  [A165601](https://oeis.org/A165601)(3n+1) and A165601(n) = Sum_{i=0..2n+1} J(i, 4n+3).
- [A165462](https://oeis.org/A165462)(n) = (A165463(n) - 3)/4. "Conjecture: These are all those terms of A165602
  which = 1 modulo 3." ([A165602](https://oeis.org/A165602) = positions of zeros of A165601.)
- [A165463](https://oeis.org/A165463): numbers 12n+7 with A165460(n) = 0. "Conjecture: a subset of A165603."
  ([A165603](https://oeis.org/A165603) = numbers 4n+3 whose A165601 value is 0.)

**Result.** All three conjectures are true. With m = 12n+7, B = Sum_{i <= (m-1)/3} J(i, m) and
A = Sum_{i <= (m-1)/2} J(i, m): B = 2A if m = 7 (mod 24) (n even) and 3B = 2A if m = 19 (mod 24) (n odd). So
B = 0 iff A = 0, which gives A165462 and A165463.

**Argument.** Fix m = 7 (mod 12) and chi(i) = J(i, m): completely multiplicative, periodic mod m, chi(0) = 0, and
chi(m - i) = -chi(i) since m = 3 (mod 4). Let T = Sum_{0<=i<m} i chi(i).
1. For k coprime to m, i -> k i mod m permutes [0, m), and k i = (k i mod m) + m floor(k i/m). Multiplying T by
   k chi(k) and reindexing gives k chi(k) T = T + m chi(k) Sum_{i<m} floor(k i/m) chi(i).
2. Reflection i -> m - i gives Sum_{i<m} chi(i) = 0, Sum_{2i>m} chi(i) = -A and Sum_{3i>2m} chi(i) = -B. Hence
   Sum floor(2i/m) chi(i) = -A and Sum floor(3i/m) chi(i) = Sum_{3i>m} chi + Sum_{3i>2m} chi = (0 - B) + (-B) = -2B.
3. chi(3) = -J(m, 3) = -1 (reciprocity, both 3 mod 4; m = 1 mod 3), so k = 3 gives -4T = 2mB. chi(2) = 1 if
   m = 7 (mod 8) and -1 if m = 3 (mod 8); k = 2 gives T = -mA, respectively 3T = -mA. Eliminating T: B = 2A,
   respectively 3B = 2A. m = 12n+7 is 7 mod 8 iff n is even.

Lean: [full proof](A165463/A165463_mathlib.lean).

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

### [A165886](A165886/): a(n)/A141459(n+1) = A006519(n+1)

**Source.** [A165886](https://oeis.org/A165886) (Paul Curtz, Sep 29 2009): a(n) = A165641(n+1)/A165641(n), where
A165641(n) = A091137(n)/A001316(n), A091137(n) = Π_{p prime, p ≤ n+1} p^⌊n/(p-1)⌋ (Hirzebruch numbers) and
A001316(n) = 2^(binary weight of n). Comment: "Conjecture: a(n)/A141459(n+1) = A006519(n+1)", with "correct at least
up to n<=2000" (R. J. Mathar, 2011). A141459(m) = product of the odd primes p with p - 1 | m; A006519(m) = highest
power of 2 dividing m. (OEIS text, CC BY-SA 4.0, revision #12 of Dec 19 2018, checked 2026-11-06.)

**Result.** True for every n ≥ 0: a(n) = A141459(n+1) · A006519(n+1).

**Argument.** 1. ⌊(n+1)/d⌋ - ⌊n/d⌋ is 1 if d | n+1 and 0 otherwise. With d = p - 1 (and the new prime p = n+2, whose exponent
   for n is 0), A091137(n+1)/A091137(n) = Π_{p prime, p-1 | n+1} p = 2 · A141459(n+1) (p = 2 always occurs).
2. Adding 1 to n turns the v₂(n+1) trailing ones of n into zeros and sets one bit, so s(n) + 1 = s(n+1) + v₂(n+1) for the binary
   weight s (induction: n = 2k gives s(2k) + 1 = s(2k+1); n = 2k+1 reduces to k). So
   A001316(n)/A001316(n+1) = 2^(v₂(n+1) - 1).
3. a(n) = 2 · A141459(n+1) · 2^(v₂(n+1) - 1) = A141459(n+1) · A006519(n+1).

Lean: [full proof](A165886/A165886_mathlib.lean).

### [A165940](A165940/): integer series

Lean: [full proof](A183241/A165940_mathlib.lean).

### [A166102](A166102/): a(n) = 3·A166103(n)

Lean: [full proof](A166103/A166103_mathlib.lean).

### [A166103](A166103/): odd k with k ∤ Σ{i ≤ k : J(i,k) = 1} are exactly 3·m², m ∈ A166104

**Source.** [A166102](https://oeis.org/A166102) (Antti Karttunen, 2009): odd numbers k such that A166100((k−1)/2)/k is
not an integer, where A166100(n) is the sum of those i ≤ 2n+1 with Jacobi symbol J(i, 2n+1) = +1. Comment:
"Conjecture: a(n) = 3*A166103(n). (Checked for terms a(1)-a(92).)" [A166103](https://oeis.org/A166103): squares of
[A166104](https://oeis.org/A166104) (numbers whose prime factors are all ≡ 3 or 5 mod 6); comment "Conjecture:
a(n)=A166102(n)/3." (OEIS text, CC BY-SA 4.0, A166102 revision #7 of Sep 16 2018, checked 2026-11-06.)

**Reading.** S(k) = Σ_{1≤i≤k, J(i,k)=1} i for odd k. The conjecture says: k ∤ S(k) iff k = 3m² with m odd and every
prime factor of m equal to 3 or ≡ 5 (mod 6); both sequences are increasing, so this set equality is the claim.

**Result.** True.

**Argument.** Let R = {i ≤ k : J(i,k) = 1}; J(·,k) is a multiplicative function of i mod k.
1. If J(u,k) = 1 then i ↦ ui permutes R mod k, so uS ≡ S (mod k). With u = 4: k | 3S. So k | S when 3 ∤ k, and in
   general k | S as soon as some u with J(u,k) = 1 has u ≡ 2 (mod 3) (then (u−1)S ≡ 0 and 3S ≡ 0 with
   gcd(u−1, 3) = 1).
2. Let 3 | k, k = 3^e N', 3 ∤ N'. If e is even, u ≡ 2 (mod 3), u ≡ 1 (mod N') gives J(u,k) = J(u,N') = 1. If e is
   odd and N' is not a square, pick a prime p with odd exponent in N', v a non-residue mod p, v ≡ 1 mod the rest
   of N' (so J(v, N') = −1), and u ≡ 2 (mod 3), u ≡ v (mod N'): J(u,k) = J(u,3)·J(u,N') = (−1)(−1) = 1. So k | S
   unless k = 3^e n² with e odd, 3 ∤ n, i.e. k = 3m².
3. k = 3m², m = 3^a n: J(i,k) = J(i,3)·J(i,m)², so R = {i : i ≡ 1 (mod 3), gcd(i,n) = 1}, a condition periodic
   mod M = 3n. With k = M·B, B = 3^{2a}·n odd, splitting [0,k) into B blocks of length M gives
   S(k) = B·S_M + |R_M|·M·B(B−1)/2 with S_M, |R_M| the sum and size of R in [0, M). So S(k)/k = S_M/M + integer.
   Multiplying by 4 shows n | S_M; every element of R_M is ≡ 1 (mod 3), so S_M ≡ |R_M| = φ(n) (mod 3) (the shift
   i ↦ i + n spreads the units mod n evenly over the three classes mod 3). Hence k | S iff 3 | φ(n) iff n has a
   prime factor ≡ 1 (mod 3).
4. So k ∤ S(k) iff k = 3m² with every prime factor of m equal to 3 or ≡ 2 (mod 3), i.e. (m odd) ≡ 5 (mod 6):
   k = 3·A166104(j)² = 3·A166103(j). Explicitly, for k = 3^e N (e odd, N = n²):
   S(k)/k = (3^e φ(N) − Π_{p|N}(1 − (p/3)))/6.

Lean: [full proof](A166103/A166103_mathlib.lean).

### [A166268](A166268/): Jacobi-bridge height identity for m = 12n+7

**Source.** OEIS [A166268](https://oeis.org/A166268), conjecture by A. Karttunen (2009).

**Result.** True. Proved with A166273, A166271, A166270, A166269 and A166268 in
[`../A166273/`](A166273/README.md); the Lean theorem for this entry is `A166268_main` in
[`../A166273/A166273_mathlib.lean`](A166273/A166273_mathlib.lean).

Lean: [full proof](A166273/A166273_mathlib.lean).

### [A166269](A166269/): Jacobi-bridge height identity for m = 12n+7

**Source.** OEIS [A166269](https://oeis.org/A166269), conjecture by A. Karttunen (2009).

**Result.** True. Proved with A166273, A166271, A166270, A166269 and A166268 in
[`../A166273/`](A166273/README.md); the Lean theorem for this entry is `A166269_main` in
[`../A166273/A166273_mathlib.lean`](A166273/A166273_mathlib.lean).

Lean: [full proof](A166273/A166273_mathlib.lean).

### [A166270](A166270/): Jacobi-bridge height identity for m = 12n+7

**Source.** OEIS [A166270](https://oeis.org/A166270), conjecture by A. Karttunen (2009).

**Result.** True. Proved with A166273, A166271, A166270, A166269 and A166268 in
[`../A166273/`](A166273/README.md); the Lean theorem for this entry is `A166270_main` in
[`../A166273/A166273_mathlib.lean`](A166273/A166273_mathlib.lean).

Lean: [full proof](A166273/A166273_mathlib.lean).

### [A166271](A166271/): Jacobi-bridge height identity for m = 12n+7

**Source.** OEIS [A166271](https://oeis.org/A166271), conjecture by A. Karttunen (2009).

**Result.** True. Proved with A166273, A166271, A166270, A166269 and A166268 in
[`../A166273/`](A166273/README.md); the Lean theorem for this entry is `A166271_main` in
[`../A166273/A166273_mathlib.lean`](A166273/A166273_mathlib.lean).

Lean: [full proof](A166273/A166273_mathlib.lean).

### [A166272](A166272/): the reduced denominator is always 3

**Source.** [A166272](https://oeis.org/A166272) (A. Karttunen), "Numerator of A166100(A166101(n))/A166102(n)."
Comment: "Conjecture: equal to 3*A166100(A166101(n))/A166102(n), i.e. the denominator of the quotient
A166100(A166101(n))/A166102(n) in its reduced form is always 3." A166100(m) = S(2m+1), the sum of the
1 ≤ i ≤ 2m+1 with Jacobi symbol J(i, 2m+1) = 1; A166101 = the m with 2m+1 ∤ S(2m+1); A166102 = 2·A166101 + 1.
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True: for every odd k with k ∤ S(k), S(k)/k = t/3 in lowest terms with t = 3S(k)/k.

**Argument.** For odd k, J(4, k) = 1, so i ↦ 4i permutes the residues i mod k with J(i, k) = 1; hence
4S ≡ S and k | 3S (this is `dvd_three_S` of [`../A166103`](A166103/README.md), settled in the same round).
Write 3S = kt. If 3 | t then k | S, contrary to the hypothesis; so gcd(t, 3) = 1 and S/k = t/3 is reduced.

Lean: [full proof](A166272/A166272_mathlib.lean).

### [A166273](A166273/): Jacobi-bridge heights at m/6, m/3, m/2 for m = 12n+7

**Source.** OEIS bisections by A. Karttunen (Oct 2009), each with a comment "Conjecture: ...":
[A166273](https://oeis.org/A166273) a(n) = −3·A166269(n); [A166271](https://oeis.org/A166271) a(n) = −2·A166269(n);
[A166269](https://oeis.org/A166269) a(n) = −(1/2)·A166271(n); [A166270](https://oeis.org/A166270) a(n) = 2·A166268(n);
[A166268](https://oeis.org/A166268) a(n) = A166270(n)/2 and also A165605(A005843(n)). (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** For m = 12n+7 and J the Jacobi symbol: A165605(n) = A165601(3n+1) = sum_{i=0..6n+3} J(i, m),
A165460(n) = sum_{i=0..4n+2} J(i, m), A166050(n) = sum_{i=0..2n+1} J(i, m), i.e. H(x) = sum of J(i, m) over
0 ≤ i < x·m at x = 1/2, 1/3, 1/6. A166273, A166271, A166269 are the odd bisections (m ≡ 19 mod 24) of A165605,
A165460, A166050; A166270, A166268 the even bisections (m ≡ 7 mod 24) of A165460, A166050.

**Result.** All true: for m ≡ 7 (mod 24), H(1/3) = 2H(1/6) and H(1/2) = H(1/6); for m ≡ 19 (mod 24),
H(1/2) = −3H(1/6) and H(1/3) = −2H(1/6). This holds for every m in these classes, squarefree or not.

**Argument.** Let χ = J(·, m): m-periodic, completely multiplicative, χ(−1) = −1 (m ≡ 3 mod 4), χ(3) = −1
(reciprocity, m ≡ 3 mod 4 and m ≡ 1 mod 3), χ(2) = +1 for m ≡ 7 (mod 8), −1 for m ≡ 3 (mod 8). Write
m = 6q+1. The integers 1..m−1 form six blocks B_j = {jq+1, ..., (j+1)q} (j = 0..5); let a(j, r) be the sum of
χ(n) over n ∈ B_j with n ≡ r (mod 6). Then H(1/6) = sum_r a(0, r), H(1/3) adds block 1, H(1/2) adds block 2.
Three families of linear relations hold:
- reflection n ↦ m − n: a(5−j, 1−r mod 6) = −a(j, r);
- doubling n ↦ 2n (j ≤ 2) or 2n − m (j ≥ 3): χ(2)·(a(j, r) + a(j, r+3)) equals a(2j, s) + a(2j+1, s)
  (indices mod 6), s = 2r − t (mod 6), t = ⌊j/3⌋;
- tripling n ↦ 3n − t m, t = ⌊j/2⌋: χ(3)·(a(j, r) + a(j, r+2) + a(j, r+4)) equals the sum of a(3j−6t+i, s),
  i = 0, 1, 2, s = 3r − t (mod 6).
With (χ(2), χ(3)) = (1, −1) or (−1, −1), these 66 relations imply the stated identities (a linear combination of
12–16 of them; found by Gaussian elimination, checked by `linarith` in Lean). No class-number formula or
primitivity of χ is used.

Lean: [full proof](A166273/A166273_mathlib.lean).

### [A166407](A166407/): A166406(n)/(2n+1) is an integer except on A166101, where its denominator is 3

**Source.** [A166407](https://oeis.org/A166407) (offset 0): "a(n) = floor(3*(A166406(n)/A005408(n)))." Comment:
"Conjecture: the quotient A166406(i)/A005408(i) has denominator 3 when i is one of the terms of A166101, and it is
integral in other cases. If true, then floor in the formula is unnecessary." Here N = 2n+1 = A005408(n),
A166406(n) = Σ_{i≤N, J(i,N)=-1} i − Σ_{i≤N, J(i,N)=+1} i (J = Jacobi symbol), A166100(n) = Σ_{i≤N, J(i,N)=+1} i,
and A166101 lists the n with A166100(n)/N not an integer. (OEIS text, revision #14 of May 08 2021, checked
2026-11-06.)

**Result.** True. Write N = N'·m^2 with N' squarefree and B = −A166406(n)/N = (1/N) Σ_{i≤N} i·J(i,N). Then B is
an integer unless N' = 3 and every prime p ≠ 3 dividing m is ≡ 2 (mod 3); in that case B = −2^w/3 (w = number of
such primes) and n ∈ A166101. Whenever B is an integer, A166100(n)/N is an integer, so n ∉ A166101. Hence
A166101 = {n : 2n+1 = 3m^2, all prime factors p ≠ 3 of m are ≡ 2 (mod 3)} (= 1, 13, 37, 121, 181, ...).

**Argument.** χ(i) = J(i,N) is a real Dirichlet character mod N; on i coprime to N it equals the Jacobi symbol
mod N', the primitive real character of conductor N' (principal if N' = 1). B = (1/N) Σ_{a=1}^{N} a χ(a) is the
generalized Bernoulli number B_{1,χ} for nonprincipal χ.
1. *N' = 1* (N a square): B = (1/N) Σ_{(a,N)=1} a = φ(N)/2 for N > 1, and B = 1 for N = 1.
2. *χ even* (N' ≡ 1 mod 4, N' > 1): a ↦ N − a gives B = −B, so B = 0.
3. *χ odd* (N' ≡ 3 mod 4): B_{1,χ} = B_{1,χ_d} Π_{p | m, p ∤ N'} (1 − χ_d(p)) with d = −N' a fundamental
   discriminant (imprimitive characters: Washington, Cyclotomic Fields, Ch. 4), and B_{1,χ_d} = −2h(d)/w(d) (class
   number formula; w = 6 for d = −3, w = 2 for d < −4). So B ∈ ℤ unless d = −3, where B = −(1/3) Π (1 − χ_{−3}(p))
   ∈ {0, −2^w/3}; it is 0 as soon as some p ≡ 1 (mod 3) divides m.
4. *Link to A166100.* For N > 1, Σ_{(a,N)=1} a = Nφ(N)/2, so A166100(n)/N = φ(N)/4 + B/2. If B has denominator
   3, so does this. If B ∈ ℤ we need φ(N) + 2B ≡ 0 (mod 4): in case 1, B = φ(N)/2 and φ(N) + 2B = 2φ(N) ≡ 0
   (N > 2); in case 2, B = 0 and φ(N) ≡ 0 (mod 4) because N' has a prime ≡ 1 mod 4 or two primes; in case 3,
   if some p | m does not divide N' then B is even and φ(N) ≡ 0 (mod 4) (two distinct primes), and otherwise
   B = −h(−N'), which is odd when N' is prime (then N = p^k with k odd, φ(N) ≡ 2 mod 4) and even when N' has
   at least two prime factors (genus theory; then φ(N) ≡ 0 mod 4).

Lean: needs Mathlib.

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

### [A173643](A173643/): the odd-part formula needs K = 0 (counterexample 3)

**Source.** [A173643](https://oeis.org/A173643) (offset 1): "Positive numbers of form 2^m - 2^l - 3*2^k (A172233)
divisible by 9, divided by 9", with A172233 requiring m > l > k ≥ 0. Comment: "Conjecture: Odd part of a(n) is of
form [(1/6)*(8^m-(-1)^m-3)*4^k-1]/3, k,m>0." (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** The terms are (2^m − 2^l − 3·2^k)/9 with m > l > k ≥ 0, value positive and divisible by 9 (this
reproduces the 55 listed terms, certificate/check.py). Write F(M,K) = ((8^M − (−1)^M − 3)/6 · 4^K − 1)/3.

**Result.** As stated (K, M > 0) the conjecture is false: a(3) = 3 = (2^5 − 2^1 − 3)/9 has odd part 3, and
F(M,K) ≠ 3 for K, M > 0 (F(2,0) = 3). With K ≥ 0 allowed it is true. The odd parts missed by K > 0 are exactly
F(M,0) for even M: 3, 227, 14563, 932067, …, each of which is a term.

**Argument.** Put B = l − k ≥ 1, D = m − l ≥ 1. The term is 2^k·w with w = (2^B(2^D − 1) − 3)/9 odd, so w is the
odd part. Since 2^6 ≡ 1 (mod 9), 9 | 2^B(2^D − 1) − 3 iff (D ≡ 2 mod 6, B even) or (D ≡ 4 mod 6, B odd).
In the first case M = (D+1)/3 is odd, K = B/2 ≥ 1 and w = F(M,K); in the second M = (D+2)/3 is even,
K = (B−1)/2 ≥ 0 and w = F(M,K). F(M,0) for odd M is even, so it is never an odd part.

Lean: [full proof](A173643/A173643_mathlib.lean).

### [A174470](A174470/): integer series

Lean: [full proof](A183241/A174470_mathlib.lean).

### [A174846](A174846/): |a(n)/n!|^(-1/n) tends to pi/4 = 0.7853...

**Source.** OEIS [A174846](https://oeis.org/A174846) (Paul D. Hanna, Jan 24 2011): e.g.f. AGM(1, exp(4x)).
Comment: "Conjecture: limit |a(n)/n!|^(-1/n) = r exists and is finite with r<0.8..." and the question "What is the
radius of convergence of the e.g.f.?". Vaclav Kotesovec (Sep 27 2019) adds r = Pi/4 and the form
e^(4x) Pi / (2 EllipticK(1 - e^(-8x))), without a proof. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True: the limit exists and equals pi/4 = 0.78539... < 0.8. Asymptotically
a(n)/n! = -pi (4/pi)^n Re(i^(1-n)) / (n log^2 n) (1 + o(1)) for odd n, and |a(n)/n!| is of exact order
(4/pi)^n / (n^2 log^2 n) for even n.

**Argument.** Let f(x) = AGM(1, e^(4x)) with the principal AGM, analytic in z = e^(4x) on C minus (-inf, 0].
1. *Radius.* For |x| < pi/4, |Im 4x| < pi, so e^(4x) avoids (-inf, 0] and f is analytic: radius >= pi/4.
   At x0 = i pi/4, z = -1. Writing AGM(1,z) = sqrt(z) AGM(1, k') with k' = (1+z)/(2 sqrt z) and
   AGM(1,k') = pi/(2K(k)), K(k) = A(k'^2) log(4/k') + B(k'^2) with A, B analytic, A(0) = 1, B(0) = 0 (classical
   expansion of the complete elliptic integral at k' = 0), one gets near x0, with d = x - x0 and k' = 2i d (1 + O(d)),
   f(x) = (pi i / 2) / (log(-2i/d) + O(d log d)). This is not analytic at x0 (f -> 0 while f' is unbounded),
   so the radius is exactly pi/4, and limsup |a(n)/n!|^(1/n) = 4/pi.
2. *Delta-analyticity.* On the circle |x| = pi/4 only x0 and its conjugate have |Im 4x| = pi; every other point has
   a neighbourhood where the principal branch is analytic. The local form in step 1 continues to a slit
   neighbourhood of x0 (and of its conjugate). By compactness f is analytic in a Delta-domain at +-x0 of radius
   pi/4 + eta.
3. *Transfer* (Flajolet-Odlyzko, logarithmic singularities, Flajolet-Sedgewick *Analytic Combinatorics* VI.2).
   With w = x/x0, the singular part at x0 is (pi i/2) / (log(8/pi) + log(1/(1-w))) + ..., whose w^n coefficient is
   -(pi i/2)/(n log^2 n)(1 + O(1/log n)); adding the conjugate gives the odd-n formula above, with
   |Re(i^(1-n))| = 1 for odd n.
4. *Even n.* The even part of f is E(x) = f(x)(1 + e^(-4x))/2, because f(-x) = e^(-4x) f(x) (AGM is homogeneous).
   At x0, 1 + e^(-4x) = 4d + O(d^2), so E's singular part is of type (1 - w)/log(1/(1-w)), with coefficients of exact
   order (4/pi)^n/(n^2 log^2 n); the conjugate contributions do not cancel for even n (their sum is
   +- 2 pi (pi/4)^(1-n) times a real sequence of that order).
Hence |a(n)/n!|^(1/n) -> 4/pi along both parities, and r = pi/4.

Lean: needs Mathlib.

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

### [A176827](A176827/): the q-analogue a(n,q) is an integer for every positive integer q

**Source.** [A176827](https://oeis.org/A176827) (P. D. Hanna, Apr 2010): A(x,q) = Σ a(n,q) x^n/q^(n(n-1)/2)
with A(x,q) = exp(Σ_{n≥1} A(x/q^n, q)^n x^n/n). "Conjecture: {a(n,q), n>=0} are integers when q is a positive
integer." (OEIS text, CC BY-SA 4.0, rev #2 of Mar 30 2012, read 2026-11-06.) The entry's second conjecture,
a(n,q) ≡ 1 (mod q), is not treated here (it holds numerically, see Evidence).

**Result.** True: a(n,q) ∈ ℤ for all n ≥ 0 and integers q ≥ 1.

**Argument.** Write A_N = [x^N] A, so a(N,q) = q^(C(N,2)) A_N. Fix a prime p.

1. *p ∤ q.* Put r = 1/q ∈ ℤ_(p). The log of A is Φ(log G) with G(x, y) = 1/(1 - y x A(x)) and Φ the linear map
   x^m y^n ↦ r^(n(m-n)) x^m (m ≥ n), because [x^m](x A(r^n x))^n = r^(n(m-n)) [x^m](A176827/xA)^n. If A ∈ ℤ_(p)[[x]] up
   to degree N-1, then G is p-integral up to that degree; factor G = Π_v (1 - x^v y^w)^(e_v) with e_v ∈ ℤ_(p);
   then exp(Φ log G) = Π_v E_v^(-e_v), E_v(t) = exp(Σ_j r^(j^2 c_v) t^j/j) with c_v = w(v-w) ≥ 0, and
   E_v ∈ ℤ_(p)[[t]] by the Dieudonné-Dwork criterion: j ↦ r^(c j^2) satisfies r^(c m^2 p^(2a)) ≡ r^(c m^2 p^(2a-2))
   (mod p^a) (Euler for r a unit). So A_N ∈ ℤ_(p), hence a(N,q) ∈ ℤ_(p). (Same lemma as for A157675 in
   [../A183241/README.md](A183241/README.md).)
2. *p | q,* v = v_p(q) ≥ 1. Claim v_p(A_N) ≥ -v C(N,2). Induction on N. The log coefficient is
   L_N = Σ_n (1/n) Σ_{M_1+...+M_n = N-n} Π_i A_{M_i} q^(-n M_i). With K = N - n and the induction hypothesis,
   each product has valuation ≥ -v(Σ C(M_i,2) + nK), and C(N,2) = C(n,2) + nK + C(K,2) ≥ C(n,2) + nK + Σ C(M_i,2),
   so v_p(L_N) ≥ -v C(N,2) + v C(n,2) - v_p(n) ≥ -v C(N,2) (C(n,2) ≥ v_p(n) for n ≥ 1). Then
   A_N = Σ_k (1/k!) Σ_{N_1+...+N_k=N} Π L_{N_i}, and C(N,2) - Σ C(N_i,2) = Σ_{i<j} N_i N_j ≥ C(k,2) ≥ v_p(k!), so
   v_p(A_N) ≥ -v C(N,2). Hence a(N,q) ∈ ℤ_(p).

Lean: [full proof](A176827/A176827_mathlib.lean).

### [A176948](A176948/): every n >= 4 except 6 has an n-gonal number that is not k-gonal for 3 <= k < n

**Source.** [A176948](https://oeis.org/A176948) (Shevelev, 2010): a(n) = least x with A176774(x) = n, where
A176774(x) is the least k >= 3 with x k-gonal; a(n) = 0 if there is none. Conjecture in the entry: for every
n >= 4, n != 6, some n-gonal number is not k-gonal for 3 <= k < n (so a(6) = 0 is the only zero). (OEIS text
checked 2026-11-06.)

**Result.** True.

**Argument.** P_k(m) = ((k-2)m(m-1) + 2m)/2. Fix n, put a = n-2 >= 2, a != 4, and for 3 <= k < n put
b = k-2 in [1, a-1] and C = b(a-2)^2 - a(b-2)^2 = (a-b)(ab-4).
1. C != 0: a > b, and ab = 4 with b < a forces (a, b) = (4, 1), i.e. n = 6. Also |C| < n^3.
2. If N = P_n(j) = P_k(i), then with X = 2aj - (a-2), Y = 2bi - (b-2) we have 8aN + (a-2)^2 = X^2,
   8bN + (b-2)^2 = Y^2, hence a(bX^2 - C) = (aY)^2.
3. For a prime p > 3 with p not dividing abC, some x in Z/p makes a(bx^2 - C) a non-square. Otherwise
   s -> a(bs - C) maps the set S of squares (with 0) injectively into itself, so permutes it; summing over S
   and using sum_{s in S} s = (1/2) sum_x x^2 = 0 gives aC|S| = 0 in Z/p, but 0 < |S| < p.
4. Take distinct primes p_k > n^3 + 2 (k = 3..n-1), the residues x_k of step 3, and j by the Chinese remainder
   theorem with 2aj - (a-2) = x_k mod p_k. Then N = P_n(j) is n-gonal, and by step 2 it is k-gonal for no
   3 <= k < n.

Lean: [full proof](A176948/A176948_mathlib.lean).

### [A177430](A177430/): exp(sum b(n)^m x^n/n) is integral exactly for even m >= 0

**Source.** [A177431](https://oeis.org/A177431) b = 1, 3, 4, 5, 6, 12, ... and [A177430](https://oeis.org/A177430)
= b^2 (Hanna, 2010): the least increasing sequence of squares that is the logarithmic derivative of an integer
series, i.e. exp(sum b(n)^2 x^n/n) is in Z[[x]]. Conjectures: A177431, "exp(Sum a(n)^m x^n/n) consists entirely of
integer coefficients only when m is a nonnegative even integer"; A177430, "{a(n)^(m/2)} forms a logarithmic
derivative of an integer sequence only when m is a nonnegative even integer" (same statement, since
A177430(n)^(m/2) = b(n)^m). (OEIS text checked 2026-11-06.)

**Reading.** m ranges over the integers.

**Result.** True, in both directions: exp(sum b(n)^m x^n/n) is integral iff m >= 0 and m is even.

**Argument.** Integrality of exp(sum c(n) x^n/n) for integer c is equivalent to the Gauss congruences
p^a | c(m p^a) - c(m p^(a-1)) (Dwork). 
- m even >= 0: b^2 satisfies them (definition of b), and they are closed under products, so b^m = (b^2)^(m/2) does.
- m odd >= 1: at p = 2, a = 2, m' = 1 the congruence needs 4 | b(4)^m - b(2)^m = 5^m - 3^m, but 5^m - 3^m = 2
  (mod 4) for odd m. (The x^4 coefficient is not integral.)
- m < 0: the x^2 coefficient is (b(1)^2m + b(2)^m)/2 = (1 + 3^m)/2 with 0 < 3^m < 1, not an integer.

Lean: [full proof](A177430/A177430_mathlib.lean).

### [A177431](A177431/): exp(sum a(n)^m x^n/n) integral only for even m >= 0

Lean: [full proof](A177430/A177430_mathlib.lean).

### [A178473](A178473/): OEIS A178473

Lean: [full proof](A178473/A178473_mathlib.lean).

### [A178612](A178612/): no term is a square (rank-0 elliptic curve)

**Source.** [A178612](https://oeis.org/A178612) (offset 1): "Positive numbers of the form p^6 - 4*p^4*q +
4*p^2*q^2 + 4*q^3 (and p*q <> 0)." Comment: "Conjecture: There are no perfect squares in this sequence (in spite
of all numbers being congruent to 0 or 1 mod 4)." A square would give a septic trinomial x^7 + Ax^2 + B with
irreducible factors of degrees 3 and 4. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True: F(p,q) = p^6 − 4p^4q + 4p^2q^2 + 4q^3 is never a perfect square for integers p, q ≠ 0.

**Argument.** If F(p,q) = y^2 with p ≠ 0, put x = 4q/p^2, Y = 4y/p^3. Dividing by p^6 and multiplying by 16 gives
Y^2 = x^3 + 4x^2 − 16x + 16, an elliptic curve E of conductor 35 (minimal model y^2 + y = x^3 + x^2 − x, isogeny
class 35.a). E(Q) has rank 0 (2-descent: PARI/GP `ellrank` gives bounds [0, 0]; also L(E,1) ≈ 0.7029 ≠ 0) and
torsion Z/3 generated by (0, 4). So E(Q) = {O, (0, 4), (0, −4)}, hence x = 0, i.e. q = 0.

Lean: [checked](A178612/A178612_mathlib.lean).

### [A179873](A179873/): nondecreasing sequence of odd numbers

Lean: [full proof](A179874/A179874_mathlib.lean).

### [A179874](A179874/): integral antiharmonic means of the units mod h are odd and nondecreasing

**Source.** [A179873](https://oeis.org/A179873) (Jaroslav Krizek, 2010): values of the antiharmonic mean
B(h) = Σk²/Σk over the k < h with gcd(k, h) = 1, for the h with B(h) an integer ([A179871](https://oeis.org/A179871)).
Comment: "Conjecture: nondecreasing sequence of odd numbers." [A179874](https://oeis.org/A179874): "Possible values of
A179873(m) in increasing order"; comment: "Conjecture: a(n) = sequence of odd numbers." (OEIS text, CC BY-SA 4.0,
A179873 revision #21 of May 25 2025, A179874 revision #10 of Jan 09 2025, checked 2026-11-06.)

**Reading.** B(h) is taken over 1 ≤ k ≤ h with gcd(k,h) = 1 (for h ≥ 2 the same as k < h; for h = 1 this gives
B(1) = 1, the entry's first term). "Sequence of odd numbers" means every term is odd (A179874 omits 5, 9, ...).

**Result.** Both true: whenever B(h) is an integer, 3B(h) = 2h ± 1, so B(h) is odd, and B is nondecreasing along
A179871. More precisely B(h) ∈ ℤ iff h is squarefree and B(h) = (2h + (−1)^ω(h))/3 is an integer.

Side note: A179874's data lists 151 twice ("..., 145, 151, 151, 153, ..."); the distinct values contain 151 once and
otherwise agree with the data.

**Argument.** 1. For n ≥ 2, Σ_{units} k = nφ(n)/2 and Σ_{units} k² = (2n²φ(n) + n·Π_{p|n}(1−p))/6 (Möbius inversion of
   Σ_{k<n} k^r = Σ_{d|n} d^r Σ_{units mod n/d} j^r, with Σ_{d|n} μ(d)d = Π(1−p); classical, see A053818).
2. So 3φ(h)B(h) = 2hφ(h) + Π(1−p), and Π(1−p) = ±Q with Q = Π(p−1). If B(h) = t ∈ ℤ then φ(h) | Q; since
   φ(h)·Πp = h·Q and Πp | h, this forces Q = φ(h) (h squarefree), and 3t = 2h ± 1.
3. 2h ± 1 is odd, so t is odd; for h < h', 3t ≤ 2h + 1 ≤ 2h' − 1 ≤ 3t'.

Lean: [full proof](A179874/A179874_mathlib.lean).

### [A179902](A179902/): the parity pattern 1, 0, 1, 1 (period 4) holds

**Source.** [A179902](https://oeis.org/A179902) (offset 1), "Row sums of triangle A179901." Comment:
"Conjectured mod 2 parity: (1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,...)." Formula by Andrew Howroyd
(Sep 21 2025): a(n) = (n^4 - 8n^3 + 35n^2 - 52n + 36)/12. [A179901](https://oeis.org/A179901):
"Triangle read by rows, antidiagonals of an array generated from (1, r, r, r, ...) convolved with
(1, 0, r, r, r, ...)." (OEIS text, CC BY-SA 4.0; A179902 revision #23 of Jul 20 2026, A179901 #14,
checked 2026-11-06.)

**Reading.** Array row r >= 1 is the coefficient list of the product of (1, r, r, ...) and
(1, 0, r, r, ...): 1, r, 2r, 2r + r^2, 2r + 2r^2, ... (column m + 1 holds 2r + r^2 (m - 2) for
m >= 2). Row n of the triangle is (A(n,1), A(n-1,2), ..., A(1,n)), as in the entry's example and
Howroyd's PARI program; this reproduces the triangle data and the A179902 data. The conjecture says
a(n) is even exactly when n = 2 (mod 4).

**Result.** True for every n >= 1: a(n) is even iff n = 2 (mod 4).

**Argument.** Coefficient m + 2 of the product is r (from 1 * r) + r (from r * 1) + 0 (from r * 0)
+ m r^2 (the middle terms), so it is 2r + r^2 m. Row n of the triangle is 1, n - 1, then
2(n - 2 - i) + (n - 2 - i)^2 i for i = 0..n - 3; summing with the power sums of i, i^2, i^3 gives
12 a(n) = n^4 - 8n^3 + 35n^2 - 52n + 36 (Howroyd's formula). Then 12(a(n+4) - a(n)) =
8(2n^3 + 19n + 12), so 3(a(n+4) - a(n)) is even and so is a(n+4) - a(n). With a(1..4) = 1, 2, 5, 11
the parities repeat 1, 0, 1, 1.

Lean: [full proof](A179902/A179902_mathlib.lean).

### [A180654](A180654/): Σ log(Σ_k C(n,k)^p x^k)^n/(n! n^n) is an integer e.g.f. (Conjectures 1-3)

**Source.** [A180654](https://oeis.org/A180654) (P. D. Hanna, Sep 2010). E.g.f. A(x) = Σ_{n≥0} log(Σ_{k=0..n} C(n,k)^2 x^k)^n
/(n! n^n). "Conjecture 1: this sequence consists entirely of integers." Conjecture 2: the same for C(n,k)^p,
every integer p ≥ 1. Conjecture 3: the same for C(n,k)^n. (OEIS text, CC BY-SA 4.0, rev #2 of Mar 30 2012,
read 2026-11-06.)

**Reading.** The %N line carries an extra factor x^n in each term; the example, the PARI program and the data
have none. The data follow the version without x^n (certificate/check_data.py). The result below holds for
both readings, because x^n = n!·(x^n/n!) is itself an integer e.g.f.

**Result.** All three conjectures are true. More generally: if P_n ∈ 1 + xℤ[x] and n divides k·[x^k]P_n for
all k, then Σ_n log(P_n)^n/(n! n^n) has integer e.g.f. coefficients.

**Argument.** Let H be the ring of integer e.g.f.s, {Σ a_N x^N/N! : a_N ∈ ℤ} (closed under products by
binomial convolution).
1. k C(n,k) = n C(n-1,k-1), so x P_n' = Σ_k k C(n,k)^p x^k = n Q_n with Q_n ∈ ℤ[x] (p ≥ 1, also p = n). Since
   P_n(0) = 1, 1/P_n ∈ ℤ[[x]], so x P_n'/P_n = n Σ d_N x^N with d_N ∈ ℤ, and
   g_n := log(P_n)/n = Σ_{N≥1} (d_N/N) x^N = Σ (N-1)! d_N x^N/N! ∈ xH.
2. For g ∈ xH, g^n/n! ∈ H: N![x^N] g^n/n! = Σ over set partitions of {1..N} into n blocks of Π_B b_{|B|}
   (b_j = j![x^j]g), an integer.
3. The n-th term log(P_n)^n/(n! n^n) = g_n^n/n! ∈ H and has x-order ≥ n, so the sum converges in H.
For p = 1, P_n = (1+x)^n gives Σ log(1+x)^n/n! = 1+x, the entry's comparison.

Lean: [full proof](A180654/A180654_mathlib.lean).

### [A180710](A180710/): sigma(n) | a(n) fails at n = 64

**Source.** [A180710](https://oeis.org/A180710) (Hanna, 2010): a(1) = 1, a(n) = sigma(2^(n-1) a(n-1)) for n > 1.
Comment: "Conjecture: sigma(n) | a(n) for n>=1." (OEIS text checked 2026-11-06; data up to a(9).)

**Result.** False. sigma(n) | a(n) holds for 1 <= n <= 63, but sigma(64) = 127 and a(64) = 43 (mod 127). a(64) has 658
digits.

**Argument.** a(n) is computed exactly through its prime factorization: if 2^(n-1) a(n-1) = prod p^e, then
a(n) = prod (p^(e+1) - 1)/(p - 1), and each factor (p^(e+1) - 1)/(p - 1) is factored separately (PARI `factor`),
the results merged. Every prime found is certified by PARI `isprime` (proven primality, APR-CL), so each step
gives the exact prime factorization of a(n) and the next sigma is exact. The first terms equal the entry's data
(and direct `sigma` evaluation for n <= 12). Reducing the factorization of a(64) modulo 127 gives 43.

Lean: —.

### [A181070](A181070/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A181074](A181074/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A181076](A181076/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A181078](A181078/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A181080](A181080/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A181082](A181082/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A181084](A181084/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A181316](A181316/): exp(Σ (q-1)((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series for every q > 1

**Source.** [A181316](https://oeis.org/A181316) (Paul D. Hanna, Oct 31 2010): g.f. A(x) = exp(Sum_{n>=1}
2*((3^n-1)/2)^(n-1)*x^n/n). "Conjecture: exp( Sum_{n>=1} (q-1)*((q^n-1)/(q-1))^(n-1)*x^n/n ) is an integer series
for all integer q>1." (OEIS text, revision #2 of Mar 30 2012, checked 2026-11-06.)

**Result.** True for every integer q >= 2.

**Argument.** Write c(n) = (q^n - 1)/(q - 1) = 1 + q + ... + q^(n-1) and b(n) = (q-1) c(n)^(n-1). By the Dold/Gauss
criterion it suffices that b(N) ≡ b(M) (mod p^a) whenever N = m p^a, M = m p^(a-1), a >= 1. Note c(N) = c(M) (1 +
q^M + ... + q^(M(p-1))), so p | c(M) implies p | c(N); and x^N ≡ x^M (mod p^a) for every integer x.
1. p ∤ c(M), p ∤ q - 1: (q - 1)(c(N) - c(M)) = q^N - q^M ≡ 0, so c(N) ≡ c(M) (mod p^a). Also c(M)^M (c(M)^(N-M) - 1)
   ≡ 0, so c(M)^(N-M) ≡ 1. Hence c(N)^(N-1) ≡ c(M)^(N-1) = c(M)^(M-1) c(M)^(N-M) ≡ c(M)^(M-1).
2. p ∤ c(M), p | q - 1: c(M) ≡ M (mod p), so p ∤ M, which forces a = 1; both b(N), b(M) contain the factor q - 1.
3. p | c(M): then M >= 2, b(N) has the factor c(N)^(N-1) with N - 1 >= a, and b(M) the factor c(M)^(M-1) with
   M - 1 >= a, except for p = 2, a = 2, M = 2; there q is odd and b(2) = (q-1)(q+1) is divisible by 4.
The Gauss congruences give integers e(d) with b(n) = Σ_{d|n} d e(d), so the series is Π_d (1 - x^d)^(-e(d)).

Lean: [full proof](A181316/A181316_mathlib.lean).

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

### [A182372](A182372/): sets with perimeter n and two-sort partitions are equinumerous

**Source.** [A182372](https://oeis.org/A182372) (offset 0): "Number of distinct sets of nonnegative integers with
perimeter n", where the perimeter of S is the sum of the elements of S whose predecessor and successor are not both
in S. Comment: "Conjecture: number of partitions of n into two sorts of parts such that no two successive parts are
the same sort (as the order of sorts in a run of identical parts is immaterial, there can be at most two parts of
same size), see example. - _Joerg Arndt_, Jun 01 2013", and "The conjecture of Arndt [namely that a(n) = A227134(n)
+ A227135(n)] has been verified for n < 1200. - _Patrick Devlin_, Jul 02 2013". (OEIS text, revision #81 of Nov 05
2025, checked 2026-11-06.)

**Reading.** Sets are finite (an infinite tail {t, t+1, ...} would add only t to the perimeter, making every a(n)
infinite), and 0 always counts as a perimeter element since -1 is not in S. A two-sort partition is a list of
pairs (part, sort), parts ≥ 1, sorts in {0, 1}, listed in increasing lexicographic order with no repeated pair,
whose sorts alternate. This is how Arndt's example lists them (a(9) = 24: [1:0 1:1 7:0] is listed, [1:0 1:1 7:1] is
not), and it splits by first sort into A227134 (first sort 0) and A227135 (first sort 1). The empty partition is
counted once here and once in each of A227134, A227135; the empty set is counted in a(0) = 2.

**Result.** True: for every n ≥ 0, the number of nonempty finite sets S ⊆ ℕ with perimeter n equals the number
of two-sort partitions of n. Hence a(n) = (two-sort partitions of n) for n ≥ 1, a(0) = 2, and
a(n) = A227134(n) + A227135(n) for all n ≥ 0.

**Argument.** Let Y_m(n) count sequences 0 ≤ y_1 < y_2 ≤ y_3 < y_4 ≤ ... of length m and sum n (strict after
odd positions, weak after even ones). Its generating function is x^Q(m)/(x;x)_m with Q(m) = floor(m^2/4). Both
sides equal Σ_{m≥1} Y_m(n).

1. *Two-sort partitions.* In the lexicographic listing, equal neighbouring parts carry sorts (0, 1), so the list
   p_1 ≤ ... ≤ p_k is weakly increasing after a part of sort 0 and strictly increasing after a part of sort 1. If
   the first sort is 1, the list is strict after odd positions: it is a Y_k sequence with y_1 ≥ 1. If the first
   sort is 0, prepend y_1 = 0: (0, p_1, ..., p_k) is a Y_{k+1} sequence with y_1 = 0. Every Y_m sequence arises
   once, except (0) of length 1, which corresponds to the empty partition. So
   #(two-sort partitions of n) = Σ_{m≥1} Y_m(n) for every n ≥ 0.
2. *Sets, one shape at a time.* A nonempty set is a union of b ≥ 1 maximal runs; let L ⊆ {1..b} be the runs of
   length ≥ 2. Its perimeter elements are the run ends: k = b + |L| numbers e_1 < ... < e_k with Σ e = perimeter.
   The set is determined by (b, L, e), and e ranges over all sequences with e_{i+1} - e_i ≥ 1 inside a run and
   ≥ 2 between runs. Writing e by its first term and differences, the sets with shape (b, L) have generating
   function x^{E}/(x;x)_k (if 0 ∉ S, e_1 ≥ 1) and x^{E-k}/(x;x)_{k-1} (if 0 ∈ S, e_1 = 0), where
   E = k + C(k,2) + Σ_{j<b} (number of perimeter elements in runs j+1..b) = C(k+1,2) + C(b,2) + Σ_{t∈L} (t-1).
   Summing over L with |L| = l uses Σ_{|L|=l} x^{Σ(t-1)} = x^{C(l,2)} [b choose l]_x. After clearing
   denominators, "sets with b runs and 0 ∉ S have generating function x^{b^2}/(x;x)_{2b}" and "sets with b runs
   and 0 ∈ S have generating function x^{b(b-1)}/(x;x)_{2b-1}" become the two cases c = b and c = b - 1 of
3. *the q-identity* Σ_{l=0}^{b} x^{l(l+c)} [b choose l]_x / (x;x)_{c+l} = 1/(x;x)_{b+c} (b, c ≥ 0). Proof by
   induction on b: b = 0 is trivial; with [b choose l] = [b-1 choose l] + x^{b-l} [b-1 choose l-1] the sum splits
   into F(b-1, c) + x^{b+c} F(b-1, c+1) = 1/(x;x)_{b+c-1} + x^{b+c}/(x;x)_{b+c} = 1/(x;x)_{b+c}.
4. So the nonempty sets with perimeter n, split by m = 2b - [0 ∈ S], number Y_m(n); summing over m and comparing
   with step 1 proves the claim.

The statistic m = 2(number of runs) - [0 ∈ S] was found by a search over small linear combinations of set
statistics ([`certificate/statistic_search.py`](A182372/certificate/statistic_search.py)).

Lean: [checked](A182372/A182372_mathlib.lean).

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

### [A182963](A182963/): integer series

Lean: [full proof](A183241/A183241_mathlib.lean).

### [A183128](A183128/): integer series

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A183129](A183129/): binomial-power Hanna series are integer series

**Source.** Nine entries by P. D. Hanna (Oct-Dec 2010), each "Conjecture: this sequence consists entirely
of integers." (OEIS text, CC BY-SA 4.0, read 2026-11-06). Each is
A(x) = exp( Σ_{n≥1} [Σ_k B(n,k)^(e(n,k)) x^k] x^n/n ) with

| id | B(n,k) | e(n,k) |
|---|---|---|
| A181070 | C(n,k), k ≤ n | k+1 |
| A181080 | C(n,k), k ≤ n | n-k+1 |
| A181082 | C(n,k), k ≤ n | n+k |
| A181084 | C(n,k), k ≤ n | n+k+1 |
| A181074 | C(n+k-1,k), k ≥ 0 | k+1 |
| A181076 | C(n+k-1,k) | n |
| A181078 | C(n+k-1,k) | n+k-1 |
| A183128 | C(n+k-1,k) | k^2+1 |
| A183129 | C(n+k-1,k) | k^2+k |

**Result.** All nine are integer series. The argument also explains the entries' remarks that the
variants with exponent k, n-k, k^2 are not integral (they violate condition (E2) below).

**Argument.** Read the series as G(x, x) with G(x, y) = exp(Σ_{n≥1,k} ℓ(n,k) x^n y^k),
ℓ(n,k) = B(n,k)^e(n,k)/n. Group the monomials by primitive w = (n0, k0) (gcd 1, n0 ≥ 1): with
(n,k) = j w and β_w(j) = j ℓ(jw) = B(jw)^e(jw)/n0, G = Π_w E_w(x^n0 y^k0), E_w(t) = exp(Σ_j β_w(j) t^j/j).
If every β_w is an integer sequence with Gauss congruences β(mp^a) ≡ β(mp^(a-1)) (mod p^a), Dwork's lemma
gives E_w ∈ ℤ[[t]], so G ∈ ℤ[[x, y]] and A(x) = G(x, x) ∈ ℤ[[x]] (the product converges since n0 ≥ 1).

Fix w, write b(j) = B(jw), s = v_p(n0), M = m p^(a-1), N = m p^a.
- (Gauss for b.) b(j) = CT(Λ^j) with Λ = (1+x)^n0 x^(-k0) (first type) or Λ = (1-x)^(-n0) x^(-k0) (second
  type, C(n+k-1,k) = [x^k](A183129/1-x)^(-n)), Λ ∈ ℤ((x)). Frobenius gives Λ^p ≡ Λ(x^p) (mod p), lifting gives
  Λ^N ≡ Λ(x^p)^M (mod p^a), and CT(Λ(x^p)^M) = CT(Λ^M). So b(N) ≡ b(M) (mod p^a).
- (Valuation.) v_p(b(j)) ≥ s: first type from C(n,k) gcd(n,k)/n ∈ ℤ; second type from
  C(jN0-1, jk0) = C(jN0, jk0) n0/N0 with N0 = n0 + k0, gcd(N0, k0) = 1.
- If k0 = 0 then n0 = 1 and b ≡ 1. Let k0 ≥ 1. Conditions on e, checked for all nine:
  (E1) e(jw) ≥ 1; (E2) e(Mw) ≥ a + 1 (≥ a suffices when s = 0) and e(Nw) ≥ e(Mw);
  (E3) φ(p^a) | e(Nw) - e(Mw) (e is linear or quadratic homogeneous-plus-constant in j:
  differences are multiples of m p^(a-1)(p-1) or m^2 p^(2a-2)(p^2-1)).
- s ≥ 1: v_p(β(M)), v_p(β(N)) ≥ s(a+1) - s ≥ a, both ≡ 0. s = 0, p | b(M): then p | b(N) and both
  b^e ≡ 0 (mod p^a) by (E2). s = 0, p ∤ b(M): b(N)^e(N) ≡ b(M)^e(N) = b(M)^e(M) b(M)^(e(N)-e(M)) ≡ b(M)^e(M)
  by Euler and (E3). Integrality of β from the valuation bound and (E1).
- (E2) for each: M ≥ p^(a-1) ≥ a, so M k0 + 1 ≥ a + 1 (k+1, k^2+1, k^2+k, n+k+1, n-k+1 when n0 > k0;
  n0 = k0 forces w = (1,1), b ≡ 1); n+k: M(n0+k0) ≥ 2p^(a-1) ≥ a+1; n+k-1: if s ≥ 1 then n0 ≥ 2 and
  3p^(a-1) - 1 ≥ a+1, if s = 0 then 2p^(a-1) - 1 ≥ a; n: if s ≥ 1 then M n0 ≥ p^a ≥ a+1, if s = 0 then
  M n0 ≥ a.

Lean: [full proof](A183129/A183129_mathlib.lean).

### [A183241](A183241/): seven Hanna series are integer series

**Source.** Seven entries by P. D. Hanna (2009-2011), each with the comment "Conjectured to consist
entirely of integers." (OEIS text, CC BY-SA 4.0; entries read 2026-11-06: A183241 rev #12 and A182963 rev #8
of Sep 10 2026, the others rev #2 of Mar 30 2012). The seven claims share only this wording; each series
is different.

| id | series |
|---|---|
| A183241 | exp(Σ b(n) x^n/n), b = A183240(n) = Σ_{λ ⊢ n} (n!/Π λ_i!)^2 |
| A182963 | the same with cubes, b = A183235(n) |
| A174470 | exp(Σ t(n) (3x)^n/n), t = A014578 (t(n) = 1 if v_3(n) even, else 0) |
| A165940 | a(n) = 2^(n^2+n) [x^n] exp(Σ x^m/(m 2^(m^2))) |
| A157675 | A(x) = exp(Σ_{n≥1} A(2^n x)^n x^n/n) |
| A156907 | A(x) = 1 + x exp(Σ_{k≥1} (A(2^k x) - 1)^k/k) |
| A156908 | the same with 3^k |

**Result.** All seven are integer series (every coefficient is an integer).

**Argument.** Tool: if b(n) ∈ ℤ satisfies the Gauss congruences b(m p^a) ≡ b(m p^(a-1)) (mod p^a) for all
primes p, then b(n) = Σ_{d|n} d c(d) with c(d) ∈ ℤ and exp(Σ b(n) x^n/n) = Π_d (1 - x^d)^(-c(d)) ∈ ℤ[[x]]
(Dwork). Locally: if b(n) ∈ ℤ_(p) satisfies them at one prime p, the series lies in ℤ_(p)[[x]]
(Dieudonné-Dwork).

1. *A183241, A182963 (any power r ≥ 1).* Let X_n be the set of r-tuples of words of length n over
   {1, 2, ...} that all have the same content (c_1, ..., c_k) with c_1 ≥ ... ≥ c_k > 0 (letter i used c_i
   times, letters 1..k all used). Then |X_n| = Σ_{λ ⊢ n} (n!/Π λ_i!)^r = b(n). Rotating all r words at once is
   an action of ℤ/n on X_n. An element fixed by rotation by d (d | n) is the (n/d)-fold repetition of an
   element of X_d (content scales by n/d, preserving the conditions), and conversely. So the elements of
   exact period d form orbits of size d, and b(n) = Σ_{d|n} d c(d) with c(d) ≥ 0 the number of primitive
   orbits. Gauss congruences follow.
2. *A174470.* b(n) = t(n) 3^n. For p ≠ 3: t(m p^a) = t(m p^(a-1)) and 3^(m p^a) ≡ 3^(m p^(a-1)) (mod p^a)
   (Euler). For p = 3: m 3^(a-1) ≥ a, so 3^a divides both terms.
3. *A165940.* Put u(m) = 2^(-m^2). For odd p, 2 is a p-adic unit and 2^(-(m p^a)^2) / 2^(-(m p^(a-1))^2) =
   2^(-m^2 p^(2a-2) (p^2-1)) ≡ 1 (mod p^a), since p^(a-1)(p-1) divides the exponent; so
   [x^n] exp(Σ u(m) x^m/m) ∈ ℤ_(p). For p = 2: the coefficient is Σ_{λ ⊢ n} 2^(-Σ λ_i^2)/z_λ with
   z_λ | n!, and 2^(n^2+n) 2^(-Σ λ_i^2)/z_λ has 2-adic valuation ≥ n - v_2(n!) ≥ 1.
4. *A157675, A156907, A156908 (one lemma).* Lemma: let G(x, y) ∈ 1 + ℤ[[x, y]] with G(x, 0) = 1 and only
   monomials x^n y^k with n ≥ k (n ≥ 1), and let Φ be the ℚ-linear map x^n y^k ↦ q^(c(n,k)) x^n with
   c(jn, jk) = j^2 c(n, k) ≥ 0 and q ≥ 2 an integer. Then exp(Φ(log G)) ∈ ℤ[[x]]. Proof: G = Π_v (1 - x^v)^(e_v)
   over primitive-or-not v = (n, k) with e_v ∈ ℤ (graded induction), so log G = -Σ_v e_v Σ_j x^(jv)/j and
   exp(Φ log G) = Π_v E_v^(-e_v) with E_v = exp(Σ_j q^(j^2 c_v) x^(j n_v)/j). Each E_v is integral: β(j) =
   q^(j^2 c) satisfies Gauss congruences (p ∤ q: φ(p^a) | c m^2 p^(2a-2)(p^2-1); p | q and c ≥ 1: both terms
   divisible by p^(p^(2a-2)) and p^(2a-2) ≥ a; c = 0: β constant). The product converges x-adically.
   - A156907/A156908: with B = A - 1 ∈ xℤ[[x]], Σ_k (A(q^k x) - 1)^k/k = Φ(log 1/(1 - yB(x))) with
     Φ: x^n y^k ↦ q^(nk) x^n.
   - A157675: Σ_n A(2^n x)^n x^n/n = Φ(log 1/(1 - y x A(x))) with Φ: x^m y^n ↦ 2^(n(m-n)) x^m (m ≥ n).
   In each case [x^N] of the right side depends only on [x^(<N)] of A, so induction on N (A integral up to
   degree N-1 ⇒ G integral up to that degree ⇒ the lemma applied to the truncation gives A integral up to
   degree N) proves integrality.

Lean: [full proof](A183241/A183241_mathlib.lean).

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

### [A192062](A192062/): the prime chain T(2n) = A(n)T(n), A(3n) = A(n)B(n), B(5n) = B(n)C(n), ... has integer factors

**Source.** [A192062](https://oeis.org/A192062) (Kenneth J. Ramsey, 2011), comment: "Conjecture re relation of
A192062 to the sequence of primes: T(2*n,j) = A(n,j)*T(n,j) where A(n,j) is from the square array A191971. There,
A(3*n,j) = A(n,j)*B(n,j) where B(n,j) are integers. ... My conjecture is that this property continues indefinitely
and follows the sequence of primes." (OEIS text, CC BY-SA 4.0, revision #23 of Dec 10 2016, checked 2026-11-06.)

**Reading.** Column j >= 0 of T is T(0)=0, T(1)=1, T(2i)=T(2i-2)+T(2i-1), T(2i+1)=T(2i-1)+j T(2i) (formula in the
entry). Column j of A191971 is A(0)=2, A(1)=1, A(2i)=j A(2i-1)+A(2i-2), A(2i+1)=A(2i)+A(2i-1). Let p_1, p_2, ... =
2, 3, 5, ... Put G_1 = T, G_2 = A and G_{k+1}(n) = G_k(p_k n)/G_k(n) (so G_3 = B, G_4 = C, ...). The conjecture:
for every k, j >= 0 and n >= 1, G_k(p_k n) = G_k(n) G_{k+1}(n) with G_{k+1}(n) an integer (and G_2 = A).

**Result.** True for every k, j and n >= 1. Every G_k(n) is a product of distinct "cyclotomic parts" of a Lehmer
sequence, and each G_{k+1}(n) is again such a product.

**Argument.** 1. *Lehmer form.* For j >= 1 let a, b be real with ab = -1 and a^2 + b^2 = j+2, so (a+b)^2 = j and a^2, b^2 are the
   two roots of x^2 - (j+2)x + 1. The Lehmer sequence L(n) = (a^n - b^n)/(a - b) (n odd), (a^n - b^n)/(a^2 - b^2)
   (n even) has L(0)=0, L(1)=1, L(2)=1, L(3)=a^2+ab+b^2=j+1 and L(n+4)=(j+2)L(n+2)-L(n). T satisfies the same
   recurrence (eliminate the odd terms from the two-step rule; it is the formula T(n+2) = (j+2)T(n) - T(n-2) in the
   entry) with the same four initial values, so T(n,j) = L(n). Likewise the companion V(n) = a^n + b^n (n even),
   (a^n + b^n)/(a + b) (n odd) has V(0)=2, V(1)=1, V(2)=j+2, V(3)=j+3 and the same order-4 recurrence, as does A;
   so A(n,j) = V(n).
2. *Cyclotomic parts.* Let P_d = b^{phi(d)} Phi_d(a/b), the homogenised cyclotomic polynomial. Then
   a^n - b^n = prod_{d | n} P_d, with P_1 = a - b and P_2 = a + b. Hence L(n) = prod_{d | n, d >= 3} P_d for every
   n >= 1. For d >= 3, Phi_d is self-reciprocal of even degree, so P_d is a symmetric form of even degree in a, b
   with integer coefficients, i.e. an integer polynomial in (a+b)^2 = j and ab = -1: P_d is an integer. a/b = -a^2
   has absolute value != 1, so P_d != 0.
3. *Exponent bookkeeping.* Write G_k(n) = prod_{d >= 3} P_d^{e_k(n,d)}. For G_1, e_1(n,d) = prod_q [v_q(d) <= v_q(n)]
   over all primes q. Claim: e_k(n,d) = prod_{i<k} [v_{p_i}(d) = v_{p_i}(n)+1] * prod_{q not in {p_1..p_{k-1}}}
   [v_q(d) <= v_q(n)], which is 0 or 1. Induction: replacing n by p_k n changes only the factor for q = p_k, from
   [v <= v_{p_k}(n)] to [v <= v_{p_k}(n)+1]; the difference is [v = v_{p_k}(n)+1] >= 0, so G_k(p_k n)/G_k(n) =
   prod P_d^{e_{k+1}(n,d)} with e_{k+1} of the claimed form. Since the P_d (d >= 3) are nonzero integers, every
   G_k(n) is an integer and G_k(p_k n) = G_k(n) G_{k+1}(n). For k = 1 this gives T(2n)/T(n) = prod_{d | 2n, d not
   dividing n, d >= 3} P_d = V(n) = A(n) (for n odd the factor P_2 = a+b is excluded, giving (a^n+b^n)/(a+b)).
4. *j = 0.* Here T(2i)=i, T(2i+1)=1, A(n)=n for odd n and 2 for even n, so B(n) = A(3n)/A(n) = 3 (n odd), 1 (n
   even), and C = B(5n)/B(n) = 1, after which every G_k is 1.

Lean: needs Mathlib.

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

### [A193550](A193550/): sqrt((A(x) - 1)/x) is an integer series

**Source.** [A193550](https://oeis.org/A193550) (Paul D. Hanna, 2011): o.g.f.
A(x) = 1/(1 - x/(1 - x/(1 - 9x/(1 - 9x/(1 - 25x/(1 - 25x/(1 - ...))))))), a continued fraction whose partial
numerators are the odd squares, each twice. "Conjecture: given o.g.f. A(x), then sqrt( (A(x) - 1)/x ) is an
integer series." The example reports integrality for the first 500 terms. (OEIS text, CC BY-SA 4.0,
revision #19, checked 2026-11-06.)

**Result.** True. Writing A = 1 + x B(x)^2, B has integer coefficients (B = 1 + x + 6x^2 + 97x^3 + ...). The
proof uses only that every partial numerator is 1 mod 4, so the same holds for any S-fraction
1/(1 - c_1 x/(1 - c_2 x/(1 - ...))) with all c_i = 1 (mod 4) integers.

**Argument.** 1. Each coefficient of a continued fraction 1/(1 - c_1 x/(1 - c_2 x/ ...)) is an integer polynomial in the
   c_i (the truncation of depth n+1 already gives the x^n coefficient). Reducing mod 4 with every c_i = 1 gives
   the all-ones fraction, whose series is the Catalan series C(x) = 1 + x C(x)^2. So a(n) = Catalan(n) (mod 4)
   for all n. In particular (A - 1)/x = C^2 + 4H with H in Z[[x]], and H(0) = (a(1) - 1)/4 = 0.
2. C is a unit of Z[[x]]. Put y = H / C^2, so y(0) = 0 and (A - 1)/x = C^2 (1 + 4y).
3. W + W^2 = y has a solution W in Z[[x]] with W(0) = 0: iterate w_0 = 0, w_(k+1) = y - w_k^2; then
   w_(k+1) - w_k = -(w_k - w_(k-1))(w_k + w_(k-1)) is divisible by x^(k+1), so the w_k converge x-adically.
4. B = C (1 + 2W) has B(0) = 1 and B^2 = C^2 (1 + 4(W + W^2)) = C^2 (1 + 4y) = (A - 1)/x.

Lean: [full proof](A193550/A193550_mathlib.lean).

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

### [A195673](A195673/): p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x)

**Source.** [A195673](https://oeis.org/A195673), Paul Curtz, Sep 23 2011: "Triangle T(n,k) read by rows:
T(0,0)=-2, T(1,0)=3, T(1,1)=0 and T(n,k) = T(n-1,k)-T(n-2,k-2) otherwise." Comment: the row polynomials
p(n,x) = sum_{k=0..n} T(n,k) x^(n-k), built with other initial constants T(0,0) = p and T(1,0) = q, satisfy
p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x), the S-polynomials of [A053119](https://oeis.org/A053119) (Chebyshev S:
S(0) = 1, S(1) = x, S(n) = x S(n-1) - S(n-2)). (OEIS text, CC BY-SA 4.0, revision #18 of Mar 30 2012, checked
2026-11-06.)

**Reading.** Entries outside 0 <= k <= n are 0, and T(1,1) = 0 is kept for every (p, q). The "otherwise"
recurrence then holds for every n >= 2 and every k (it returns 0 outside the triangle).

**Result.** True for all integers p, q and all n >= 0.

**Argument.** Shifting the sum index, sum_k T(n-2,k-2) x^(n-k) = p(n-2,x), so the row polynomials satisfy
p(n,x) = x p(n-1,x) - p(n-2,x) for n >= 2, with p(0,x) = p and p(1,x) = q x. The recurrence for T is linear in
(p, q), so T_{p+1,q+1} = T_{p,q} + T_{1,1} entrywise, and the difference of the row polynomials is the row
polynomial for p = q = 1. That one starts 1, x and has the S recurrence, so it is S(n,x).

Lean: [full proof](A195673/A195673_mathlib.lean).

### [A195825](A195825/): plateaus of the columns of the generalized pentagonal-number array

**Source.** [A195825](https://oeis.org/A195825) (Omar E. Pol, 2011): square array T(n,k), n ≥ 0, k ≥ 1, column k
built from the generalized (k+4)-gonal numbers as Euler's pentagonal number theorem builds the partition numbers
(column 1 = A000041, column 2 = A006950, column 3 = A036820). Comment (Pol, Jun 21 2012): "Conjecture: if k is odd
then column k contains (k+1)/2 plateaus whose levels are the first (k+1)/2 terms of A210843 and whose lengths are
k+1, k-1, k-3, k-5,... 2. Otherwise, if k is even then column k contains k/2 plateaus whose levels are the first k/2
terms of A210843 and whose lengths are k+1, k-1, k-3, k-5,... 3. The sequence A210843 gives the levels of the
plateaus of column k, when k -> infinity." [A210843](https://oeis.org/A210843): 1, 4, 13, 35, 86, ..., "Level of the
n-th plateau of the column k of the square array A195825, when k -> infinity." (OEIS text, CC BY-SA 4.0, A195825
revision #100 of Jun 28 2026, checked 2026-11-06.)

**Reading.** Column k has g.f. 1/Σ_{j∈ℤ} (−1)^j q^{(mj² − (m−2)j)/2} with m = k+2 (the entry's program; this
reproduces the data). A plateau is a maximal run of at least two equal consecutive terms.

**Result.** True. With m = k + 2:
- T(n+1, k) = T(n, k) exactly for A(m+1) ≤ n ≤ (A+1)(m−1) − 2, A ≥ 0. So the plateaus are n ∈ [A(m+1), (A+1)(m−1) − 1],
  of length k + 1 − 2A, for A = 0, 1, ... while k + 1 − 2A ≥ 2, and the column increases strictly elsewhere.
- The level of plateau A is T(A(k+3), k), the same for every k ≥ 2A + 1; so it is A210843(A+1). It equals
  Σ_{B ≤ A} p₃(B), with p₃ the 3-colored partition numbers A000716 (this also answers A210843's question: it is the
  Euler transform of 4, 3, 3, 3, ...).

**Argument.** 1. Jacobi's triple product gives Σ_j (−1)^j q^{(mj²−(m−2)j)/2} = Π_{n≥1} (1−q^{mn})(1−q^{mn−1})(1−q^{mn−m+1}), so
   T(n,k) counts partitions of n into parts ≡ 0, ±1 (mod m).
2. Removing one part 1: T(n+1) − T(n) = D(n+1), the number of such partitions of n+1 with no part 1.
3. A part ≠ 1 is am + e with a ≥ 1, e ∈ {−1, 0, 1}, so lies in [a(m−1), a(m+1)]; a sum of such parts lies in
   [A(m−1), A(m+1)] with A = Σa ≥ 1, and conversely every n in such an interval is A parts from {m−1, m, m+1}. So
   D(n) = 0 iff n lies in a gap A(m+1) < n < (A+1)(m−1), which has m − 2 − 2A elements; a gap of g zeros is a
   plateau of length g + 1 = k + 1 − 2A.
4. Level of plateau A: N = A(m+1). In a partition of N, the parts am + e ≠ 1 have Σa ≤ A when 2A + 3 ≤ m
   (Σa(m−1) ≤ N). The map am + e ↦ a(m+1) + e, refilling with 1s up to A(m+2), is a bijection onto the partitions of
   A(m+2) into parts ≡ 0, ±1 mod m+1 (the inverse direction uses Σa·m ≤ A(m+2) and each part ≤ a(m+2)). So the
   level does not depend on m; it counts multisets of pairs (a, e) with Σa ≤ A, which is Σ_{B≤A} p₃(B).

Lean: [full proof](A195825/A195825_mathlib.lean).

### [A196226](A196226/): the term 690 violates all three σ_k congruences

**Source.** [A196226](https://oeis.org/A196226) (John W. Layman, Sep 29 2011): "m such that A054024(m) (sum of
divisors of m reduced modulo m) is 3 + m/2." Comment: "Conjectures. (1) If m>=14 is a term of this sequence,
then sigma(2,m) is congruent to 5 + m/2 modulo m; (2) If m>=22 ..., sigma(3,m) ... 9 + m/2 ...; If m>=38 ...,
sigma(4,m) ... 17 + m/2 modulo m." R. J. Mathar (Aug 24 2023): "The terms in this sequence which are not even
semiprimes are 8, 690, 12978, 176946, ..." (OEIS text, CC BY-SA 4.0, revision #21 of Aug 24 2023, checked
2026-11-06.)

**Result.** All three conjectures are false. m = 690 = 2·3·5·23 is a term (σ(690) = 1728 ≡ 348 = 3 + 345), but
σ₂(690) ≡ 380 (claimed 350), σ₃(690) ≡ 426 (claimed 354), σ₄(690) ≡ 668 (claimed 362) mod 690. Up to 200000 the
violating terms are exactly the non-semiprime terms 690, 12978, 176946.

**Argument.** Direct computation, σ_k(690) = (1+2^k)(1+3^k)(1+5^k)(1+23^k). For the even semiprimes m = 2p
(p > 3 prime), the congruences do hold for every k: σ_k(2p) = (1+2^k)(1+p^k), and (1+2^k)p^k ≡ p mod 2p since
1+2^k and p^k are odd multiples of p, so σ_k(2p) ≡ 2^k + 1 + p.

Lean: [witness](A196226/A196226_mathlib.lean).

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

### [A202150](A202150/): the odd coefficients of the q-analog of π/2 sit exactly at 3n(n+1)

**Source.** [A202150](https://oeis.org/A202150) (Paul D. Hanna), "a(n) = A202146(3*n*(n+1)) for n>=0."
Comment: "Conjecture: this sequence consists of all odd terms in A202146; the g.f. of A202146 is
1/(1-x) + Sum_{n>=1} x^n/(1-x) * Product_{k=1..n} (1 - x^k) / (1 - x^(2*k+1)), which by the conjecture has an
odd coefficient of x^m iff m = 3*n*(n+1) for n>=0. The conjecture holds for at least the initial 30300 terms
of A202146." [A202146](https://oeis.org/A202146) repeats the parity claim as a conjectured formula. (OEIS text,
CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True. With (a;q)_n = (1−a)(1−aq)···(1−aq^{n−1}), the g.f. of A202146 is
A(q) = Σ_{n≥0} q^n (q;q)_n/(q;q²)_{n+1}, and

(∗)  Σ_{n≥0} (−q)^n (−q;q)_n/(q;q²)_{n+1} = Σ_{m≥0} (−1)^m q^{3m(m+1)}.

Reducing mod 2 ((q;q)_n ≡ (−q;q)_n, q^n ≡ (−q)^n, and 1/(q;q²)_{n+1} has integer coefficients) gives
A(q) ≡ Σ_m q^{3m(m+1)} (mod 2): A202146(k) is odd iff k = 3m(m+1), so A202150 lists exactly the odd terms.

**Argument.** 1. *Finite identities.* Let E_b(n) = Σ_{j∈ℤ} (−1)^j q^{3j²+bj} [2n+1, n−2j] (Gaussian binomials, zero outside
   0..2n+1). Expanding [2n+3, k+1] by the two q-Pascal rules in the two orders,
   [N+2,k+1] = [N,k−1] + (q^k+q^{k+1})[N,k] + q^{2k+2}[N,k+1] and
   [N+2,k+1] = q^{N+1−k}[N,k−1] + (1+q^{N+1})[N,k] + q^{k+1}[N,k+1],
   and folding odd offsets back with [N,k] = [N,N−k], one gets for N = 2n+1
   E_b(n+1) = −q^{3−b}E_{6−b}(n) + (1+q)q^n E_{b−2}(n) + q^{2n+2}E_{4−b}(n) and
   E_b(n+1) = (1+q^{2n+2})E_b(n) + q^{n+1}E_{2−b}(n) − q^{n+3−b}E_{4−b}(n).
   The second at b = 1 and the first at b = 3 involve only E_1, E_3; induction from E_1(0) = E_3(0) = 1 gives
   E_1(n) = (−q;q)_n and E_3(n) = q^n(−q;q)_n.
2. *Bailey pair.* E_1(n) + E_3(n) = (−q;q)_n(1+q^n) says exactly that (α_n, β_n) is a Bailey pair relative to
   a = q, with β_n = (−q;q)_n(1+q^n)/(2(q;q)_{2n+1}), 2(1−q)α_0 = 2,
   2(1−q)α_{2m} = (−1)^m q^{m(3m+1)}(1+q^{2m}) (m ≥ 1), 2(1−q)α_{2m+1} = (−1)^{m+1} q^{3m(m+1)}(1+q^{2m+2}).
3. *Bailey's lemma* with a = q, ρ1 = q, ρ2 = −1 (so aq/ρ1ρ2 = −q): the left side is
   Σ (q)_n(−1)_n(−q)^n β_n = LHS(∗); the right side is (1−q)/(1+q)·Σ (−1)_n(−q)^n α_n/(−q²;q)_n. The factor
   (1+q^{n})(1+q^{n+1}) in the denominator cancels one of the two monomials of each α_n, and the remaining
   terms pair up (n = 2m and 2m+1) into (−1)^m q^{3m(m+1)}; the n = 0, 1 terms give 1/(1+q) + q/(1+q) = 1.

Lean: [full proof](A202150/A202150_mathlib.lean).

### [A202941](A202941/): Shevelev's generalized binomials at the first p-row

**Source.** V. Shevelev (Dec 2011 – Jan 2012). For t = 2, 3, 4 let Q^(t)_0(n) = 1 and
Q^(t)_m(n) = Σ_{i=1..n} i^t Q^(t)_{m−1}(i) (a polynomial in n), let n!^(t) be the LCM of the
denominators of the coefficients of Q^(t)_n ([A202367](https://oeis.org/A202367),
[A202368](https://oeis.org/A202368), [A202369](https://oeis.org/A202369) at n+1), and
C^(t)(n,m) = n!^(t)/(m!^(t) (n−m)!^(t)). Conjectures (OEIS text, CC BY-SA 4.0, read 2026-11-06):
- [A202941](https://oeis.org/A202941) (t = 2): "If p is an odd prime, then the ((p-1)/2))-th row
  contains two 1's and (p-3)/2 numbers multiple of p."
- [A203484](https://oeis.org/A203484) (t = 3): p = 3k+1: the k-th row has two 1's and k−1
  multiples of p; p = 3k+2: the (2k+1)-th row has two 1's and 2k multiples of p.
- [A178473](https://oeis.org/A178473) (t = 4): p = 4k+1: row k; p = 4k+3: row 2k+1 (same form).
- Row sums: [A203278](https://oeis.org/A203278) (t = 2) a((p−1)/2) ≡ 2 (mod p);
  [A203498](https://oeis.org/A203498) (t = 3) a((p−1)/3) ≡ 2 for p ≡ 1 (mod 3),
  a((2p−1)/3) ≡ 2 for p ≡ 2 (mod 3); [A203509](https://oeis.org/A203509) (t = 4) a((p−1)/4) ≡ 2
  for p ≡ 1 (mod 4), a((p−1)/2) ≡ 2 for p ≡ 3 (mod 4).

**Reading.** "Multiple of p" for the (rational) entries C^(t)(n,m) means v_p ≥ 1; the row sums
are integers in the data and "≡ 2 (mod p)" then means p | (sum − 2). The conjectured closed
form of A202367 is not needed.

**Result.** All six claims hold for every prime in their range. Write r* for the row in each
claim (r* = (p−1)/2; k or 2k+1; k or 2k+1). Then v_p(n!^(t)) = 0 for n < r* and
v_p(r*!^(t)) ≥ 1, so every inner entry of row r* has v_p = v_p(r*!^(t)) ≥ 1, the two outer
entries are 1, and the row sum is 2 plus a multiple of p.

**Argument.** Let S_k(n) = Σ_{i=1..n} i^k and Z_(p) the p-integral rationals; p is odd (p = 2
occurs only for t = 3, row 1, which has no inner entries).
1. *Power sums (k ≤ 2p−1).* i^k = Σ_j S(k,j) j! C(i,j) (Stirling numbers of the second kind), so
   S_k(n) = Σ_{j≤k} S(k,j) (n+1)(n)⋯(n+1−j)/(j+1). The falling product has integer
   coefficients and content 1, so only terms with p | j+1 can fail to be p-integral; for
   j ≤ 2p−2 that is j = p−1. Also (p−1)! S(k,p−1) = Σ_i (−1)^(p−1−i) C(p−1,i) i^k ≡ Σ_{i=1}^{p−1} i^k
   (mod p), which is ≡ −1 if (p−1) | k and ≡ 0 otherwise. Hence:
   (i) S_k ∈ Z_(p)[n] for 1 ≤ k ≤ 2p−3, k ≠ p−1;
   (ii) S_{p−1}, S_{2p−2} ∉ Z_(p)[n] (the j = p−1 term has p-adic valuation −1 and is the only
   bad term); (iii) S_{2p−1} ∉ Z_(p)[n] (the j = p−1 term is integral since (p−1) ∤ 2p−1; the
   j = 2p−1 term (n+1)⋯(n+2−2p)/(2p) is the only bad term).
2. *Newton.* Σ_m Q^(t)_m z^m = Π_{i≤n} (1 − i^t z)^(−1) = exp(Σ_r S_{tr}(n) z^r/r), so
   Q^(t)_m = Σ_{λ ⊢ m} z_λ^(−1) Π_i S_{tλ_i}, with z_λ = Π j^{m_j} m_j! a p-unit when m < p.
3. *The threshold.* In each case r* < p, every r < r* has t r ≤ 2p−3 and t r ≠ p−1, while
   t r* ∈ {p−1, 2p−2, 2p−1}: t = 2: 2r* = p−1; t = 3, p = 3k+1: 3k = p−1; t = 3, p = 3k+2:
   3(2k+1) = 2p−1 and 3r ≤ 6k = 2p−4, 3 ∤ p−1; t = 4, p = 4k+1: 4k = p−1; t = 4, p = 4k+3:
   4(2k+1) = 2p−2 and 4r ≤ 8k = 2p−6, 4 ∤ p−1.
   By 1(i) and 2, Q^(t)_m ∈ Z_(p)[n] for m < r*, so v_p(m!^(t)) = 0. For m = r*, every λ ≠ (r*)
   has parts < r*, so Q^(t)_{r*} = (element of Z_(p)[n]) + S_{t r*}/r*, which is not in
   Z_(p)[n] by 1(ii)/(iii); so v_p(r*!^(t)) ≥ 1.

Lean: [full proof](A202941/A202941_mathlib.lean).

### [A202943](A202943/): a(n) is odd iff n has no 1-bit at an even position ≥ 2

**Source.** [A202943](https://oeis.org/A202943) (Paul D. Hanna), "G.f.: [ Sum_{n>=0} (n+1)*(n+2)/2 *
2^(n*(n-1)) * x^n ]^(1/3)." Comment: "Conjecture: the characteristic function of a(n) (mod 2) equals
(1+x)*(1+x^2)*(1+x^8) * Sum_{n>0} x^(32*A000695(n)), where A000695 is the sums of distinct powers of 4."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** The sum over A000695 must include A000695(0) = 0 (the entry's own example starts 1 + x^32 + ...).
The exponents of the product are n = e + 32m with e ∈ {0,1,2,3,8,9,10,11} and m with base-4 digits in {0,1};
equivalently n has no 1-bit at positions 2, 4, 6, ....

**Result.** True.

**Argument.** Let B(x) = Σ C(n+2,2) 2^{n(n−1)} x^n and A = B^{1/3}.
1. *Integrality.* 2^{n(n−1)} ≡ 1 (mod 9) unless n ≡ 2 (mod 3), and then 3 | C(n+2,2) and 3 | 2^{n(n−1)} − 1;
   so B ≡ (1−x)^{−3} (mod 9), B(1−x)^3 = 1 + 9D with D ∈ ℤ[[x]], and A = (1−x)^{−1}(1+9D)^{1/3} has integer
   coefficients (the binomial coefficients C(1/3, k)·9^k are integers). It also gives a(n) ≡ 1 (mod 3), the
   entry's formula.
2. *Parity.* Mod 2, B ≡ 1 + x, so A^4 ≡ A(1+x). In characteristic 2, [x^n] f² = f_{n/2} for even n and 0 for odd
   n, so [x^n] A^4 = a(n/4) if 4 | n and 0 otherwise. Hence a(n) ≡ a(n−1) + [4|n]·a(n/4), a(0) = 1. The
   indicator s(n) = t(⌊n/4⌋), t(m) = [m has no 1-bit at an even position], satisfies the same recursion
   (case split on n mod 4 and on ⌊n/4⌋ mod 4), so a(n) ≡ s(n). Finally s(n) = 1 iff n = e + 32m as above.
   (Equivalently A ≡ (1+x)^{1/3} = (1+x)(1+x²)(1+x⁸)(1+x^{32})(1+x^{128})··· mod 2, from the binary expansion
   1/3 = 1 + 2 + 2³ + 2⁵ + ··· in ℤ₂.)

Lean: [full proof](A202943/A202943_mathlib.lean).

### [A203278](A203278/): OEIS A203278

Lean: [full proof](A203278/A203278_mathlib.lean).

### [A203484](A203484/): OEIS A203484

Lean: [full proof](A203484/A203484_mathlib.lean).

### [A203498](A203498/): OEIS A203498

Lean: [full proof](A203498/A203498_mathlib.lean).

### [A203509](A203509/): OEIS A203509

Lean: [full proof](A203509/A203509_mathlib.lean).

### [A207969](A207969/): exp(Σ 5 F(n)^(2k) x^n/n) is an integer series

**Source.** [A207969](https://oeis.org/A207969) and [A207970](https://oeis.org/A207970) (P. D. Hanna,
Feb 22 2012), g.f. exp(Σ_{n≥1} 5 F(n)^4 x^n/n) and exp(Σ_{n≥1} 5 F(n)^6 x^n/n). Both entries state:
"Conjecture: exp( Sum_{n>=1} 5*Fibonacci(n)^(2*k) * x^n/n ) is an integer series for integers k>=0."
(OEIS text, CC BY-SA 4.0, revisions #16 and #23 of Oct 18 2020, checked 2026-11-06.)

**Result.** True for every k ≥ 0. (k = 2 and k = 3 are A207969 and A207970.)

**Argument.** For integers b(n), exp(Σ b(n) x^n/n) ∈ ℤ[[x]] as soon as b(m p^a) ≡ b(m p^(a-1)) (mod p^a)
for all primes p, a ≥ 1, m ≥ 1 (Gauss congruences): then b(n) = Σ_{d|n} d c(d) with integers c(d)
(Dwork), and the series is Π_d (1 - x^d)^(-c(d)). So it suffices to check the congruences for
b(n) = 5 F(n)^(2k). For k = 0, b = 5 is constant. Let k ≥ 1.

- *p ≠ 5.* With L(n) the Lucas numbers, 5 F(n)^2 = L(2n) - 2(-1)^n. Both n ↦ L(2n) and n ↦ (-1)^n
  satisfy the congruences: in ℤ[φ], z^p ≡ τ(z) (mod p) for a fixed τ ∈ {identity, conjugation}
  (from (2φ - 1)^2 = 5 and 5^((p-1)/2) ≡ ±1, or φ^2 ≡ conj(φ) mod 2), hence
  (φ^m)^(p^a) ≡ τ(φ^(m p^(a-1))) (mod p^a), and taking traces gives L(m p^a) ≡ L(m p^(a-1)).
  The congruences are preserved by sums and products, so (5F(n)^2)^k = 5^(k-1) b(n) satisfies them,
  and since 5 is a unit mod p, so does b.
- *p = 5.* 5^j | n implies 5^j | F(n) (from F(5m) = 5 F(m)(x^4 + 2x^3y + 4x^2y^2 + 3xy^3 + y^4) with
  x = F(m-1), y = F(m)). So 5^(a-1) | F(m 5^(a-1)) and 5^a | 5^(1+2k(a-1)) | b(m 5^(a-1)); the same
  holds for b(m 5^a). Hence both terms are 0 mod 5^a.

Lean: [full proof](A207969/A207969_mathlib.lean).

### [A207970](A207970/): exp(Σ 5 F(n)^6 x^n/n)

Lean: [full proof](A207969/A207969_mathlib.lean).

### [A208034](A208034/): exp(Σ 2 Pell(n)^(2k) xⁿ/n) is an integer series; the odd-power and halved versions are not

**Source.** [A208034](https://oeis.org/A208034) (P. D. Hanna, Feb 2012), g.f.
exp(Σ_{n≥1} 2 Pell(n)² xⁿ/n), Pell = A000129. "Conjectures: For all positive integers k,
(1) exp( Sum_{n>=1} 2*Pell(n)^(2*k) * x^n/n ) is an integer series; (2) ... 2*Pell(n)^(2*k-1)
... is NOT an integer series; (3) ... Pell(n)^(2*k) ... is NOT an integer series."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** All three hold for every k ≥ 1 ((1) also for k = 0).

**Argument.** For integers b(n), exp(Σ b(n) xⁿ/n) ∈ ℤ[[x]] once b(m p^a) ≡ b(m p^(a−1))
(mod p^a) for all primes p, a, m ≥ 1 (Gauss congruences; then b(n) = Σ_{d|n} d c(d) with integer
c(d) and the series is Π_d (1 − x^d)^(−c(d))). For b(n) = 2 Pell(n)^(2k):
- *p odd.* In ℤ[√2], with α = 1 + √2, α^n = H(n) + Pell(n)√2 and Q(n) = tr α^n = 2H(n). Since
  2^((p−1)/2) ≡ ±1, z^p ≡ τ(z) (mod p) with τ the identity or conjugation, so Q(m p^a) ≡
  Q(m p^(a−1)) (mod p^a). Then 8 Pell(n)² = Q(2n) − 2(−1)ⁿ (norm of α^n is (−1)ⁿ); the
  congruences pass to products and differences, so 2(8 Pell(n)²)^k = 8^k b(n) satisfies them,
  and 8^k is a unit mod p.
- *p = 2.* Pell(2m) = 2 Pell(m) H(m), so 2^j | n gives 2^j | Pell(n); both b(m 2^a) and
  b(m 2^(a−1)) are divisible by 2^(1+2k(a−1)), a multiple of 2^a.

(2): with b(n) = 2 Pell(n)^m, m = 2k − 1 odd, the x³ coefficient is (4 + 6·2^m + 2·5^m)/3 and
4 + 2·5^m ≡ 4 − 2 = 2 (mod 3). (3): the x² coefficient of exp(Σ Pell(n)^(2k) xⁿ/n) is
(1 + 4^k)/2, not an integer.

Lean: [full proof](A208034/A208034_mathlib.lean).

### [A208060](A208060/): lim a(n)^(1/n) = 2L, L the Lüroth geometric mean

**Source.** [A208060](https://oeis.org/A208060) (Paul D. Hanna): a(n) = 1 + 2n + 2^2 n[n/2] + 2^3 n[n/2][n/3] + ...,
[x] = floor(x). Conjecture in the entry: "limit a(n)^(1/n) = 2*L where L = 2.200161058099... is the geometric mean of
Luroth expansions, where log(L) = Sum_{n>=1} log(n)/(n*(n+1))". The companion
[A075885](https://oeis.org/A075885) (no factor 2^m) carries the same conjecture with limit L. (OEIS text, checked
2026-11-06.)

**Reading.** The m-th term is 2^m prod_{k=1..m} [n/k]; it vanishes for m > n, so a(n) = 1 + sum_{m=1..n} 2^m
prod_{k=1..m} [n/k]. The entry's %F line writes "Product_{k=1..m} 2^k*floor(n/k)", which gives a(2) = 21, not the data
term 13; it should read 2*floor(n/k). The %N definition reproduces the data (certificate/numeric.py).

**Result.** True: a(n)^(1/n) -> 2L. Likewise A075885(n)^(1/n) -> L. For any base c >= 1 the sum
1 + sum_m c^m prod_{k<=m}[n/k] has n-th root tending to cL.

**Argument.** Let T = 2^n P, P = prod_{k=1..n} [n/k] >= 1.
1. Each factor 2[n/k] (k <= n) is >= 1, so the m-th term grows with m up to m = n; hence T <= a(n) <= (n+1) T.
2. With d_j = log j - log(j-1) (d_1 = 0), log [n/k] = sum_{2 <= j <= [n/k]} d_j, and [n/k] >= j iff k <= [n/j], so
   log P = sum_{j=2..n} d_j [n/j].
3. n/j - 1 < [n/j] <= n/j, d_j >= 0 and sum_{j<=n} d_j = log n, so |log P / n - E(n)| <= log n / n with
   E(n) = sum_{j<=n} d_j / j.
4. Summation by parts: E(N) = sum_{j<N} log j / (j(j+1)) + log N / N, which tends to log L (the series converges since
   log j <= 2 sqrt j).
5. So (log a(n))/n -> log 2 + log L, as log(n+1)/n -> 0.

Lean: [full proof](A208060/A208060_mathlib.lean).

### [A209860](A209860/): A054429 commutes with the permutation A209861/A209862

**Source.** - [A209862](https://oeis.org/A209862): "Conjecture: For all n, a(A054429(n)) = A054429(a(n)) ..." (revision #26, Sep 15 2021).
- [A209861](https://oeis.org/A209861) (inverse permutation): "Conjecture: For all n, A209861(A054429(n)) = A054429(A209861(n)) ..."
- [A209860](https://oeis.org/A209860) (fixed points): "Conjecture: for every a(n), also A054429(a(n)) is in the sequence. Conversely, if i is not in the sequence, then neither is A054429(i)."

All three by Antti Karttunen, Mar 24 2012; OEIS text, CC BY-SA 4.0; all still conjectures on 2026-11-06.

**Reading.** A209642(n) is given by the entry's Scheme loop (read n from the least significant bit; a 0-bit sends
(s, i) to (4s+1, 4i), a 1-bit to (2(s+i), 4i); start (0, 1)). A209641 is the same set of values in ascending order,
A209861 maps A209641 to A209642 (so A209861(n) is the position of A209642(n) in A209641, offset 0), and A209862 is its
inverse. A054429 has offset 1: A054429(n) = 3·2^k − 1 − n for 2^k ≤ n < 2^(k+1). The conjectures are read for n ≥ 1.

**Result.** True: A209861(A054429(n)) = A054429(A209861(n)) and A209862(A054429(n)) = A054429(A209862(n)) for all
n ≥ 1, and for i ≥ 1, i is a fixed point iff A054429(i) is.

**Argument.** Let g = A209642, and for n ≥ 1 let L = len(n) (binary length), K = pop(n) (number of 1-bits),
E = 2L − K, and tau(n) defined by tau(1) = 0, tau(2q+1) = tau(q), tau(2q) = 2^E(q) + tau(q).
1. *Closed form.* Induction on the loop: g(n) + 2^E = 2^(2L) + tau(n), with 2·tau(n) < 2^E. So
   2^(2L−1) ≤ g(n) < 2^(2L): g maps level L (2^(L−1) ≤ n < 2^L) into the 2L-bit numbers, and A209861 maps level L
   onto itself. (As words: g(n) is 1^K followed by the tokens "0" for a 1-bit and "01" for a 0-bit of n, LSB first.)
2. *Order on a level.* For n, n' on level L: fewer 1-bits gives a smaller g value; with equal popcount, g order =
   tau order. With equal popcount, tau(odd) < tau(even), and when the last bits agree the comparison passes to
   (n div 2, n' div 2).
3. *A054429 reverses the order.* A054429 keeps the level, sends popcount K to L + 1 − K, and satisfies
   A054429(2q) = 2·A054429(q) + 1, A054429(2q+1) = 2·A054429(q). It flips every bit below the leading one, so by step 2
   g(n) < g(n') iff g(A054429(n')) < g(A054429(n)). Step 2 also shows g is injective.
4. *Ranks.* A209861(n) = 2^(L−1) + r(n), r(n) = #{i on level L : g(i) < g(n)}. Reindexing by A054429 and step 3 give
   r(A054429(n)) = 2^(L−1) − 1 − r(n), which is the claim for A209861. A209861 is a bijection (injective, and maps
   each level into itself), so the claim passes to the inverse A209862 and to the fixed points A209860.

Wiseman's description of A209862 (Aug 2021 comment, verified there up to 2^15) follows from steps 1-2: within a row,
sets are sorted by size, then lexicographically. It is not formalised here.

Lean: [full proof](A209860/A209860_mathlib.lean).

### [A209861](A209861/): A054429 commutes with the permutation A209861/A209862

Lean: [full proof](A209860/A209860_mathlib.lean).

### [A209862](A209862/): A054429 commutes with the permutation A209861/A209862

Lean: [full proof](A209860/A209860_mathlib.lean).

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

### [A210456](A210456/): periods of digital roots of n-step Fibonacci numbers (divisibility by 3, Helenius's closed forms)

**Source.** [A210456](https://oeis.org/A210456) (Paolo P. Lava, Robert G. Wilson v, 2013): period of the digital roots
of the n-step Fibonacci numbers started 0, ..., 0, 1. Comments: "Conjecture: All entries >1 are divisible by 3." and
"Conjecture: a(3^n-1)=3^(2*n+1)-3, a(3^n)=3^(2*n+1)+3^(n+1)+3 - Fred W. Helenius ..., posting to MathFun, Feb 21
2013". Formula (Shixuan Gao, 2025): a(n) = A351889(n, 9), the period mod 9. (OEIS text, CC BY-SA 4.0, revision #82 of
Nov 02 2025, checked 2026-11-06.)

**Reading.** a(n) is the period of u_k mod 9, where u_0 = ... = u_{n-2} = 0, u_{n-1} = 1, u_{k+n} = u_k + ... +
u_{k+n-1} (digital roots of positive terms are the residues mod 9 with 0 written as 9). Entries > 1 are a(n), n ≥ 2.

**Result.** Both conjectures are true. With P(n) the period mod 3:
- a(n) = 3·P(n) whenever 3 ∤ P(n); in all cases 3 | a(n) for n ≥ 2.
- P(3^m − 1) = 3^{2m} − 1 and P(3^m) = 3^{2m} + 3^m + 1, so a(3^m − 1) = 3^{2m+1} − 3 and
  a(3^m) = 3^{2m+1} + 3^{m+1} + 3.

**Argument.** Let f(x) = x^n − x^{n−1} − ... − 1 and M its companion matrix. The start vector (0, ..., 0, 1) is cyclic for
M, so the period mod m is the order of M mod m, i.e. the order of x in (ℤ/m)[x]/(f). Let s_k = tr(M^k) (power sums of
the roots of f): s_1 = 1, s_3 = 7 for n ≥ 3 and s_3 = 4 for n = 2.
1. *3 | a(n).* The order mod 9 is P or 3P (if x^P = 1 + 3r then x^{3P} ≡ 1 mod 9). Suppose M^Q ≡ I (mod 9) with
   3 ∤ Q. Gauss's congruence for traces of integer matrices gives tr(M^{9t}) ≡ tr(M^{3t}) (mod 9) for all t. Take t
   with 3t ≡ 1 (mod Q); then 9t ≡ 3 (mod Q), so s_3 ≡ s_{9t} ≡ s_{3t} ≡ s_1 (mod 9), i.e. 7 ≡ 1 or 4 ≡ 1 (mod 9).
   Contradiction. So the order mod 9 is divisible by 3; when 3 ∤ P it equals 3P.
2. *Mod 3 structure.* (x − 1)f(x) = x^{n+1} − 2x^n + 1 ≡ x^{n+1} + x^n + 1 (mod 3). Its reversal has roots
   β = 1/α. P(n) is the lcm of the orders of the roots α of f̄ when f̄ is squarefree.
   - n = q − 1, q = 3^m: the β are the roots of x^q + x + 1, separable, = {1 + cγ₀ : c ∈ F_q} with γ₀^{q−1} = −1
     (shift β = 1 + γ turns the equation into γ^q + γ = 0), all in F_{q²}. β = 1 is the root of x − 1. The group they
     generate is F_{q²}^*: together with F_q^* it contains every a + bγ₀ with a ≠ 0 (= a(1 + (b/a)γ₀)), more than half
     of F_{q²}^*, so ⟨S⟩·F_q^* = F_{q²}^*; and ⟨S⟩
     contains (1 + cγ₀)(1 − cγ₀) = 1 − c²ν (ν = γ₀² a non-square of F_q), and these (q−1)/2 values 1 − u (u a
     non-square) are not all squares (the number of non-squares u with 1 − u a non-square is (q − χ(−1))/4 > 0), so
     they generate F_q^* (a proper subgroup has at most (q−1)/2 elements and only the squares reach that size). In
     a cyclic group the lcm of the orders of a generating set is the group order: P = q² − 1.
   - n = q: the β are the roots of x^{q+1} + x + 1, separable; from β^{q+1} = −(1+β) one gets β^{q²+q+1} = 1, and
     writing β = z^{q−1} (Hilbert 90 in F_{q³}) the equation becomes z^{q²} + z^q + z = 0, i.e. Tr(z) = 0. So the β
     are the images of the 2-dimensional F_q-space W = ker Tr (which contains F_q) under z ↦ z^{q−1}; as points of
     PG(2,q) = F_{q³}^*/F_q^*, W is a line L. Lines of PG(2,q) are Singer difference sets: L·L^{−1} is the whole
     Singer group (a nontrivial g has gL ≠ L since gcd(q+1, q²+q+1) = 1, and two lines meet in one point). So the β
     generate the norm-one group of order q² + q + 1, and P = q² + q + 1.
   In both cases 3 ∤ P, so step 1 gives a = 3P.

Lean: needs Mathlib.

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

### [A211163](A211163/): numerators of (-1/π^n) ∫_0^1 log(1-1/x)^n dx

Lean: [full proof](A141459/A141459_mathlib.lean).

### [A212392](A212392/): n divides a(n) for A(x) = (x + A(A(x)))^2

**Source.** OEIS [A212392](https://oeis.org/A212392), "Conjecture: n divides a(n); see A212391." (P. D. Hanna,
2012).

**Result.** True. Proved together with A212425 and the general form for every exponent b ≥ 2 in
[`../A212425/`](A212425/README.md); the b = 2 case is the Lean theorem `A212392_b2` in
[`../A212425/A212425_mathlib.lean`](A212425/A212425_mathlib.lean).

Lean: [full proof](A212425/A212425_mathlib.lean).

### [A212425](A212425/): ((b−1)(n−1)+1) divides the coefficients of A(x) = (x + A(A(x)))^b

**Source.** OEIS [A212425](https://oeis.org/A212425) (b = 3, A(x) = sum a(n) x^(8n−5)), "Conjecture: (2*n-1)
divides a(n)", and OEIS [A212392](https://oeis.org/A212392) (b = 2, A(x) = sum a(n) x^(3n−1)), "Conjecture: n
divides a(n)" (P. D. Hanna, May 2012). Both entries add the general form: if A(x) = (x + A(A(x)))^b with
A(x) = sum a(n) x^((b^2−1)(n−1)+b), then ((b−1)(n−1)+1) divides a(n). (OEIS text, CC BY-SA 4.0, revisions
#20 and #19 of Oct 30 2026; still conjectures on 2026-11-06.) A212426 and A212391 list the quotients.

**Result.** True for every b ≥ 2 (so both conjectures and the general form).

**Argument.** Let F = A, u = x + F(F(x)), so F = u^b, and let J be the formal antiderivative of (b+1)F (rational
coefficients, J(0) = 0).
1. *Identity.* J(x) − J(F(x)) = u^(b+1) − (b+1) F(x) F(F(x)). Both sides vanish at 0. Derivatives (chain rule):
   left (b+1)F − (b+1)F(F)·F'; right (b+1)u^b u' − (b+1)[F'·F(F) + F·F'(F)·F'] with u^b = F and
   u' = 1 + F'(F)·F', which is the same.
2. *Integrality.* The right side has integer coefficients. F = u^b with u(0) = 0, so x^b, hence x^2, divides F.
   The coefficient of x^n in J(F(x)) = sum_d j_d F^d only involves j_d with 2d ≤ n, i.e. d < n. By induction on
   n every coefficient j_n of J is an integer.
3. *Reading off.* j_(k+1) = (b+1) [x^k]F/(k+1). At k = (b^2−1)(n−1)+b, k+1 = (b+1)((b−1)(n−1)+1), so
   ((b−1)(n−1)+1) divides a(n).

Lean: [full proof](A212425/A212425_mathlib.lean).

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

### [A214074](A214074/): a(n) = 3 is not the residue class n ≡ 121 (mod 330)

**Source.** OEIS [A214074](https://oeis.org/A214074), least m > 0 such that 2^n − m and 3^n − m are
relatively prime. Comment: "Conjecture: a(n) = 3 if and only if n = 330*k-209 for some k>=1."
(OEIS text, CC BY-SA 4.0.)

**Result.** False in both directions.
- n₁ = 3438721 = 330·10421 − 209 has a(n₁) = 4 (Lean proves a(n₁) ≥ 4).
- n₂ = 1186095 ≡ 75 (mod 330) has a(n₂) = 3 (Lean proves a(n₂) ≥ 3; the gcd for m = 3 is from PARI/GP).
The conjecture holds for all n ≤ 40000 (`certificate/scan.out`).

**Argument.** a(n) ≥ m + 1 when some prime divides both 2^n − j and 3^n − j for each j ≤ m.
- q | gcd(2^n − 1, 3^n − 1) iff ord_q 2 | n and ord_q 3 | n. For q = 23 both orders are 11, so 11 | n gives a(n) ≥ 2.
- q | gcd(2^n − 2, 3^n − 2) (q odd) iff 2^(n−1) ≡ 1 and 3^n ≡ 2 (mod q). This needs ord_q 2 | ord_q 3 and
  log₃ 2 ≡ 1 (mod ord_q 2), and then fixes n mod ord_q 3. Among q < 3·10⁶ only q = 331 (n ≡ 121 mod 330) and
  q = 1210483 (n ≡ 379107 mod 403494) qualify (`certificate/p2.out`). The class 121 mod 330 is the q = 331 class,
  and 11 | n there, which explains the observed pattern.
- q | gcd(2^n − 3, 3^n − 3) (q > 3) iff 3^(n−1) ≡ 1 and 2^n ≡ 3 (mod q). q = 487891 gives the class
  n ≡ 23491 (mod 487890), which meets 121 mod 330 in n ≡ 3438721 (mod 5366790). So a(n) ≥ 4 on that class.
- n₂ = 1186095 is in the q = 1210483 class, 88681 | gcd(2^n₂ − 1, 3^n₂ − 1), and gcd(2^n₂ − 3, 3^n₂ − 3) = 1
  (PARI/GP), so a(n₂) = 3 while n₂ ≡ 75 (mod 330). Other n in the same class with a(n) = 3: 1589589, 1993083,
  2396577, 3203565, 4414047, 5221035 (`certificate/cex.out`).

Lean: [witness](A214074/A214074_mathlib.lean).

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

### [A215944](A215944/): Coman's 5461(42k − 13) exception claim is false (counterexample 3048841)

**Source.** [A215944](https://oeis.org/A215944) (Fermat pseudoprimes to base 2 with three prime factors divisible by a
smaller base-2 pseudoprime). Comment by Marius Coman (Aug 2012): "Conjecture: The only Fermat pseudoprimes to base 2
divisible by a smaller Fermat pseudoprime to base 2 that can't be written as p*((m + 1)*p - m)*((n + 1)*p - n), where
m, n, p are natural numbers, are multiples of 5461 and can be written as 5461*(42*k - 13)." Checked there for the 30
listed terms (up to 2299081) and the first 15 such numbers with four prime factors. (OEIS text, CC BY-SA 4.0; no
counterexample in the entry, revision #23, Dec 2025, checked 2026-11-06.)

**Reading.** The claim is refuted under the broadest reading: p ≥ 1 any natural number (not only a prime factor),
m, n ≥ 0. A counterexample under it is a counterexample under every narrower reading.

**Result.** False. P = 3048841 = 61 · 151 · 331 is a base-2 Fermat pseudoprime, divisible by the smaller base-2
pseudoprime 49981 = 151 · 331, not divisible by 5461, and not of the form p((m+1)p − m)((n+1)p − n) for any natural
p, m, n. It is the least counterexample (it is a(36) of A215944, just past the terms Coman checked). Below 10¹³ there
are 56782 base-2 pseudoprimes divisible by a smaller one; 4042 of them fail the strict reading (p a prime factor,
m, n ≥ 1) without being 5461(42k − 13), and 4019 fail even the broad reading.

**Argument.** (m+1)p − m = p + m(p − 1), so P = p·A·B with A ≡ B ≡ p (mod p − 1) and A, B ≥ p. p, A, B divide P,
so they are among its 8 divisors; none of the triples with product P satisfies the congruences (checked
exhaustively). p = 0, 1 give 0 and 1.

Lean: [witness](A215944/A215944_mathlib.lean).

### [A216971](A216971/): every entry of row n is divisible by n

**Source.** [A216971](https://oeis.org/A216971) (Geoffrey Critzer, Sep 21 2012): T(n,k) is "the number of functions
f:{1,2,...,n}->{1,2,...,n} that have exactly k nonrecurrent elements mapped to some (one or more) recurrent
element", n >= 1, 0 <= k <= n-1. Comment: "Conjecture: every entry in row n is divisible by n. - _Jon Perry_, Sep 21
2012". (OEIS text, CC BY-SA 4.0, revision #43 of Aug 09 2022, checked 2026-11-06.)

**Reading.** x is recurrent for f if f^m(x) = x for some m >= 1 (the entry's comment). T(n,k) counts f with exactly
k elements x such that x is not recurrent and f(x) is recurrent. This reproduces rows 1..6 by brute force
(certificate/check.py).

**Result.** True: n divides T(n,k) for all n >= 1 and all k.

**Argument.** Let R(f) be the set of recurrent points; it is nonempty (n >= 1, finiteness) and f permutes it.
Fix r >= 1 and let S be the set of f with statistic k and |R(f)| = r.
1. *Double count.* Count pairs (f, x) with f in S and x in R(f): this is r|S|. Relabelling f by the transposition
   (x 0), f -> t f t^-1, keeps the statistic and |R|, and moves "x recurrent" to "0 recurrent". So the count is
   n M with M = #{f in S : 0 in R(f)}. Hence r|S| = nM.
2. *Factor r!.* For a fixed set R, the f with R(f) = R and statistic k correspond bijectively to pairs (pi, g):
   pi a permutation of R and g such a function that fixes R pointwise (replace f on R by the identity, and glue
   pi back). Replacing f on R by any map that permutes R does not change which points are recurrent (an orbit
   that enters R never leaves it, so a point outside R returns to itself only along an orbit that avoids R, where
   the two functions agree) nor the statistic (it reads f only off R). So r! divides the count for each R, and
   r! divides M.
3. With M = r! q, r|S| = n r (r-1)! q, so |S| = n (r-1)! q. Summing over r gives n | T(n,k).

Equivalently T(n,k) = sum_{r>=1} C(n,r) r! r^k C(m-1,k-1) m^(m-k) (m = n - r, k >= 1), and C(n,r) r! =
n!/(n-r)! is a multiple of n for r >= 1. certificate/check.py checks this formula against brute force (n <= 6) and
the b-file (rows 1..32); it is not used in the Lean proof.

Lean: [full proof](A216971/A216971_mathlib.lean).

### [A217396](A217396/): 2^k − 2 twice a triangular or 3/2 a tetrahedral number only for k = 1, 2, 3, 5, 7, 13

**Source.** OEIS A217396 (Raphie Frank, 2012), data 1, 2, 3, 5, 7, 13. Conjecture (OEIS wiki
Talk:Conjectures/List, from the entry's former comments): this is the complete set of k with
2^k − 2 (a) twice a triangular number (A076046), or (b) 3/2 times a tetrahedral number (A217482),
"true to at least 1.41·10^1505" (C. R. Greathouse IV, Physics Forums, Nov 2010). Current entry
(checked 2026-11-06, #70, Aug 14 2026): renamed in June 2025 to "Prime indices of Euler's lucky
numbers"; the conjecture comment is no longer in the entry.

**Reading.** Under the current name the sequence is finite and complete by the classification of
Euler's lucky numbers (Rabinowitsch; Heegner–Baker–Stark class number one), so the entry itself
no longer states a conjecture. We settle the original characterization (a) ∨ (b), k ≥ 1.

**Result.** True. (a) 2^k − 2 = n(n+1) iff (2n+1)^2 + 7 = 2^(k+2), the Ramanujan–Nagell equation;
Nagell (1948): k ∈ {1, 2, 3, 5, 13}. (b) 2(2^k − 2) = 3·j(j+1)(j+2)/6 iff y^3 − y + 8 = 2^(k+2)
with y = j + 1. **New:** the only integer solutions of y^3 − y + 8 = 2^m are
y ∈ {−2, −1, 0, 1, 3, 5, 8} (m = 1, 3, 3, 3, 5, 7, 9), so (b) holds exactly for k ∈ {1, 3, 5, 7}.
The union is {1, 2, 3, 5, 7, 13}. This also proves the conjecture in OEIS A217482 (the tetrahedral
numbers T with (3/2)T + 2 a power of 2 are 0, 4, 20, 84).

**Argument for (b).** K = Q(α), α^3 − α + 8 = 0: discriminant −431, signature (1,1), class
number 1, [O_K : Z[α]] = 2, fundamental unit ε = −6α − 13, and (2) = P1 P2 P3 with generators
π1 = (α^2 + α − 2)/2, π2 = (α^2 + 3α + 2)/2, π3 = α + 2, π1π2π3 = 2ε (`s1.gp`, `dep.gp`).
1. N(y − α) = f(y) = 2^m, so y − α = ±ε^a π1^b1 π2^b2 π3^b3 with b1 + b2 + b3 = m. In the
   2-adic embeddings v_Pi(y − α) = v_2(y − θ_i), θ_i the 2-adic roots of f, and the pairwise
   differences of the θ_i have 2-adic valuations 0, 0, 1. So two of the b_i are in {0, 1}.
2. Real embedding α1 ≈ −2.166: Λ = 3 log|y − α1| − m log 2 = 3a log|ε1| + Σ b_i l_i with
   l_i = 3 log|π_i(α1)| − log 2, and for y ≥ 10, 0 < Λ = 2 log(|y − α1|/|y − α2|) < 8·2^(−m/3)
   (α2 complex).
3. Matveev's lower bound (n = 3, D = 3; γ = |ε1|, |π_i(α1)|^3/2 and the product of the two small
   factors) gives m < 3.4·10^17 in each of the 12 cases (`baker.gp`).
4. Dujella–Pethő reduction (continued fractions of log|ε1|/l_i; the four cases where both small
   exponents are 1 become homogeneous through l1 + l2 + l3 = 3 log|ε1| and use Legendre's bound
   with the largest partial quotient) lowers this to m ≤ 207, 60, 51, 50 in four rounds
   (`reduce.gp`).
5. Direct check of m ≤ 60 (and, as a cross-check, m ≤ 5000 by `direct.gp`) gives the 7 solutions.

Lean: [witness](A217396/A217396_mathlib.lean).

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

### [A217482](A217482/): tetrahedral numbers T with 3T/2 + 2 a power of 2

Lean: [witness](A217396/A217396_mathlib.lean).

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

### [A219197](A219197/): the square root of the A199033 g.f. has no coefficient = 3 (mod 4)

**Source.** [A219197](https://oeis.org/A219197) (Hanna, 2012): a = 1, 2, 9, 46, 253, ..., the self-convolution square
root of A199033(n) = sum_k C(n+k+1, n-k) C(2n-k+1, k). G.f. formula in the entry: A = G/sqrt(1 - 2xG^2 - 3x^2G^4),
G = 1 + xG^3. Comment: "Conjecture: a(n) is never congruent to 3 modulo 4." (OEIS text checked 2026-11-06.)

**Result.** True. Moreover a(n) is odd iff n is even and n AND 2n = 0 (no two adjacent 1-bits), and then a(n) = 1
(mod 4).

**Argument.** 1. *Lagrange form.* Put t = xG^2; then G = 1/(1-t) and x = t(1-t)^2. The entry's g.f. becomes
   A = (1-t)^(-1) (1-2t-3t^2)^(-1/2), and Lagrange inversion ([x^n] H = [t^n] H(t) phi^n (1 - t phi'/phi),
   phi = (1-t)^(-2)) gives a(n) = [t^n] S(t) (1-t)^(-2n-2), S = sqrt((1-3t)/(1+t)).
2. *S mod 4.* (1-3t)/(1+t) = 1 - 4u with u = t/(1+t), so S = sqrt(1-4u) = 1 - 2 sum_{k>=1} Cat(k-1) u^k. Cat(k-1) is
   odd iff k is a power of 2, and u^(2^j) = t^(2^j)/(1+t^(2^j)) (mod 2). Hence S = 1 + 2W (mod 4) with
   W = sum_m (v2(m) + 1) t^m (mod 2), and
   a(n) = C(3n+1, n) + 2 E(n) (mod 4),  E(n) = sum_{1<=m<=n, v2(m) even} C(3n+1-m, n-m).
3. *Parity.* C(3n+1, n) = C(n + (2n+1), n) is odd iff adding n and 2n+1 has no carry, i.e. n even and n AND 2n = 0.
   By Lucas, C(3n+1-m, n-m) = C(k + (2n+1), k) with k = n-m is odd iff k AND (2n+1) = 0, so
   E(n) = #{0 <= k < n : k AND (2n+1) = 0, v2(n-k) even} (mod 2).
4. *C(3n+1, n) mod 4.* From (1+t)^(2x) = (1+t^2+2t)^x = (1+t^2)^x + 2xt(1+t^2)^(x-1) (mod 4), C(2x, 2y) = C(x, y)
   (mod 4); with C(2x+1, 2y) = C(2x, 2y)(2x+1)/(2x-2y+1) and C(2x+1, 2y+1) = C(2x, 2y)(2x+1)/(2y+1) and
   2z+1 = (-1)^z (mod 4), a carry-free C(a, b) is (-1)^N (mod 4), N = #{i : a_(i+1) = a_i = 1, b_(i+1) != b_i}. For
   a = 3n+1, b = n (n even, no adjacent 1-bits) this is N(n) = popcount(n) + #{i >= 0 : n_(i+1) = 1, (2n+1)_i = 1}.
5. *E = N (mod 2).* Write n = 2^e + n' with n' < 2^(e-1) (top bit e, next bit e2 <= e-2 if n' > 0). The k >= 2^e
   are 2^e + k'' with k'' counted by E(n'). The k < 2^e range over the span of the free positions F = {1..e-1}
   minus {e_j + 1 : j >= 2}; k = n' gives v2 = e, and for k != n', v2(n-k) = v2(n'-k) = v exactly for 2^|F cap (v, e-1]|
   values of k when v is in F (none otherwise). Mod 2 only v = max F survives, so this part is
   [max F even] + [e even]: 1 if e >= 2 and e2 != e-2 (or n' = 0), 0 if e2 = e-2 or e = 1. The same top-bit step
   changes N by 1 + [e2 = e-2] (by 1 + [e = 1] when n' = 0). Induction from E(0) = N(0) = 0 gives E = N (mod 2).
6. Hence for odd a(n): a(n) = (-1)^N + 2N = 1 (mod 4); otherwise a(n) is even. So a(n) is never 3 mod 4.

Lean: needs Mathlib.

### [A219431](A219431/): a(odd) ≡ 2 and a(even) ≡ 0 (mod 4)

**Source.** OEIS [A219431](https://oeis.org/A219431), logarithmic derivative of the g.f. of the
overpartitions of n² (A219430(n) = A015128(n²)). Comment: "Conjecture: a(2*n+1) == 2 (mod 4),
a(2*n) == 0 (mod 4)." (OEIS text, CC BY-SA 4.0.) A219430 states the equivalent form "log derivative
≡ 2x/(1 − x²) (mod 4)" as a conjecture too.

**Reading.** G(x) = Σ_{n≥0} A219430(n) xⁿ and Σ_{n≥1} a(n) xⁿ = x G′(x)/G(x), i.e.
Σ_{k=1}^{n} a(k) A219430(n−k) = n A219430(n) for n ≥ 1.

**Result.** True for all n ≥ 1.

**Argument.** 1. An overpartition of m is a partition in which the first occurrence of each part size may be overlined, so
   p̄(m) = Σ_λ 2^{d(λ)}, d(λ) = number of distinct part sizes. For m ≥ 1, d ≥ 1 and 2^d ≡ 0 (mod 4) for d ≥ 2,
   so p̄(m) ≡ 2·#{λ ⊢ m with one part size} = 2τ(m) (mod 4) (one part size s ⇔ s | m).
2. τ(n²) = Π (2e_p + 1) is odd, so b(n) := A219430(n) ≡ 2 (mod 4) for n ≥ 1, and b(0) = 1.
3. a(n) = n b(n) − Σ_{k=1}^{n−1} a(k) b(n−k). By strong induction all a(k) are even, so each a(k) b(n−k)
   is ≡ 0 (mod 4), and a(n) ≡ n b(n) ≡ 2n (mod 4).

Lean: [full proof](A219431/A219431_mathlib.lean).

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

### [A225004](A225004/): a(n) divides n²

**Source.** [A225004](https://oeis.org/A225004), a(n) = the largest multiple of n with fewer than twice as many
divisors as n. Comment: "Conjecture: a(n) is always a divisor of n^2." (OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True: every positive multiple m of n with τ(m) < 2τ(n) divides n², so in particular a(n) | n²
(and the maximum exists, at most n²).

**Argument.** Let n | m, m > 0, and suppose v_p(m) = f > 2e with e = v_p(n) for some prime p. Write
m = p^f m', n = p^e n' with p ∤ m', n'. Then n' | m', so τ(n') ≤ τ(m'), and
τ(m) = (f+1)τ(m') ≥ (2e+2)τ(n') = 2τ(n). Hence τ(m) < 2τ(n) forces v_p(m) ≤ 2v_p(n) for every p, i.e. m | n².

Lean: [full proof](A225004/A225004_mathlib.lean).

### [A225660](A225660/): a(n) is odd for n > 9

**Source.** [A225660](https://oeis.org/A225660) (Clark Kimberling, 2013): number of nonrepeating vectors in the
counting procedure H(0) = binary digits of n, H(q+1) = F(H(q)), where F(S) = (f(0), ..., f(max S)) and f(i) is the
number of occurrences of i in S. Comment: "Conjecture: if n>9, then a(n) is odd." (OEIS text, CC BY-SA 4.0, revision
#14 of Dec 04 2016, checked 2026-11-06.)

**Reading.** a(n) = least i such that H(i) occurs again later; this reproduces the data (e.g. a(7) = a(9) = 0
because 111 and 1001 lie on a cycle).

**Result.** True: a(n) is odd for every n > 9.

**Argument.** 1. *Cycles.* The set C = {002, 011, 03, 1001, 111, 12, 201, 22} is closed under F and F^6 is the identity on C
   (cycles 12 -> 011 -> 12 and 22 -> 002 -> 201 -> 111 -> 03 -> 1001 -> 22). If the orbit of a vector meets C,
   then H(i) repeats iff H(i) is in C (a periodic H(i) equals F^{pT}H(i), which lies in C once the orbit is in C),
   so a(n) is the first time the orbit meets C.
2. *First step.* For n >= 1, F(bits) = (z, o), the numbers of 0s and 1s; for n >= 8, z + o >= 4 and o >= 1. For
   n > 9 the binary word of n is not in C (the members of C read as binary numbers are at most 9), so
   a(n) = 1 + (hitting time of C from (z, o)).
3. *Pairs return in an even number of steps.* For z != o with q = max(z, o): F(z, o) is the word of length q+1 with
   1 at positions z and o, and F^2(z, o) = (q-1, 2). For m >= 3: (m, m) -> 0^m 2 -> (m, 0, 1) -> 1 1 0^{m-2} 1 ->
   (m-2, 3). The intermediate words have length >= 6 or maximum >= 5, so they are not in C when max >= 5.
4. *Induction on max(z, o).* For pairs with z + o >= 4, o >= 1 and max <= 4 the hitting time is even (finite check).
   For max >= 5, step 3 reaches a pair with smaller max, still with sum >= 4 and o in {2, 3}, after 2 or 4 steps.
   So the hitting time from (z, o) is even and a(n) is odd.

Lean: [full proof](A225660/A225660_mathlib.lean).

### [A225919](A225919/): the greedy harmonic-block sequence for f(k) = 1/(k+4) is linearly recurrent

**Source.** OEIS [A225919](https://oeis.org/A225919): a(1) = 1, a(n) = least k such that
f(a(n−1)+1) + ... + f(k) > f(a(n−2)+1) + ... + f(a(n−1)) (n > 1), f(k) = 1/(k+4); a(2) = 11 from comparison with 1
(the entry's example). Comment: "Conjecture: a(n) is linearly recurrent. See A225918 for details." A225918 lists
the conjectured recurrence coefficients (4, −4, 3, −2) for this f. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True: a(n) = 4a(n−1) − 4a(n−2) + 3a(n−3) − 2a(n−4) for all n ≥ 5 (a(1..4) = 1, 11, 40, 124).

**Argument.** Let r(n) be the recurrence solution, x_n = r(n) + 9/2, F(k) = H_(k+4) (harmonic number), so the
rule compares F(k) − F(a(n−1)) with F(a(n−1)) − F(a(n−2)).
1. *Harmonic bounds* (D. W. DeTemple, Amer. Math. Monthly 100 (1993) 468–470):
   1/(24(m+1)^2) < H_m − ln(m + 1/2) − γ < 1/(24m^2). So F(k) = ln(k + 9/2) + γ + ε with ε of size 1/(24k^2).
2. *Sufficient conditions.* With Q_n = x_n x_(n−2) − x_(n−1)^2 and P_n = x_(n−2) − Q_n, using
   ln(1+u) ≥ u/(1+u) and ln(1−v) ≤ −v: (S1) Q_n > 0 and Q_n/(x_n x_(n−2)) > 1/(12(r(n−1)+4)^2) imply the rule
   accepts k = r(n); (S2) P_n > 0 and P_n/x_(n−1)^2 ≥ 1/(24(r(n)+3)^2) + 1/(24(r(n−2)+4)^2) imply it rejects
   k = r(n) − 1. So, by induction, a(n) = r(n).
3. *Small n.* (S1), (S2) hold for 3 ≤ n ≤ 60 (exact rational arithmetic).
4. *Large n.* u_n = r(n) + 13/3 satisfies u_n = 3u_(n−1) − u_(n−2) + 2u_(n−3), whose characteristic polynomial is
   (x − R)(x^2 − (3−R)x + 2/R), R ≈ 2.89329 the real root of x^3 − 3x^2 + x − 2. For w_n = u_n − R u_(n−1) and λ
   a complex root of the quadratic (|λ|^2 = 2/R < 1), z_n = w_n − λ̄ w_(n−1) = λ z_(n−1), so |w_(n−1)| ≤
   |z_N|/Im λ for n ≥ N. Exactly, e_n := Q_n/x_(n−2) = (R−1)^2/6 + w_n − R w_(n−1) − (w_(n−1) − (R−1)/6)^2/x_(n−2).
   At N = 60 interval arithmetic gives |e_n − (R−1)^2/6| ≤ 1.1·10^(−5) for n > 60, with (R−1)^2/6 ≈ 0.5974; so
   0.3 ≤ e_n ≤ 0.9, and also x_n ≤ 3x_(n−1), x_(n−2) ≥ 30. Then (S1): Q_n/(x_n x_(n−2)) = e_n/x_n ≥ 0.1/x_(n−1)
   > 1/(3x_(n−1)^2); (S2): P_n/x_(n−1)^2 = x_(n−2)(1 − e_n)/x_(n−1)^2 ≥ 1/(90 x_(n−2)) ≥ 1/(6 x_(n−2)^2), which
   bounds the right side.

Lean: —.

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

### [A227345](A227345/): a distinct-part partition of n with boundary size k exists iff 3k^2/4 <= n

**Source.** [A227345](https://oeis.org/A227345), triangle T(n, k), 1 <= k <= n: number of partitions of n into
distinct parts with boundary size k, where the boundary size counts the parts p for which not both p-1 and p+1
are parts. Comment: "Conjecture: there exists a partition (into distinct parts) of n with boundary size k if and
only if 0 < k^2 * 3/4 <= n. - _Patrick Devlin_, Jul 13 2013" (OEIS text, CC BY-SA 4.0; still a conjecture in
revision #32, May 15 2025, checked 2026-11-06).

**Result.** True. For n >= 1, T(n, k) > 0 iff k >= 1 and 3k^2 <= 4n. Equivalently, the least n with boundary
size k is ceil(3k^2/4) (3m^2 for k = 2m, 3m^2 + 3m + 1 for k = 2m + 1), and every larger n also occurs. This also
proves the formula a(n) = floor(2 sqrt(n/3)) of A227568 (largest boundary size for n), stated there without proof.

**Argument.** Let S be the set of parts and B its boundary parts, |B| = k.
1. *No three consecutive boundary parts.* If x, x+1, x+2 are all in B, then x+1 has both neighbours in S, so it is
   not a boundary part.
2. *Counting.* A set of positive integers up to M with no three consecutive integers has at most (2M+2)/3
   elements (strip off M-2, M-1, M, of which at most two occur, and induct).
3. *Sum.* For such a set B with k elements, 4 * sum(B) >= 3k^2 + (k mod 2). Induct by removing the largest element
   M: by step 2, 2M >= 3k - 2, and 2M >= 3k - 1 when k is odd. Hence n = sum(S) >= sum(B) >= 3k^2/4. Also k >= 1,
   since the largest part is always a boundary part.
4. *Construction.* Let A_m = {1, 2, 4, 5, ..., 3m-2, 3m-1} (pairs {3j+1, 3j+2}, j < m): sum 3m^2, boundary size 2m.
   Boundary size is additive over pieces separated by a missing integer. For k = 2m and n >= 3m^2 take
   A_{m-1} ∪ {3m-2, b} with b = n - 3(m-1)^2 - (3m-2) >= 3m-1. For k = 2m+1 and n >= 3m^2 + 3m + 1 take
   A_m ∪ {c} with c = n - 3m^2 >= 3m+1.

Lean: [full proof](A227345/A227345_mathlib.lean).

### [A227370](A227370/): an involution made of the transpositions (2k-1, 2k), k in A061887

**Source.** [A227370](https://oeis.org/A227370) (A. Karttunen, 2013): "Permutation which maps between A227368 and
A227369", a(n) = A227183(A227369(n)). Comments: "Conjecture 1: This is an involution ... Conjecture 2: (which would
automatically imply the conjecture 1): the only transpositions (used to compose the permutation) are of adjacent
terms 2k-1 and 2k, where A061887 gives the values of k. This is true at least for the first 35 transpositions (up
to k=60)." A227368(N) is the least x whose run-length partition (A227183) sums to N; A227369 is A227368 sorted.
A061887 = numbers in [2j^2, 2j^2 + 2j]. (OEIS text, revision #14, checked 2026-11-06.)

**Reading.** As in [OEIS/A227786](A227786/README.md): the code of a partition with k parts and largest part m
has m + k - 1 bits; read from the top it has runs r_1, ..., r_k (r_1 a run of 1s, then alternating), with
r_t = d_t + 1 for t < k (d_t the drops) and r_k = smallest part. a(n) is the N whose minimal code is the n-th
smallest minimal code.

**Result.** Both conjectures are true. Let c(N) = A227368(N). For N ≥ 2, c(N) < c(N-1) exactly when N is even
and s^2 ≤ N ≤ s^2 + 2s for some even s ≥ 2 (that is N = 2k, k in A061887, k ≥ 2), and the codes sorted
increasingly are c(0), c(1), ... with exactly these adjacent pairs swapped. So A227370 is the product of the
disjoint transpositions (2k-1, 2k), k in A061887, k ≥ 2, hence an involution.

**Argument.** From A227786 (Lean-proved there: `LL`, `F4`, `G_opt`): the minimal code has length
L(N) = min{m + k - 1 : mk ≥ N}; it is the best, over the pairs (m, k) with m + k - 1 = L(N) and D = mk - N ≥ 0
(then D < min(m, k)), of the greedy code: d_t = 0 at odd t < k-1, the first even t < k-1 with k - t ≤ D gets
d_t = 1, and d_{k-1} takes the rest. Codes of different lengths are ordered by length, and L is nondecreasing.

1. *Shape of a candidate.* Compare each code with the alternating word 1010... . A candidate either first deviates
   with a 0 for a 1 (sign −) at the odd bit φ = least odd number ≥ k - D + 1 (a doubled 0-run at the even run
   p = φ - 1, or the final 0-run when D = 0 and k is even, or a lengthened run k-1 when k is odd and D ≤ 2), or,
   when k - D is odd and D ≤ 1, first deviates with a 1 for a 0 (sign +). The smaller code is the one with the
   earlier sign − deviation; sign + candidates lose to any sign − candidate.
2. *Blocks.* L = 2s - 1 for N = s^2 - E (0 ≤ E ≤ s - 1), pairs (s ± j, s ∓ j) with D = E - j^2; L = 2s for
   N = s^2 + s - E (0 ≤ E ≤ s - 1), pairs (s + 1 + j, s - j), (s - j, s + 1 + j) with D = E - j(j + 1). By step 1
   only k in {s - 1, s, s + 1} can reach the least φ; comparing the runs after the common deviation (first
   difference at run s - 1 or s - 2, whose bit value is its parity) gives the winners (m, k):
   - O, s - E even: (s + 1, s - 1) if s is odd, (s, s) if s is even;
   - O, s - E odd: E = 0: (s, s); E = 1: (s - 1, s + 1); E = 2: (s, s); E ≥ 3: (s + 1, s - 1) if s is even,
     (s, s) if s is odd;
   - V, s - E even: (s + 1, s); V, s - E odd: (s, s + 1) if s is even or E = 0, (s + 2, s - 1) if s is odd.
3. *Consecutive codes.* Group the N of a block by the doubled-run position p. Within a group of two (E, E - 1)
   the codes agree up to the end of the alternating middle part; the next bits decide: in O-blocks with s odd and
   V-blocks with s even the larger N has the smaller code (its tail is 0s, the other's 1s or 001...), in O-blocks
   with s even and V-blocks with s odd the order agrees with N; in O-blocks with s even the only inversion is the
   pair (s^2 - 1, s^2) (E = 1 has a sign + deviation, E = 0 the final 0-run). Groups with a smaller p deviate
   earlier, so every code of a group is below every code of the next group. The inversions are therefore exactly
   the even N in (s(s-1), s^2] for odd s, in (s^2, s^2 + s] for even s, and N = s^2 for even s; for even s these
   make up the even N in [s^2, s^2 + 2s].

Lean: [checked](A227370/A227370_mathlib.lean).

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

### [A227786](A227786/): positions of 2 in A227761

**Source.** [A227786](https://oeis.org/A227786) (A. Karttunen, Jul 31 2013): "Take squares larger than 1,
subtract 3 from even squares and 2 from odd squares", a(n) = (n+1)^2 - 2 - (n mod 2) = 1, 7, 13, 23, 33, 47, ...
Comment: "Conjecture: from n>=2 onward, a(n) gives the positions of 2's in A227761." The same conjecture
is in [A227761](https://oeis.org/A227761), which also asks "Are there any terms larger than 2?"
(OEIS text, CC BY-SA 4.0, revision #32 of A227786, checked 2026-11-06.)

**Reading.** A227183(x): read the binary runs of x from the least significant end, c1, c2, ..., ck; the
parts are c1, c1 + c2 - 1, c1 + c2 + c3 - 2, ... (A129594 coding). A227368(N) is the least x with
A227183(x) = N, and A227761(N) is the largest difference between successive parts of that partition
(0 for N < 2). This reading reproduces the b-files of A227368 and A227761 (N <= 132).

**Result.** True. For every N, A227761(N) = 2 exactly when N = a(n) for some n >= 2, i.e. N = j^2 - 2
with j >= 3 odd or N = j^2 - 3 with j >= 4 even. Also A227761(N) <= 2 for all N, which answers the
question in A227761: there are no terms larger than 2.

**Argument.** Write the code of a partition with k parts and largest part m from the top as runs
r_1, ..., r_k: r_t = (q_t - q_{t+1}) + 1 for t < k and r_k = q_k, where q_1 = m >= q_2 >= ... >= q_k are
the parts. The bit length is m + k - 1, and among codes of equal length the integer is smaller iff at
the first differing run an odd-numbered run is shorter or an even-numbered run is longer.
Put d_t = q_t - q_{t+1} (t < k) and D = mk - N = sum_t (k - t) d_t.

1. *Length.* Every N in [m + k - 1, mk] is the sum of a partition with k parts and largest part m, so
   the minimal code has m + k - 1 = L(N) = min{m' + k' - 1 : m'k' >= N}. If D >= m (or D >= k) the
   pair (m, k-1) (or (m-1, k)) would give a shorter code, so 0 <= D < min(m, k) for every pair (m, k)
   with m + k - 1 = L(N) and mk >= N. For N >= 4 also m, k >= 2.
2. *Greedy drops.* For fixed (m, k) the best code takes d_1 = 0, d_2 as large as possible, d_3 = 0,
   d_4 as large as possible, ..., and d_{k-1} = the remainder (weight 1). With D < k each greedy
   step on an even position with weight w >= 2 sees a remainder < w + 2, so d_t <= 1 there; the last
   drop (weight 1) is <= 2, and it is 2 exactly when k is odd and D = 2 (if D >= 3 the first even
   weight w <= D leaves D - w <= 1). So A227761(N) <= 2, with equality iff the winning pair has
   k odd and D = 2.
3. *Which pair wins.* Suppose the winner has k odd, D = 2, so its runs are 1^(k-2), 3, m-2.
   - m = k + 1: the pair (m+1, k-1) has D = 0 and runs 1^(k-2), m+1; position k-1 is even and
     m+1 > 3, so it is better.
   - m >= k + 3 or m <= k - 1: the neighbour (m-1, k+1) resp. (m+1, k-1) has D' = |m - k| + 1 >= 2 and
     its greedy drops put a 1 on an even position before k-1 (the weight there is the largest
     weight <= D' of the right parity, which is >= 2), where the original has 1; so it is better.
   - m = k gives N = k^2 - 2 and m = k + 2 gives N = (k+1)^2 - 3, both of the form a(n).
   Conversely, for N = j^2 - 2 (j odd >= 3) the valid pairs are (j, j) with D = 2 and (j +- 1, j -+ 1)
   with D = 1, and (j, j) beats both; for N = j^2 - 3 (j even >= 4) the valid pairs are (j+1, j-1) and
   (j-1, j+1) with D = 2 and (j, j) with D = 3, and (j+1, j-1) wins. In both cases the winner has
   k odd and D = 2.

Lean: [full proof](A227786/A227786_mathlib.lean).

### [A228095](A228095/): Sun's Legendre-symbol determinants vanish on residue classes

**Source.** Three conjectures of Zhi-Wei Sun (2013), with p = p_n the n-th prime and (·/p) the Legendre symbol:
- [A228095](https://oeis.org/A228095): det[((i^2 + 3ij + 3j^2)/p)]_{0<=i,j<=p-1} (Sun's [3,3]_p). "Conjecture: a(n) = 0
  if p_n == 5 (mod 6)." (revision #44 of Aug 25 2021)
- [A225611](https://oeis.org/A225611): det[((i^2 + 6ij + j^2)/p)]_{1<=i,j<=p-1} (Sun's (6,1)_p). "Conjecture: We have
  a(n) = 0 if p_n == 3 (mod 4)." (revision #52 of Aug 25 2021)
- [A226163](https://oeis.org/A226163): det[((i^2 - ((p-1)/2)! j)/p)]_{1<=i,j<=(p-1)/2}. "Conjecture: a(n) = 0 if and only if
  p_n == 3 (mod 4)." (revision #20 of Aug 19 2026, which links a proof)
(OEIS text checked 2026-11-06.)

**Result.** - A228095: true. For p ≡ 5 (mod 6) the vector v_j = (j/p) is a nonzero kernel vector.
- A225611: true (known: Krachun, Petrov, Sun, Vsemirnov 2020); reproved here with the kernel vector v_j = (j/p).
- A226163: true (known: OEIS Open project, Adamczewski 2026, with a Lean proof); not redone here.

**Argument.** Write χ for the Legendre symbol on F_p.
- *A228095.* Row i of M v is Σ_y χ(i^2 + 3iy + 3y^2) χ(y). For i = 0 it is χ(3) Σ_y χ(y^3) = 0, because cubing permutes
  F_p when p ≡ 2 (mod 3). For i ≠ 0, put y = it: the row is χ(i^3) Σ_t χ(t + 3t^2 + 3t^3), and t = 1/s turns the
  summand into χ((s+1)^3 - 1) (the factor s^-4 is a square), so the sum is Σ_w χ(w^3 - 1) = Σ_z χ(z - 1) = 0.
- *A225611.* As above, row a of M v is χ(a^3) S with S = Σ_t χ(t^3 + 6t^2 + t). For p ≡ 3 (mod 4), -1 is a non-square,
  so every t ≠ 0 is u^2 or -u^2 (twice each) and 2S = (U - 1) - (T - 1) with U = Σ_u χ(u^4 + 6u^2 + 1),
  T = Σ_u χ(u^4 - 6u^2 + 1). Under u ↦ w = (1+u)/(1-u), w^4 - 6w^2 + 1 = -4(u^4 - 6u^2 + 1)/(1-u)^4 and
  w^4 + 6w^2 + 1 = 8(1 + u^4)/(1-u)^4. The first makes T odd under the involution apart from the end points u = 1,
  w = -1, giving T = -1. The second gives U = χ(2)(Σ_u χ(1 + u^4) - χ(2)) + χ(8), and Σ_u χ(1 + u^4) = -1 (from
  Σ_t χ(t^2 + 1) = -1 and Σ_t χ(t^3 + t) = 0), so U = -1. Hence S = 0. (S is minus the Frobenius trace of
  y^2 = x(x^2 + 6x + 1), which has CM by Z[2i]; the substitution is an explicit form of its supersingularity.)

Lean: [full proof](A228095/A228095_mathlib.lean).

### [A228469](A228469/): least c with an alternating trace (Kimberling)

**Source.** OEIS [A228469](https://oeis.org/A228469) and [A228471](https://oeis.org/A228471) (Clark Kimberling,
Aug 22 2013), both defined by a(n) = 6a(n-2) + a(n-4) with a(0..3) = 2, 8, 13, 49 and 3, 5, 19, 31.
Conjecture in each: a(n) is the least positive integer c for which there is a positive integer b with trace(b,c)
equal to the first letters of 01010... (A228469), 10101... (A228471). The trace (A228469): from (x,y), with
u(x,y) = (y, x mod y), v(x,y) = (y, y - (x mod y)), apply w = min(u,v) until the second entry is the gcd,
recording 0 when w = u and 1 otherwise. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** min compares pairs with equal first entry, so w = u iff r <= y - r (r = x mod y; ties give 0).
The run stops when y divides x. This gives trace(18,13) = 010 and trace(30,19) = 101 as in the entries' examples
(the intermediate pairs printed in A228471's example are misprinted; the trace is right). With offset 0 the
term a(n) belongs to the first n+1 letters (a(0) = 2 for the word 0, a(0) = 3 for the word 1).

**Result.** Both conjectures are true for all n. More generally, for every nonempty 0-1 word w the least such c is
given by a backward greedy recursion.

**Argument.** Let the run be (y_{-1}, y_0) = (b, c), (y_0, y_1), ..., (y_{L-1}, y_L), y_L = gcd. Step k sends
(y_{k-2}, y_{k-1}) to (y_{k-1}, y_k); letter 0 means y_{k-2} = q y_{k-1} + y_k with 2y_k <= y_{k-1}, letter 1 means
y_{k-2} = q y_{k-1} - y_k with 2y_k < y_{k-1}. Since 2y_{k-1} <= y_{k-2}, q >= 2 for letter 0 and q >= 3 for
letter 1. In the coordinates t = y_{k-1} - 2y_k >= 0, u = y_k >= 1 the backward step is
(t,u) -> ((q-2)(t+2u) + u, t+2u) for letter 0 and ((q-2)t + (2q-5)u, t+2u) for letter 1: monotone in t, u, q.
So c = t + 2u is smallest with y_L = 1, the smallest y_{L-1} (2 or 3 by the last letter) and the smallest q at every
step; the resulting pairs are realised (b = 2c + y_1 or 3c - y_1). For alternating words, two backward steps act
by (a,b) -> (5a+3b, 2a+b) (pattern 01) or (7a-2b, 3a-b) (pattern 10); both matrices have trace 6 and determinant
-1, so the minima satisfy x(n+4) = 6x(n+2) + x(n), and the first four values are 2, 8, 13, 49 and 3, 5, 19, 31.

Lean: [full proof](A228469/A228469_mathlib.lean).

### [A228471](A228471/): least c whose trace begins 1010... (Kimberling)

Lean: [full proof](A228469/A228469_mathlib.lean).

### [A228916](A228916/): indices of primes in A108300 are 1 and multiples of 3

**Source.** [A228916](https://oeis.org/A228916), indices n with A108300(n) prime, where
[A108300](https://oeis.org/A108300)(n) = 3a(n−1) + a(n−2), a(0) = 1, a(1) = 5. Comment: "Conjecture: for n>1 a(n)
is a multiple of 3." (OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True: if A108300(n) is prime then n = 1 or 3 | n.

**Argument.** A108300 mod 10 is periodic with period 12: 1, 5, 6, 3, 5, 8, 9, 5, 4, 7, 5, 2. For n ≡ 2 (mod 3)
the residue is even, and for n ≡ 1 (mod 3) it is 5. The sequence is increasing with a(2) = 16, so for n ≥ 2 the
term is an even number > 2 or a multiple of 5 larger than 5, hence composite. Only n = 1 (a(1) = 5) and
n ≡ 0 (mod 3) remain.

Lean: [full proof](A228916/A228916_mathlib.lean).

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

### [A005376](A005376/): a(n) is approximately c*n, c the real root of x^5 + x - 1

**Source.** [A005376](https://oeis.org/A005376), a(n) = n - a(a(a(a(a(n-1))))), a(0) = 0. Comment by Benoit
Cloitre (Nov 05 2002): "Conjecture: a(n) is approximately c*n, where c is the real root of x^5+x-1 = 0,
c=0.754877666...". (OEIS text, CC BY-SA 4.0, revision #68, checked 2026-11-06.)

**Reading.** "Approximately c*n" read as a(n)/n -> c.

**Result.** True, and known: a(n) = c*n + O(log n) (stronger than the conjecture).

**Argument (known, summarised).** Let L(i) = L(i-1) + L(i-5) (A003520, 1, 2, 3, 4, 5, 6, 8, 11, ...). Every n
has a unique greedy representation as a sum of L(i) with indices at least 5 apart, and a(n) is obtained by
replacing each L(i) with L(i-1) (the "Lamé antecedent" rule in the entry; Meek-van Rees type numeration
theorem for generalised Hofstadter functions). The characteristic polynomial factors as
x^5 - x^4 - 1 = (x^3 - x - 1)(x^2 - x + 1); its dominant root is the plastic number rho = 1.3247..., and
c = 1/rho satisfies c^5 + c - 1 = 0. Then L(i-1) - c L(i) is a combination of powers of the other roots, two
of modulus < 1 and two of modulus 1, so each digit contributes O(1) error and a(n) - c n = O(number of
digits) = O(log n). Proofs: K. Dilcher, "On a class of iterative recurrence relations", Applications of
Fibonacci Numbers 5 (1993) 143-158; P. Letouzey, arXiv:2502.12615 (2025), which states that almost all of
the article is formalised in Coq/Rocq. The entry's own comment (P. Letouzey, Mar 06 2025) records
a(n) = c*n + O(ln n).

Lean: —.

### [A007413](A007413/): counts of 1's between consecutive 2's of A076826

**Source.** [A007413](https://oeis.org/A007413): "A squarefree (or Thue-Morse) ternary sequence: closed under
1->123, 2->13, 3->2. Start with 1." Comment: "Conjecture. The sequence is formed by the numbers of 1's between every
pair of consecutive 2's in A076826. - _Vladimir Shevelev_, May 31 2009". [A076826](https://oeis.org/A076826):
a(n) = 2*(Sum_{k=0..n} A010060(k)) - n. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** A007413 has offset 1 and is the fixed point of sigma: 1 -> 123, 2 -> 13, 3 -> 2 starting with 1.
A076826 has offset 0. The claim: for n >= 1, A007413(n) is the number of i with p_n < i < p_{n+1} and
A076826(i) = 1, where p_1 < p_2 < ... are the positions of the 2's.

**Result.** True: with t = Thue-Morse (A010060), A007413(n+1) = 2 + t(n) - t(n+1), and A007413(n) is the number of 1's
of A076826 between its n-th and (n+1)-th 2 for every n >= 1.

**Argument.** 1. *Fixed point.* Let u(n) = 2 + t(n) - t(n+1) (n >= 0). From t(2m) = t(m), t(2m+1) = 1 - t(m):
   u(2m) = 1 + 2t(m), u(2m+1) = 3 - t(m) - t(m+1). Put L(m) = 2m + t(m). Checking the four values of
   (t(m), t(m+1)) gives sigma(u(m)) = u(L(m)) ... u(L(m+1) - 1), so sigma maps the prefix of u of length m onto
   the prefix of length L(m). Since u(0) = 1, sigma^k(1) is the prefix of u of length l_k with l_0 = 1,
   l_{k+1} = L(l_k) >= k + 2. So A007413(n+1) = u(n).
2. *A076826.* Pairs (2j, 2j+1) contain one odious number each, so Sum_{k<2m} t(k) = m. Hence A076826(2m) = 2t(m),
   A076826(2m+1) = 1 (Cloitre's formula in the entry). The 2's are at 2x with t(x) = 1, i.e. at 2o(j), where
   o(j) = 2j + 1 - t(j) is the j-th odious number (j >= 0); the 1's are at the odd positions.
3. Between 2o(n-1) and 2o(n) there are o(n) - o(n-1) = 2 + t(n-1) - t(n) = u(n-1) = A007413(n) odd positions.

Lean: [full proof](A007413/A007413_mathlib.lean).

### [A007645](A007645/): OEIS A007645 = A002383 ∪ A162471 (proved), and the A002383 intersection conjecture (open)

**Source.** [A007645](https://oeis.org/A007645) (generalized cuban primes: "primes of the form x^2 + xy + y^2; or
primes of the form x^2 + 3*y^2; or primes == 0 or 1 (mod 3)"), comment "Conjecture: this sequence is
Union(A002383,A162471). - Daniel Tisdale, Jul 04 2009" (revision #116, Jul 19 2026). [A002383](https://oeis.org/A002383)
(primes k^2 + k + 1), comment "Conjecture: the set of these numbers, except 3, is the intersection of sets A085104
and A059055. See A225148. - Thomas Ordowski, May 02 2013" (revision #116, Nov 04 2025). A162471: "Prime divisors
of {n^2+n+1} which do not occur in A002383". A085104: primes 1 + n + ... + n^k with n > 1, k > 1 (Brazilian
primes). A059055: primes (b^k+1)/(b+1) with b, k positive. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** A007645 is taken in its first form, primes x^2 + xy + y^2 with x, y natural numbers (integer x, y
give the same primes: `nat_rep` turns any integer solution into a natural one).

**Result.** - A007645 = A002383 ∪ A162471: true (classical; proved in Lean here).
- A002383 \ {3} = A085104 ∩ A059055: the inclusion ⊆ is true; the inclusion ⊇ is open. It is equivalent to: every
  prime p = (n^q - 1)/(n - 1) = (b^r + 1)/(b + 1) with odd q, r >= 5 and n, b >= 2 is of the form c^2 + c + 1. With
  y = -b this is the Goormaghtigh equation (x^m - 1)/(x - 1) = (y^n - 1)/(y - 1) with one negative base; no such
  coincidence exists below 10^26 (search below), and no general result is known.

**Argument (A007645).** First, a prime is x^2 + xy + y^2 iff it is 0 or 1 mod 3. The form is never 2 mod 3
(check residues). Conversely 3 = 1 + 1 + 1, and for p ≡ 1 (mod 3) take s with p | s^2 + s + 1 (below). Among the
(m+1)^2 > p pairs (i, j) with 0 <= i, j <= m = floor(sqrt p), two give the same i - s j mod p (Thue's lemma); the
differences a, b satisfy a ≡ s b, so p | a^2 + ab + b^2, and 0 < a^2 + ab + b^2 <= 3m^2 < 3p. The value 2p is
impossible (it would force a, b even, so 4 | 2p). Hence p = a^2 + ab + b^2, and a sign change makes x, y natural.
Second, A002383 ∪ A162471 is the set of primes dividing some n^2 + n + 1 (k^2 + k + 1 divides
itself). If p | n^2 + n + 1 and p != 3, then n^3 ≡ 1 and n ≢ 1 (mod p), so n has order 3 and 3 | p - 1; and
3 | 1 + 1 + 1. Conversely p = 3 divides 1^2 + 1 + 1, and for p ≡ 1 (mod 3) Cauchy's theorem gives x of order 3 in
(Z/p)^*, so (x - 1)(x^2 + x + 1) = 0 with x != 1.

**Argument (A002383, partial).** For k >= 2, k^2 + k + 1 = 111 in base k (A085104 form) and
((k+1)^3 + 1)/((k+1) + 1) (A059055 form); 3 is not Brazilian. Conversely, if a prime in A085104 ∩ A059055 has a
representation with exponent 3 on either side, it is n^2 + n + 1 or b^2 - b + 1 = (b-1)^2 + (b-1) + 1, so in
A002383; an even number of digits gives a composite repunit. So a counterexample needs odd exponents q, r >= 5 on
both sides and no third representation c^2 + c + 1.

Lean: [full proof](A007645/A007645_mathlib.lean).

### [A007669](A007669/): A007669(n) = A178717(n−1) − 1 is false (first failure n = 8)

**Source.** [A007669](https://oeis.org/A007669) (offset 1), now dead: "Duplicate of A034343". Former name "Number of
orthogonal lattices in dimension n" (Schwarzenberger), data 1, 2, 4, 8, 16, 36, 80 until 2017. Comment, in the entry
from Sep 2010 until revision #12 (Nov 27 2017): "Conjecture (V. Kotesovec, 2010): a(n) = A178717(n-1) - 1".
(OEIS text, CC BY-SA 4.0.) [A178717](https://oeis.org/A178717) (offset 1): degree of the denominator of the GF for
k nonattacking queens on an n × n board, with Kotesovec's explicit formula
d(k) = 2k + 1 + Σ_{j=1}^{k−1} Σ_{i=F(k−j)+1}^{F(k−j+1)} 2j φ(i) (k > 1).

**Reading.** A007669 is read as [A034343](https://oeis.org/A034343) (Sloane's identification, via Schwarzenberger's
theorem): the number of binary linear codes of length n, any dimension, with no zero column, up to permutation of
coordinates (= loopless binary matroids on n points). A178717 is read through Kotesovec's formula, from which its data
are computed.

**Result.** False. The conjecture was made on the seven terms known in 2010 (it holds for 2 ≤ n ≤ 7). With
A034343(8) = 194 (data since the 2017 merge; Fripertinger, Wild) and A178717(7) = 197, it fails at n = 8:
194 ≠ 196. It fails again at n = 9 (506 ≠ 476) and for every n ≥ 9 in the data; a(n) grows like 2^{n²/4}/n!,
A178717 only like φ^{2n}.

**Argument (Lean, n = 20).** The 10 × 10 matrices A over GF(2) with no zero row give (2¹⁰ − 1)¹⁰ = 1023¹⁰ different
codes {(x, Ax)} of length 20 with no zero column. Each equivalence class is the image of the symmetric group, so it has
at most 20! members, and a(20) ≥ 1023¹⁰/20! > 5.15 · 10¹¹. Kotesovec's formula with φ(i) ≤ i ≤ F(19) = 4181 gives
A178717(19) ≤ 39 + 18 · 4181 · 38 · 4181 < 1.2 · 10¹⁰ (actual value 17202449). So a(20) ≠ A178717(19) − 1.

Lean: [full proof](A007669/A007669_mathlib.lean).

### [A008683b](A008683b/): a moved-corner divisibility matrix has determinant μ(n) and A074206(n) nonzero terms

**Source.** OEIS [A008683](https://oeis.org/A008683), comment by M. Granvik (Dec 08 2008): "Conjecture: Consider
the table A051731 and treat 1 as a divisor. Move the value in the lower right corner vertically to a divisor
position in the transpose of the table and you will find that the determinant is the Moebius function. The number
of permutation matrices that contribute to the Moebius function appears to be A074206." (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** The wording admits two concrete matrices (n × n, n ≥ 2); both satisfy both claims.
1. A = A051731 truncated (A(i, k) = 1 iff k | i), with the 1 at (n, n) moved up its column to row 1, so column n
   becomes e_1.
2. The Redheffer matrix (R(i, j) = 1 iff j = 1 or i | j: the transpose of A051731 with 1 "treated as a divisor"
   in the first column) with the entry (n, n) set to 0; this is the matrix of the A008683 comment on A143104.
"Contributing permutation matrices" = permutations σ with all entries M(i, σ(i)) nonzero.

**Result.** True for both readings and every n ≥ 2: det = μ(n), and the number of contributing permutations is
H(n) = A074206(n), the number of ordered factorizations of n.

**Argument.** - *Determinant, reading 1.* Expanding along column n, det A' = (−1)^(n+1) det N, N = A without row 1 and column n.
  A is unitriangular with inverse A^(−1)(i, k) = μ(i/k)[k | i] (Möbius inversion), and the cofactor formula
  gives μ(n) = A^(−1)(n, 1) = (−1)^(n+1) det N.
- *Determinant, reading 2.* det is linear in column n; removing e_n from column n subtracts the determinant of the
  (n−1) × (n−1) Redheffer matrix. By Redheffer's theorem (det of the k × k Redheffer matrix is the Mertens
  function M(k)), det = M(n) − M(n−1) = μ(n).
- *Count.* Reading 1: σ(1) = n is forced, and the remaining rows m = 2..n go injectively to columns 1..n−1 with
  σ(m) | m, so σ(m) ≤ m. Starting from n and following σ gives a strictly decreasing divisor chain
  n = c_0 > c_1 > ... > c_k = 1 (a value repeated would have two preimages); the rows off the chain are mapped
  among themselves with σ(m) ≤ m, which forces σ(m) = m. Chains correspond to ordered factorizations
  n = (c_0/c_1)(c_1/c_2)...(c_(k−1)/c_k). Reading 2: row n can only use column 1 (its only other candidate is
  (n, n) = 0), and rows 1..n−1 go to columns 2..n with i | σ(i); the same chain argument applies upward from 1.
  (Reading 1 is D. Callan's 2005 comment in A074206: H(n) is the permanent of N.)

Lean: [witness](A008683b/A008683b.lean).

### [A022344](A022344/): Fibonacci sequences in the Wythoff array and the product of characteristics

**Source.** [A022344](https://oeis.org/A022344) (Allan Wechsler's "J determinant"; a(n) = ⌊(n+1)τ⌋² − n⌊(n+1)τ⌋ − n²).
Comment of Kenneth J. Ramsey, Feb 11 2007: "Conjecture: Every pair of Fibonacci sequences, F1 and F2, appear in rows n
and m of Wythoff's Array, respectively and have respective characteristics a(n) and a(m). Also, there is a third
Fibonacci sequence F3, defined by F3(i) = F1(i) * F2(j+1) - F1(i+1)*F2(j) where j is held constant. The sequence F3
appears in row p of Wythoff's array and has the characteristic a(p) = a(n)*a(m)." The characteristic of a row is
|T(i)² − T(i−1)T(i+1)| (Ramsey, 2007 comment). (OEIS text, CC BY-SA 4.0, revision #45 of Nov 05 2025, checked
2026-11-06.)

**Reading.** "Fibonacci sequence": integer sequence with F(i+2) = F(i+1) + F(i), eventually positive (the rows of the
Wythoff array are positive); "appears in row n": agrees with row n from some index on, after a shift of index.
Rows are indexed so that row n has characteristic a(n) (A022344 has offset 0; the first Wythoff row 1, 2, 3, 5, ...
has characteristic 1 = a(0)).

**Result.** True up to sign, and known. (1) Every eventually positive Fibonacci sequence is, after finitely many
terms and a shift, a row of the Wythoff array (D. R. Morrison 1980); its characteristic is constant along the
sequence and equals that of the row. (2) F3 is a Fibonacci sequence with characteristic char(F1)·char(F2), since
D_{F3}(i) = D_{F1}(i)·D_{F2}(j) with D(i) = F(i+1)² − F(i)F(i+2) (the norm in Z[φ] is multiplicative). F3 is
eventually of constant sign but can be negative: F1 = F2 = Fibonacci numbers, j = 1 give F3(i) = −F(i−1). So the
row in the conjecture is that of |F3| (for F3 < 0, F3 itself is not a row). The product rule is Peter Munn's
A357097 (2022), stated there as A022344(A(x,y)) = A022344(x)·A022344(y).

**Argument.** (1) With x = F(i), y = F(i+1): D(i+1) = (x+y)² − y(x+2y) = x² + xy − y² = −D(i), so |D| is
constant. Since a positive Fibonacci tail is a row tail (Morrison), the characteristic is that row's, a(n).
(2) F3(i) is a fixed integer combination of F1(i), F1(i+1), so F3 satisfies the recurrence, and expanding gives
D_{F3}(i) = (y² − xy − x²)(v² − uv − u²) with u = F2(j), v = F2(j+1). F3 is not identically zero (D ≠ 0) and a
nonzero integer Fibonacci sequence is eventually of one sign, so |F3| eventually is a positive Fibonacci sequence,
hence a row tail p with a(p) = a(n)a(m).

Lean: [witness](A022344/A022344.lean).

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

### [A029905](A029905/): r(n) and h(n) are not complementary (row 120 of 3-row Chomp is in neither)

**Source.** OEIS [A029905](https://oeis.org/A029905), "r(n), where exists one-parameter family of
strategic partitions (k+p(n)+q(n), k+q(n), r(n)) for k = 0,1,2,... in Chomp", comment
"Conjectured to be complementary to h(n), see A029902", and A. E. Brouwer (May 31 2002):
"Maybe the conjecture is false - see the Brouwer link." h(n) is [A029902](https://oeis.org/A029902):
the strategic move on the g(n) X 3 rectangle is (h(n),2) (OEIS text, CC BY-SA 4.0).
Origin: Berlekamp-Conway-Guy, Winning Ways vol. 2, 598-600.

**Reading.** Positions of 3-row Chomp are (p,q,r), p >= q >= r >= 0 row lengths, the player
who must take the poisoned square loses ((1,0,0) is a P-position). The move (h,2) on the
g X 3 rectangle (g,g,g) leads to (g,g,h). So h ranges over the rows r for which some
(q,q,r), q > r, is a P-position. r(n) ranges over the rows r for which (k+P+Q, k+Q, r) is a
P-position for every k >= 0.

**Result.** False. Row r = 120 lies in neither set. For q >= 170 the P-positions in row 120
are (q+72, q, 120) for even q and (q+70, q, 120) for odd q (q - 170 even / odd), forever, and
no (q,q,120) is a P-position. Rows 0..119 and 121..125 each lie in exactly one of the two
sets, and the computed sets agree with the OEIS data of A029902 and A029905.

**Argument.** For q >= r let f(q,r) be the unique p with (p, min(p,q), min(p,q,r)) a
P-position (the positions with fixed q, r and varying p form a chain, each can move to every
lower one, so there is at most one P-position; there is at least one by the rule below).
Re-derived from the move rules: if some p' < q has (p',p',min(p',r)) a P-position then
f(q,r) = p'; otherwise f(q,r) is the least p >= max(q,1) that is not among
f(a, min(r,a)) (a < q, moves in row 1) and f(q,b) (b < r, moves in row 2). This rule is
checked against a brute-force game solver on all boards with p <= 14 (`chomp_cert.py`).
A row with a diagonal P-position is constant from then on (the finite case, giving h).
Otherwise, for q beyond the starting points of all lower rows, f(q,r) = q + t with t the
least t >= 1 outside S_q ∪ D_q, where S_q = {v - q : v already used in row r, v >= q} and
D_q = {f(q,b) - q : b < r infinite rows}. Each lower infinite row is certified eventually
periodic, so D_q is periodic in q, and (q mod L, S_q) evolves by a deterministic finite rule
S_{q+1} = {s-1 : s ∈ S_q ∪ {t}, s >= 1}. A repeated state proves the row periodic forever.
`chomp_rows.py` does this row by row for r <= 125 (rows 0..119 have period 1); for row 120
the state repeats with period 2 and offsets (72, 70), t >= 1 throughout, and f(q,120) != q
for 120 < q < 170 is checked directly. Hence (q,q,120) is never a P-position (120 not in h)
and f(q,120) - q is not eventually constant (no one-parameter family, 120 not in r).

Lean: —.

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

### [A053029](A053029/): which m have 4 (resp. 1) zeros in the Fibonacci numbers mod m

**Source.** [A053029](https://oeis.org/A053029) "Numbers with 4 zeros in Fibonacci numbers mod m" and
[A053031](https://oeis.org/A053031) "Numbers with 1 zero in Fibonacci numbers mod m" (Henry Bottomley, Feb 23 2000).
Conjectures in the entries: A053029, "m is on this list iff m is an odd number all of whose factors are on this
list or m is twice such an odd number"; A053031, the same with "2 or 4 times such an odd number". (OEIS text,
CC BY-SA 4.0, revisions #33 and #41 of Jun 11 2026, checked 2026-11-06.)

**Reading.** The number of zeros is counted in one Pisano period (OEIS A001176). "Factors" is read as prime
factors (reading it as all divisors other than 1 gives the same statement for m >= 3; the literal "all factors"
including m itself makes the statement circular). Under this reading the A053029 statement fails vacuously at
m = 1 and m = 2 (1 has no prime factors, 2 = 2 * 1, but both have one zero), so it is proved for m >= 3. The A053031
statement holds for every m >= 1.

**Result.** Both conjectures are true (A053029 for m >= 3). Known: B. Benfield and O. Lippard, *Connecting zeros in
Pisano periods to prime factors of K-Fibonacci numbers*, Fibonacci Quart. 63 (2025) 240-258 (arXiv:2407.20048),
Theorems 2.9-2.12, from results of Vinson, Wall, Renault. Reproved here in Lean.

**Argument.** Let alpha(m) be the rank of apparition (least n > 0 with m | F_n) and u = F_{alpha+1} mod m.
1. m | F_n iff alpha | n (F_gcd(a,b) = gcd(F_a, F_b)), and F_{j alpha + r} ≡ u^j F_r. So the Pisano period is
   alpha times the order of u, and the number of zeros per period equals ord_m(u).
2. Cassini gives u^2 ≡ (-1)^alpha. Hence for m >= 3: 4 zeros iff alpha(m) is odd; otherwise u^2 ≡ 1.
3. If u ≡ 1 (one zero) and m >= 3, then alpha = 2h with h odd: from F_{2h} = F_h L_h and
   F_{2h+1} - (-1)^h = F_h L_{h+1} with consecutive Lucas numbers coprime, h even would give m | F_h.
4. Divisors: alpha(d) | alpha(m) and u_m ≡ u_d^{alpha(m)/alpha(d)} (mod d). With alpha(m) ≡ 2 (mod 4) this forces
   u_d ≡ 1 for every divisor d >= 3 (an odd alpha(d) would give u_m ≡ -1 mod d). Since alpha(4) = 6 and
   (alpha(8), u_8) = (6, 13), four zeros exclude 4 | m and one zero excludes 8 | m.
5. Converse by induction over coprime prime-power factors. p^j | F_N implies p^(j+1) | F_{pN}, and
   (F_N, F_{N+1}) ≡ (0, 1) mod p^j implies the same mod p^(j+1) at pN (from F_{kN} ≡ k F_N F_{N+1}^(k-1) and
   F_{kN+1} ≡ F_{N+1}^k mod F_N^2). Odd indices N with m | F_N (A053029) multiply; indices N ≡ 2 (mod 4) with
   (F_N, F_{N+1}) ≡ (0, 1) (A053031) combine as 2AB from 2A and 2B. Step 2 and the order of u then give the count.

Lean: [full proof](A053029/A053029_mathlib.lean).

### [A053031](A053031/): m has one zero in the Fibonacci numbers mod m iff ...

Lean: [full proof](A053029/A053029_mathlib.lean).

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

### [A064016](A064016/): the limit comment is misstated; a(n)/10^(2n) → 1/2 − 3/π² (Mertens)

**Source.** [A064016](https://oeis.org/A064016), "a(n) = Sum_{k <= 10^n} cototient(k), where cototient is
A051953." Comment: "It appears that lim_{n->infinity} (1/n^2) * Sum_{j=1..n} a(j) = 0.1960364... = (1/2 -
3/Pi^2)." (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** As printed the claim is about (1/n^2) Σ_{j≤n} a(j). The constant 1/2 − 3/π² is the density of
Σ_{k≤N} cototient(k) / N^2, so the intended statement is a(n)/10^(2n) → 1/2 − 3/π² (equivalently
Σ_{k≤N} (k − φ(k)) ~ (1/2 − 3/π²) N^2).

**Result.** As printed: false, (1/n^2) Σ_{j≤n} a(j) → +∞ (a(n) grows like 100^n). Intended: true,
a(n)/10^(2n) → 1/2 − 3/π² = 0.19603644907..., by Mertens' theorem Σ_{k≤N} φ(k) = 3N²/π² + O(N log N) (1874).

**Argument.** φ = μ ∗ id, so Σ_{n≤N} φ(n) = Σ_{d≤N} μ(d) T(⌊N/d⌋) with T(M) = M(M+1)/2. Each term divided by
N^2 tends to μ(d)/(2d²) and is bounded by 1/d², so by dominated convergence the ratio tends to
(1/2) Σ μ(d)/d² = (1/2)/ζ(2) = 3/π². Subtracting from Σ_{k≤N} k = N(N+1)/2 gives the cototient sum. For the
printed form, a(n) ≥ (c/2)·100^n eventually (c = 1/2 − 3/π² > 0) and 100^n ≥ n³, so the average is at least
(c/2)·n.

Lean: [full proof](A064016/A064016_mathlib.lean).

### [A071010](A071010/): if n is not a sum of two squares then 4 | sigma(n)

**Source.** [A071010](https://oeis.org/A071010) (sigma(k)/4 for k not a sum of 2 squares), comment:
"Conjecture : if n is not the sum of 2 squares sigma(n) == 0 (mod 4) ..." (OEIS text, CC BY-SA 4.0.)
The same statement is B. Cloitre's 2002 conjecture in [A022544](https://oeis.org/A022544).

**Result.** True. Proved in A022544 by M.-A. Leduc (Mar 2026); re-derived here.

**Argument.** By the two-squares theorem, n is not a sum of two squares iff some prime p ≡ 3 (mod 4)
divides n to an odd power e. Then σ(p^e) = (1 + p) + p^2(1 + p) + … + p^(e−1)(1 + p) ≡ 0 (mod 4), since
4 | p + 1, and σ is multiplicative.

Lean: [full proof](A071010/A071010_mathlib.lean).

### [A078130](A078130/): numbers with exactly one representation as a sum of cubes > 1 — last term 218

**Source.** [A078130](https://oeis.org/A078130) (offset 1), "Numbers having exactly one representation as sum of
cubes > 1", i.e. A078128(n) = 1. Comment: "Conjecture: the sequence is finite; is a(63)=218 the last entry?"
(OEIS text, CC BY-SA 4.0.) Revision #25 (Jun 18 2025) answers "Yes" with a sketch by Sean A. Irvine and adds the
keywords fini, full.

**Result.** True. The numbers n ≥ 1 with exactly one partition into cubes k³, k ≥ 2, are the 63 data terms
8, 16, …, 210, 218; so the set is finite and a(63) = 218 is the last term.

**Argument.** 1. Only 8 and 27: every r ≥ 182 is 8x + 27y (y = 3r mod 8, x = (r − 27y)/8; 181 = 8·27 − 8 − 27 is the Frobenius
   number). If n ≥ 216m + 182, write n − 216m = 8x + 27y; then x + 27j eights and y + 8(m − j) twenty-sevens,
   j = 0..m, are m + 1 different partitions of n into cubes > 1. With m = 1: A078128(n) ≥ 2 for n ≥ 398.
2. For n < 512 the possible parts are 8, 27, 64, 125, 216, 343, and a partition is fixed by its multiplicities, so
   A078128(n) equals the coin-change count with these six coins. Evaluating it for n ≤ 397 gives A078128(n) ≥ 2 for
   219 ≤ n ≤ 397 and A078128(n) = 1 for n ≤ 218 exactly at the 63 data terms.

Lean: [full proof](A078130/A078130_mathlib.lean).

### [A079128](A079128/): gcd(a(n), n) = 1 for permutations with relatively prime cycle lengths

**Source.** OEIS [A079128](https://oeis.org/A079128) (Vladeta Jovovic and Vladimir Baltic, Dec 27 2002): number of
degree-n permutations with (mutually) relatively prime cycle lengths. Conjecture (Jovovic, Jan 25 2003):
gcd(a(n), n) = 1. The entry now records (Ahaan Kallat, Oct 30 2026) that this and the divisibility by n^2 - 1 are
proved in A. Kallat, "A p-adic Valuation Calculus for Permutations with Restricted Cycle Lengths",
arXiv:2610.40342 (2026), Corollary 6.2. (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** "Relatively prime cycle lengths": the gcd of all cycle lengths, fixed points included, is 1
(reproduces the data, certificate/check.py).

**Result.** True; more precisely a(n) = (-1)^(m+1) (mod p) for each prime p dividing n, n = pm.

**Argument.** Fix a prime p | n and write the points as Fin m x Z/p. The group G = (Z/p)^m of block shifts
rho_s(i, x) = (i, x + s_i) is a p-group and acts by conjugation on the set T of permutations with gcd of cycle
lengths 1 (conjugation keeps cycle lengths). Hence |T| = |T^G| (mod p). A permutation commuting with every
shift keeps each block (else (σy).2 + 1 = (σy).2) and commutes with x -> x+1 on it, so it is a shift rho_s.
rho_s has fixed points on block i when s_i = 0 and only p-cycles otherwise, so rho_s is in T iff some s_i = 0.
Thus |T^G| = p^m - (p-1)^m = (-1)^(m+1) (mod p), and p does not divide a(n).

Lean: [full proof](A079128/A079128_mathlib.lean).

### [A079267](A079267/): the number of short pairs in a random perfect matching of [2n] tends to Poisson(1)

**Source.** OEIS [A079267](https://oeis.org/A079267), d(n, s) = number of perfect matchings on {1, ..., 2n}
with s short pairs (pairs {i, i+1}). Comment: "Conjecture: Asymptotically, the n-th row has a Poisson
distribution with mean 1." (D. Callan, Nov 11 2012). (OEIS text, CC BY-SA 4.0, revision #91 of Mar 23 2026;
still marked conjecture on 2026-11-06.)

**Reading.** Divide row n by its sum (2n-1)!! (A001147). The claim is d(n, s)/(2n-1)!! → e^(-1)/s! for every
fixed s as n → ∞, i.e. the number S_n of short pairs in a uniform random perfect matching of [2n] converges in
distribution to Poisson(1).

**Result.** True; known (G. Kreweras and Y. Poupard 1978: all factorial moments of S_n tend to 1).

**Argument.** 1. *Factorial moments.* E[S_n (S_n - 1) ... (S_n - k + 1)] counts ordered k-tuples of distinct short pairs all
   present. A set of k disjoint short pairs {i, i+1} in [2n] is a choice of k non-overlapping dominoes on a path of
   2n vertices: C(2n-k, k) ways. Given the set, the other 2n - 2k points are matched in (2n-2k-1)!! ways. So
   sum_s C(s, k) d(n, s) = C(2n-k, k) (2n-2k-1)!!, and the k-th factorial moment is
   F_k(n) = k! C(2n-k, k) (2n-2k-1)!!/(2n-1)!! = prod_{i<k} (2n-k-i)/(2n-1-2i).
2. *Limit.* Each of the k factors is at most 1 (2n-k-i ≤ 2n-1-2i for i ≤ k-1) and tends to 1, so
   0 ≤ F_k(n) ≤ 1 and F_k(n) → 1 = the k-th factorial moment of Poisson(1).
3. *Poisson law.* By inclusion–exclusion (Bonferroni), P(S_n = s) = (1/s!) sum_{j=0}^{n-s} (-1)^j F_{s+j}(n)/j!
   (this is the entry's explicit formula). With 0 ≤ F ≤ 1 the terms are dominated by 1/(s! j!), so termwise
   limits give P(S_n = s) → (1/s!) sum_j (-1)^j/j! = e^(-1)/s!.

Lean: [witness](A079267/A079267.lean).

### [A081847](A081847/): see A082235

Lean: [full proof](A082235/A082235_mathlib.lean).

### [A082108](A082108/): a(n−1) is the largest integer keeping the partial sum below 1

**Source.** [A082108](https://oeis.org/A082108) (offset 0): a(n) = 4n² + 6n + 1. The 2013 wiki conjecture list gives
"Conjecture. a(n-1) is the largest integer such that Sum[a(k)/(2k)!, k=1,2,...,n] is less than 1". The current entry
no longer carries the conjecture; it has, from Robert Israel (Jul 19 2017), "Sum_{k=1..n} a(k-1)/(2*k)! = 1 - 1/(2*n)!".
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** Literally (summand a(k)) the claim fails at n = 1: a(1)/2! = 11/2 > 1. The intended statement has summand
a(k−1): a(n−1) is the largest integer x with Σ_{k=1}^{n−1} a(k−1)/(2k)! + x/(2n)! < 1.

**Result.** The intended statement is true; it is equivalent to Israel's formula.

**Argument.** a(k−1)/(2k)! = 1/(2k−2)! − 1/(2k)! because (2k)(2k−1) − 1 = 4(k−1)² + 6(k−1) + 1; the sum telescopes
to 1 − 1/(2n)!. With S = 1 − 1/(2n−2)!, S + x/(2n)! < 1 iff x < (2n)(2n−1) = a(n−1) + 1.

Lean: [full proof](A082108/A082108_mathlib.lean).

### [A082235](A082235/): the triangular numbers 1, 21, 28, 45, 78, 91 are never hit

**Source.** [A081847](https://oeis.org/A081847) (Amarnath Murthy, Apr 10 2003): "a(1) = 1, a(n) = smallest positive
number such that the concatenation of a(n-1) and a(n) is a triangular number not obtained earlier."
[A082235](https://oeis.org/A082235): "Triangular numbers obtained as a concatenation of successive terms of A081847."
Comment in both entries: "Conjecture: Every triangular number other than 3, 6 and 10 is a member."
A081847 also carries a comment by Robert Israel (Dec 30 2018): all terms end in 0, 1, 3, 5, 6 or 8, and
"Triangular numbers that cannot be obtained as concatenation of a(n-1) and a(n) include 1, 3, 6, 10, 21, 28,
45, 78, 91." (OEIS text, CC BY-SA 4.0; A081847 revision #12 of Jan 11 2019, A082235 revision #5 of Nov 30 2025,
checked 2026-11-06.)

**Result.** The conjecture is false: 1, 21, 28, 45, 78 and 91 are triangular and are not members of A082235.

**Argument.** For n ≥ 2, a(n) is the last block of digits of a triangular number, so a(n) mod 10 is a last digit
of a triangular number, one of 0, 1, 3, 5, 6, 8 (m(m+1) mod 20 ∈ {0, 2, 6, 10, 12, 16}); a(1) = 1. A member below
100 is concat(x, y) with x, y > 0, hence a two-digit number 10x + y with y one digit, x = a(n). For 21, 28, 45,
78, 91 this needs x ∈ {2, 4, 7, 9}, which is neither 1 nor a valid last digit. 1 has one digit.

Lean: [full proof](A082235/A082235_mathlib.lean).

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

### [A103152](A103152/): a(23) = 725 is not divisible by 3

**Source.** [A103152](https://oeis.org/A103152) (Lei Zhou, 2005): smallest odd number that is 2p + q (p, q odd
primes) in exactly n ways. Comment: "Conjecture: except for the 2nd, 3rd and 4th terms, all other terms are
divisible by 3". Later comments in the same entry: "a(23)=725 is also not divisible by 3" (D. S. McNeil,
Sep 06 2010) and "The only terms a(n) not divisible by 3 for n <= 1450 are a(2),a(3),a(4) and a(23)" (Robert
Israel, Mar 17 2020). (OEIS text checked 2026-11-06.)

**Result.** False, already refuted in the entry: a(23) = 725 = 5^2 * 29.

**Argument.** 725 has exactly 23 representations 2p + q with p, q odd primes, and every odd m < 725 has a
different number of representations; so a(23) = 725, and 3 does not divide 725.

Lean: [witness](A103152/A103152_mathlib.lean).

### [A109926](A109926/): "a(n+15) == 0 (mod 30) for n > 4" is false as printed; the mod 3 and mod 15 claims are out of reach

**Source.** [A109926](https://oeis.org/A109926) (offset 0, keywords hard, more): least k such that k - 2^r is prime
for n values of r. Data a(0..20) = 1, 3, 4, 15, 21, 45, 75, 465, ..., 53999715, 2282745465. Comments: T. D. Noe
(2005) "It appears that 3 and 5 divide a(n) for n>4"; Robert G. Wilson v (Jul 21 2005) "Conjecture: a(n)==0
(mod 3) for n > 2" and "Conjecture: a(n+15)==0 (mod 30) for n > 4". (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Reading.** "For n values of r" means exactly n (the entry's programs count exactly; certificate/check.py
reproduces a(0..12) this way); r >= 0 and k - 2^r must be a prime (so 2^r < k).

**Result.** - The second conjecture is false as printed: a(m) is odd for every m >= 3, so a(n+15) is never divisible by 30;
  for instance a(20) = 2282745465 = 15 (mod 30). All data terms a(5..20) are 15 (mod 30), so the intended
  statement is presumably "a(n)+15 == 0 (mod 30)", i.e. a(n) = 15 (mod 30), for n > 4.
- The odd part of that corrected statement holds for all n >= 3 (whenever a(n) exists). The parts "3 | a(n)" and
  "5 | a(n)" for all large n are not attempted: they assert that the least k with exactly n prime values k - 2^r is
  a multiple of 3 (and 5) for every n, which needs control of primes among k - 2^r for all k below a(n). It also
  presupposes that every count n is attained, which is not known (Erdős 1950 showed the count is unbounded). This
  is famous-strength in the sense of the scan rules: no method proves such statements.

**Argument.** If k is even and r >= 1, then k - 2^r is even, so it is prime only if k - 2^r = 2, i.e. 2^r = k - 2,
which fixes r. With r = 0 this gives at most 2 representations. So k with at least 3 representations is odd.

Lean: [full proof](A109926/A109926_mathlib.lean).

### [A111677](A111677/): "a(n) = 0 iff n ≡ 3 (mod 5)" fails at n = 1

**Source.** [A111677](https://oeis.org/A111677) (offset 1): number of primes of the form "k concatenated with 2n−1"
with k < 2n−1 (row n of [A111676](https://oeis.org/A111676)). Comment: "Conjecture: a(n)=0 iff n== 3 (mod 5).
[Corrected by _R. J. Mathar_, Aug 20 2007]". (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** k runs over 1 ≤ k < 2n−1 and "k concatenated with m" is k·10^d + m, d the number of digits of m. This
reproduces the 29 listed terms (certificate/check.py). Row 1 is empty, as the entry's own a(1) = 0 and the name
("1---> no prime") say.

**Result.** Misstated: a(1) = 0 but 1 ≢ 3 (mod 5). The "if" direction holds for all n: if n ≡ 3 (mod 5) then 2n−1
ends in 5, so every k·10^d + (2n−1) is a multiple of 5 above 5. The remaining direction (a(n) > 0 for n ≥ 2,
n ≢ 3 mod 5) is open; it asks for a prime among k·10^d + m, k < m < 10^d, beyond what Linnik-type bounds give.

Lean: [full proof](A111677/A111677_mathlib.lean).

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

### [A122957](A122957/): "except for 1,2,3,4, this is the nonzero values of A066362" is false

**Source.** [A122957](https://oeis.org/A122957), numbers n such that φ(m) ≥ φ(n) for every m > n. Comment:
"Conjecture: except for 1,2,3,4, this is the nonzero values of A066362." (OEIS text, CC BY-SA 4.0, rev #6 of
Mar 30 2012, read 2026-11-06.) [A066362](https://oeis.org/A066362)(n) is the least k > n with φ(k) < φ(n),
or 0 if there is none. The entry's cross-reference line reads "zeros of A066362".

**Reading.** Literal: the set of nonzero values {A066362(n) : n ≥ 1} \ {0} equals A122957 \ {1, 2, 3, 4}.

**Result.** False. A066362(21) = 22 (φ(21) = 12, φ(22) = 10), but 22 is not in A122957 (φ(24) = 8 < 10).
The nonzero values outside A122957 below 5000 begin 22, 26, 28, 32, 34, 38, 40, 44, ...

What holds:
- A122957 is exactly the zero set of A066362 (by the two definitions; 1, 2, 3, 4 included). This is the
  cross-reference "zeros of A066362".
- One inclusion of the comment holds numerically: every term of A122957 other than 1, 2, 3, 4 below 5000 is a
  nonzero value of A066362 (`certificate/check.py`). Not proved here.

**Argument.** φ(21) = φ(3)φ(7) = 12, φ(22) = 10, φ(24) = 8. The least k > 21 with φ(k) < 12 is 22, and
24 > 22 has φ(24) < φ(22). Zero set: A066362(n) = 0 iff no k > n has φ(k) < φ(n), which is the definition of
A122957.

Lean: [full proof](A122957/A122957_mathlib.lean).

### [A123721](A123721/): first occurrences of k in A123249(n) - 2n

**Source.** [A123721](https://oeis.org/A123721) (Klaus Brockhaus, Oct 2006): a(n) = A123249(n) - 2n, where
[A123249](https://oeis.org/A123249)(1) = 1 and A123249(n) = n + (smallest integer >= n missing from the earlier
terms). "Conjecture: For k > 1, the smallest n such that a(n) = k is A123720(k) = 2^k + 2^(k-1) - k. Confirmed for
k <= 22." (OEIS text, revision #4 of Sep 02 2017, checked 2026-11-06.)

**Reading.** a(1): the data list a(1) = 1 (the PARI program prints A123249(1)); by the name a(1) = -1. Either way
n = 1 does not affect the claim for k > 1.

**Result.** Misstated by one index: the smallest n with a(n) = 2 is 9 = A123720(3), while A123720(2) = 4 and
a(4) = 1. Corrected and proved: for every k >= 1 the smallest n with a(n) = k is A123720(k+1) = 3·2^k - k - 1
(this matches the data and the "confirmed for k <= 22" check).

**Argument.** Let m(n) be the smallest integer >= n missing from a(1..n-1) (A123249 values) and d(n) = m(n) - n,
so A123249(n) = 2n + d(n) for n >= 2 and A123721(n) = d(n).
1. m is nondecreasing and A123249 is strictly increasing.
2. *Run.* If d(n) >= K + 1, then n, ..., n + K are earlier terms, consecutive in value, hence consecutive terms
   A123249(i), ..., A123249(i + K) with i < n, and d(i + t) = d(i) - t.
3. *Staircase.* If d(j) = k then m(j + t) = m(j) for t <= k, so A123249(j + t) = 2j + k + t; these are earlier terms
   at n = 2j + k, so d(2j + k) >= k + 1.
4. *Induction.* Let G(k) = 3·2^k - k - 1 and assume d(G(k)) = k and d(n) < k for n < G(k). By 3, d(2G(k) + k) >= k+1.
   If n < 2G(k) + k were the least n with d(n) >= k + 1, step 2 gives i < n with d(i) = d(i + k) + k >= k, and
   minimality gives d(i) = k, so i >= G(k) and n = 2i + k >= 2G(k) + k, a contradiction. Step 2 at n = 2G(k) + k
   also shows d(n) <= k + 1. So G(k+1) = 2G(k) + k is the first n with d(n) = k + 1.

Lean: [full proof](A123721/A123721_mathlib.lean).

### [A129364](A129364/): a(n) divides A092287(n) (known)

**Source.** [A129364](https://oeis.org/A129364) (offset 1): a(n) = Π_{k=1..n} A066841(k) = Π_{k=1..n} Π_{d|k} d^(k/d);
the entry also gives a(n) = Π_{k=1..n} (⌊n/k⌋!)^k. Comment: "Conjecture: a(n) divides A092287(n) for all n - see
comments in A129365", where A092287(n) = Π_{j,k ≤ n} gcd(j,k). This is Conjecture A of
[A129365](https://oeis.org/A129365) (A129365 = A092287/A129364 is an integer). (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Result.** True, known.

**Argument.** Fix a prime p and write m_r = ⌊n/p^r⌋. Counting pairs (j,k) with p^r | gcd(j,k) gives
v_p(A092287(n)) = Σ_{r≥1} m_r² (Greathouse, in A092287, 2013). By Legendre, v_p(Π_k (⌊n/k⌋!)^k) =
Σ_{r≥1} Σ_k k·⌊m_r/k⌋, and m² − Σ_{k≤m} k⌊m/k⌋ = Σ_{k≤m} (m mod k) ≥ 0 (A004125). So every p-adic valuation of
a(n) is at most that of A092287(n).

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

### [A132293](A132293/): maximal number of right angles in an n-gon (Mathar's correction)

**Source.** [A132293](https://oeis.org/A132293), "Maximal number of right angles in an n-gon", offset 3, data
1, 4, 3, 4, 5, 6, with the editors' note "A proper definition is needed for this sequence". Conjecture (R. J. Mathar,
Mar 07 and Apr 21 2008, in the entry): the correct sequence is a(n) = A014681(n-1), because a zigzag staircase
polyomino has as many right angles as edges. M. Paulovic (Sep 27 2023): possibly an incorrect version of
[A049008](https://oeis.org/A049008). (OEIS text, checked 2026-11-06.)

**Reading.** The entry does not say whether reflex 270° angles count as right angles. A014681(n-1) is n for even n
and n - 2 for odd n (n >= 3). Mathar's staircase counts every corner of a rectilinear polygon, so his reading is:
simple polygon, no straight (180°) vertices, an interior angle is "right" if it is 90° or 270°. A049008 is the other
reading (only 90° counts).

**Result.** The entry is misstated: its data match neither reading (a(6) = 4 is too small under both: an L-shaped
hexagon has six 90°/270° corners, and A049008(6) = 5). Under Mathar's reading his conjecture is true: the maximum is
n for even n >= 4 and n - 2 for odd n >= 3. Under the 90°-only reading the answer is A049008 (from n = 6 on,
A004396), a separate known sequence.

**Argument.** (Mathar's reading).
1. Upper bound for odd n. The interior angles sum to (n-2)·180°. If n - 1 of them are 90° or 270°, their sum is
   (n-1)·90° = 0 (mod 180°) since n - 1 is even, so the last angle is 0 (mod 180°), hence 180° (excluded) or, if all n
   are right, the total is n·90° = 90° (mod 180°), which is not 0 (mod 180°). So at most n - 2.
2. Even n >= 4: the rectangle (n = 4) and staircase polygons (each extra step adds two corners) are rectilinear with
   n corners, all 90° or 270°.
3. Odd n: n = 3, a right triangle; n >= 5, cut one convex corner of a rectilinear (n-1)-gon by a short segment at 45°,
   which replaces one 90° corner by two 135° corners: n vertices, n - 2 right angles.

Lean: —.

### [A132870](A132870/): see A177390

Lean: [witness](A177390/A177390.lean).

### [A136269](A136269/): a(3k) = (3/4)10^(4k) + 5*10^(k-1) - 1

**Source.** [A136269](https://oeis.org/A136269) (offset 0), Cino Hilliard, Mar 19 2008: "Floor of sum of the first
10^n cube roots." Comment: "Conjecture: For n = 3k, a(n) = (3/4)*10^(4n/3)+5*10^(n/3-1)-1." A later comment (Sela
Fried, Oct 02 2024) states that the conjecture is true, with links to a note and to arXiv:2410.07237. (OEIS text,
CC BY-SA 4.0, revision #14 of Oct 14 2024, checked 2026-11-06.)

**Reading.** a(n) = floor(Sum_{i=1..10^n} i^(1/3)) with real cube roots. For k = 0 the formula gives 1/4, not an
integer (a(0) = 1), so the claim is for k >= 1.

**Result.** True for every k >= 1. More generally, for every even M >= 2,
floor(Sum_{i=1..M^3} i^(1/3)) = 3M^4/4 + M/2 - 1; the case M = 10^k is the conjecture.

**Argument.** Let H(c) = (3/4)c^4 + (1/2)c and, for i >= 1, a = (i-1)^(1/3), b = i^(1/3), so b^3 - a^3 = 1.
1. *One step.* Using b^3 - a^3 = 1, E_i = H(b) - H(a) - b = (b-a)^3 (a+b)/4 (polynomial identity after
   multiplying (a+b)/2 by b^3 - a^3). So E_i > 0, and E_1 = 1/4.
2. *Small steps.* For i >= 2, a >= 1. From (b-a)(a^2+ab+b^2) = 1 and a^2+ab+b^2 >= 3ab, (b-a)ab <= 1/3. Hence
   E_i = (b-a)^3(a+b)/4 <= (b-a)(a+b)/(36 a^2 b^2) = (1/a^2 - 1/b^2)/36.
3. *Telescoping.* With c = N^(1/3), Sum_{i<=N} i^(1/3) = H(c) - Sum E_i, and 1/4 <= Sum E_i <= 1/4 + (1 - 1/c^2)/36.
   So H(c) - 1/4 - 1/36 <= S(N) <= H(c) - 1/4.
4. For N = M^3, c = M and H(M) = 3M^4/4 + M/2 is an integer when M is even; S(N) lies in (H - 1, H), so the floor
   is H - 1. For M = 10^k: 3*10^(4k)/4 + 5*10^(k-1) - 1.

Lean: [full proof](A136269/A136269_mathlib.lean).

### [A138684](A138684/): Layman's self-similarity conjecture has the wrong peak values; the corrected form holds

**Source.** [A138684](https://oeis.org/A138684) (offset 1), first differences of
[A138683](https://oeis.org/A138683). A138683: "a(1)=1 and, for n>1, a(n) is the smallest integer
greater than a(n-1) such that a(n) and a(k) do not sum to a term of A001333". Comment in A138684 by
John W. Layman (Nov 26 2011): "Conjecture. Let x(1)=1, x(2)=2, x(n) = 2*x(n-1) + x(n-2), and let
y(1)=1, y(2)=3, y(n) = y(n-1) + y(n-2). Then if n=x(k), a(n)=y(k); if x(k) < n < 2*x(k),
a(n) = a(n-x(k)); and if 2*x(k) <= n < x(k+1), a(n)=1. (This has been confirmed for n < 500.)"
(OEIS text, CC BY-SA 4.0; A138684 revision #11 of Sep 11 2021, checked 2026-11-06.)

**Reading.** The name of A138683 says a(1) = 1, but its data are 2, 3, 6, 7, 8, 12, ... and the data
of A138684 are the differences of exactly this list. The greedy rule started at 2 reproduces both
data sections; started at 1 it gives 1, 3, 5, 7, 8, ... with differences 2, 2, 2, 1, 3, ..., which is
not A138684 (`certificate/readings.py`). We take a(1) = 2 for A138683, as the data do. Whether the
pair a(n) + a(n) is also forbidden does not change the sequence. A001333 = 1, 1, 3, 7, 17, 41, 99, ...;
x(k) are the Pell numbers 1, 2, 5, 12, 29, 70, ...; y(k) are the Lucas numbers 1, 3, 4, 7, 11, 18, ...

**Result.** False as stated: a(12) = 6 (in the entry's data), while x(4) = 12 and y(4) = 7. The peak
values a(x(k)) are 1, 3, 4, 6, 11, 23, 52, 122, ...; they agree with y(k) only for k = 1, 2, 3, 5.
The other two clauses are true, and the conjecture holds for every k >= 1 once y(k) is replaced by

  z(1) = 1,  z(k) = (A001333(k-1) + 5)/2 for k >= 2.

**Argument.** Let S be the set of terms of A138683, q_j = 1, 3, 7, 17, 41, ... (q_j = A001333(j+1)),
r_j = P_1 + ... + P_j (Pell P), so q_j = 2 r_j + 1 and q_{j+1} = 2 q_j + q_{j-1}. By the greedy rule,
x >= 2 is in S iff no smaller y in S has x + y in A001333.
1. *Local rule.* For x in [r_j + 1, r_{j+1}] we have q_j < 2x < q_{j+1} and every q_i with i < j is
   at most r_j + 1 <= x. So the only value of A001333 in (x, 2x) is q_j, and x is in S iff x >= q_j or
   q_j - x is not in S.
2. *Reflection.* For j >= 1 and 1 <= z <= r_{j+1}: z is in S iff not (z < q_j and q_j - z in S). For
   z > r_j this is step 1; for z <= r_j, step 1 applied to w = q_j - z (which lies in [r_j + 1, 2 r_j])
   says w is in S iff z is not.
3. *Level structure* (k = j + 1 >= 2, t = 2 P_k). Since q_k - t = q_{k-1}, step 1 at level k and
   step 2 give: z + t is in S iff z is in S, for 1 <= z <= r_k (copy); nothing in [r_k + 1, t] is in S
   (its reflections lie in [q_{k-1}, r_k], all in S by step 1); everything in [r_k + t + 1, r_{k+1}]
   is in S (it is >= q_k), a run of P_{k-1} integers.
4. *Counting.* By induction, exactly P_k terms are <= r_k, the last one r_k. So the terms with
   indices P_k + 1 .. 2 P_k are the first P_k terms plus 2 P_k, and indices 2 P_k .. P_{k+1} are the
   run. This gives a(n) = a(n - P_k) for P_k < n < 2 P_k, a(n) = 1 for 2 P_k <= n < P_{k+1}, and
   a(P_k) = (2 + 2 P_k) - r_k = (q_{k-2} + 5)/2 = (A001333(k-1) + 5)/2.

Lean: [full proof](A138684/A138684_mathlib.lean).

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

### [A140320](A140320/): a(n) = 2n*3^(n-1) + 1

**Source.** [A140320](https://oeis.org/A140320) (offset 0), Vladimir Shevelev, May 26 2008: "a(n) =
A137576((3^n-1)/2)." Comment: "Conjecture. a(n)=2n*3^(n-1)+1." Here [A137576](https://oeis.org/A137576)(n) =
A002326(n)*A006694(n) + 1, with [A002326](https://oeis.org/A002326)(n) the multiplicative order of 2 mod 2n+1 and
[A006694](https://oeis.org/A006694)(n) the number of cyclotomic cosets of 2 mod 2n+1. (OEIS text, CC BY-SA 4.0,
A140320 revision #13 of Jun 28 2026, checked 2026-11-06.)

**Reading.** A006694 does not count the coset {0}: its data start 0, 1, 1, 2 (mod 3 the cosets are {0}, {1, 2}, and
the value is 1), with "a(0) = 0 by convention". So A006694(n) is the number of distinct sets {x*2^k mod 2n+1 : k >= 0}
with 1 <= x <= 2n. With this reading A137576(0..63) and A140320(0..12) match the entries' data.

**Result.** True for every n >= 0 (a(0) = 1).

**Argument.** Let m = 3^n, n >= 1, so (3^n-1)/2 is the index with 2*index + 1 = m.
1. *2 has order 2*3^(n-1) = phi(3^n) mod 3^n.* Its order divides phi(3^n) by Euler. 2^(3^(n-1)) = 2 mod 3 (odd
   exponent), so it is not 1. For n >= 2, 2^(2*3^(n-2)) - 1 = 4^(3^(n-2)) - 1 has 3-adic valuation
   v_3(4-1) + v_3(3^(n-2)) = n-1 by lifting the exponent, so it is not 1 mod 3^n.
2. *Cosets.* Write a nonzero x mod 3^n as 3^j*u with j < n, 3 not dividing u. Every element of the coset of x has
   valuation exactly j (multiplying by 2 and reducing mod 3^n does not change it, as j < n). By step 1 applied to
   3^(n-j), the powers of 2 run through all units mod 3^(n-j), so the coset of x is the set of all residues of
   valuation j, the coset of 3^j. Hence there are exactly n cosets, one per j = 0, ..., n-1.
3. a(n) = 2*3^(n-1) * n + 1. For n = 0, A002326(0) = 1 (order of 2 mod 1) and A006694(0) = 0, so a(0) = 1.

Lean: [full proof](A140320/A140320_mathlib.lean).

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

### [A158110](A158110/): exp(Σ q^(n^m) x^n/n) is an integer series (known; reproved in Lean)

**Source.** [A158110](https://oeis.org/A158110) (P. D. Hanna, Mar 2009), g.f. exp(Σ 2^(n^3) x^n/n). "Conjecture:
given q and m are nonnegative integers, then exp( Sum_{n>=1} q^(n^m)*x^n/n ) is a power series in x with
integer coefficients." The entry now adds "The conjecture is true (see Fried link)." (S. Fried, Dec 15 2025.)
(OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True (known: S. Fried, "Further proofs of conjectures from the OEIS", arXiv:2607.24832,
Theorem 43). Reproved here in Lean for all q, m ≥ 0.

**Argument.** By Dwork's lemma it suffices that b(n) = q^(n^m) satisfies b(k p^a) ≡ b(k p^(a-1)) (mod p^a).
m = 0: b is constant. m ≥ 1: write (k p^a)^m = K p^E p^(a-1+m), (k p^(a-1))^m = K p^E p^(a-1) with
K = k^m, E = (a-1)(m-1), and x = q^(K p^E). Then x^(p^(a-1+i)) ≡ x^(p^(a-1)) (mod p^a) for all i ≥ 0 (telescoping
x^(p^(j+1)) ≡ x^(p^j) (mod p^(j+1)), Fermat-Euler), valid for every integer x.

Lean: [full proof](A158110/A158110_mathlib.lean).

### [A161579](A161579/): alternation of odious and evil solutions

**Source.** V. Shevelev, 2009, in [A161579](https://oeis.org/A161579) (t(n) = t(n+3)),
[A161580](https://oeis.org/A161580) (t(n) + t(n+3) = 1), [A161817](https://oeis.org/A161817) (k = 5),
[A162311](https://oeis.org/A162311) (k = 7), [A161890](https://oeis.org/A161890) (k = 9), where t = A010060
is the Thue–Morse sequence: "In every sequence of numbers n such that A010060(n)=A010060(n+k), for fixed
odd k, the odious (A000069) and evil (A001969) terms alternate" (A161580: the same for
A010060(n)+A010060(n+k)=1). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** Odious: t(n) = 1; evil: t(n) = 0. "Alternate": consecutive solutions n < n' (no solution
strictly between) have t(n) ≠ t(n').

**Result.** True for every odd k, for both equations. Known: A161890 carries the comment (J. Shallit,
Oct 12 2022) that the conjecture was proved in a later version of Shevelev's arXiv:0907.0880 and can be
proved with Walnut. Reproved here with a short argument and a full Lean proof.

**Argument.** Let P(n) = Σ_{m<n} (-1)^t(m). Since t(2j+1) = 1 - t(2j), P(2j) = 0 and
P(2j+1) = (-1)^t(j). Let Q(n) = Σ (-1)^t(m) over m < n with t(m) = t(m+k). Because
(-1)^t(m) [t(m) = t(m+k)] = ((-1)^t(m) + (-1)^t(m+k))/2, 2Q(n) = P(n) + P(n+k) - P(k). For odd k,
one of n, n+k is even, so 2Q(n) = ±1 - σ with σ = P(k) = ±1, i.e. Q(n) ∈ {0, -σ} for all n. Each
solution changes Q by (-1)^t(m) = ±1 and non-solutions leave it fixed; a sequence staying in a set of
two adjacent integers must step alternately up and down, so consecutive solutions have opposite
(-1)^t. For t(m) + t(m+k) = 1 the same works with 2R(n) = P(n) - P(n+k) + P(k), R(n) ∈ {0, σ}.

Lean: [full proof](A161579/A161579_mathlib.lean).

### [A161580](A161580/): alternation for t(n) + t(n+3) = 1

Lean: [full proof](A161579/A161579_mathlib.lean).

### [A161817](A161817/): alternation for t(n) = t(n+5)

Lean: [full proof](A161579/A161579_mathlib.lean).

### [A161890](A161890/): alternation for t(n) = t(n+9)

Lean: [full proof](A161579/A161579_mathlib.lean).

### [A162311](A162311/): alternation for t(n) = t(n+7)

Lean: [full proof](A161579/A161579_mathlib.lean).

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

### [A171871](A171871/): the last 2^(R-1) entries of column R are binary-code counts (A039754)

**Source.** [A171871](https://oeis.org/A171871) (Robert Munafo, 2010), "Triangle read by rows: Distinct
classifications of N elements containing exactly R binary partitions." Comment: "Conjecture: In general, in
each column, the last 2^(R-1) values are the same as the first 2^(N-1) values from the corresponding row of
A039754. - Robert Munafo, Dec 30 2009". [A005646](https://oeis.org/A005646) defines a classification: a set of
type-specimens each separated from the others by a set of binary partitions, none of which can be omitted
without leaving two types unseparated. [A039754](https://oeis.org/A039754): T(R, N) = number of binary codes of
length R with N words (up to coordinate permutations and complementations). (OEIS text, CC BY-SA 4.0, checked
2026-11-06.)

**Reading.** "2^(N-1)" in the comment means 2^(R-1) (row R of A039754 has 2^R + 1 entries). Encode a
classification by listing its R partitions, choosing a side of each, and writing each element's 0/1 word: the
result is a set C of N distinct words in {0,1}^R whose columns are nonconstant, pairwise neither equal nor
complementary, and such that deleting any column makes two words equal. Isomorphism of classifications is the
action of the hypercube group (coordinate permutations and flips) on C. This reading reproduces A171871 for
R ≤ 4 and all N (`certificate/check.py`). Column R of A171871 is nonzero for R < N ≤ 2^R, so its last 2^(R-1)
entries are N = 2^(R-1)+1, ..., 2^R.

**Result.** True: A(N, R) = T(R, N) for 2^(R-1) < N, and T(R, N) = T(R, 2^R − N), so the last 2^(R-1) values of
column R are T(R, 2^(R-1)+1..2^R) = the first 2^(R-1) values of row R of A039754 read backwards.

**Argument.** Let C have N > 2^(R-1) words. If deleting coordinate i were injective on C, then
N ≤ 2^(R-1). So deleting any coordinate merges two words (minimality); a constant column i, or a column j equal
or complementary to column i, would make deleting i (resp. j) injective, so neither occurs. Hence every N-word
code is a classification, and the two counts are the same orbit count. Complementing C (w ↦ every word not in
C) commutes with the group and maps N-word codes to (2^R − N)-word codes, giving T(R, N) = T(R, 2^R − N).

Lean: [full proof](A171871/A171871_mathlib.lean).

### [A171949](A171949/): P-positions of Mark-4 versus A217319

**Source.** OEIS [A171949](https://oeis.org/A171949), P-positions for the game Mark-4 (offset 1, a(1) = 0).
Formula line: "Conjecture: For n>=2, a(n) = A217319(n-1)." (V. Shevelev, Mar 18 2013; still a conjecture in
revision #26 of May 30 2026, checked 2026-11-06.) (OEIS text, CC BY-SA 4.0.)

**Result.** True; known (Fraenkel 2012). This is the same statement as the conjecture in A217319
("a(n) = A171949(n+1)"), settled and proved in core Lean in [`../A217319/`](A217319/README.md):
`A217319_main` says n is a P-position of Mark-4 iff n = 0 or n = 4^(2k+1)·m with 4 ∤ m. Listing that set in
increasing order gives 0 followed by the terms of A217319 in order, which is a(n) = A217319(n-1) for n ≥ 2.

**Evidence, review level, prior art.** See [`../A217319/README.md`](A217319/README.md) (`lean-proof`).
Outside Lean, beyond what is listed there: the step from the set equality to the index shift of the two
increasing listings (immediate).

Lean: [full proof](A217319/A217319.lean).

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

### [A177390](A177390/): Hanna's "integer triangle for every k" fails at k = 1 (and k = 3)

**Source.** [A177390](https://oeis.org/A177390) (Paul D. Hanna, May 25 2010): "Triangle T where the
g.f. of row n of T^(2n) = (2n^2 + y)^n". Comment: "Conjecture: for all integer k, there exists an
integer triangle J such that the g.f. of row n of J^(k*n) = (k*n^2 + y)^n for n>=0." The k = 1
triangle is [A132870](https://oeis.org/A132870), which carries the same conjecture in the scan list
(OEIS wiki Talk:Conjectures/List). OEIS text CC BY-SA 4.0, checked 2026-11-06.

**Reading.** "Triangle" as in both entries and in the Pascal analogy: lower triangular with 1 on the
diagonal. Then row n of J^(kn) is a polynomial identity whose coefficient of y^j involves J(n,j)
with factor kn (all diagonal entries 1), so for k != 0 the rows are determined one after another
and the rational solution is unique. If the diagonal is not required to be 1, the question changes:
J(0,0) is unconstrained, and J(0,0) = 0 makes column 0 integral automatically (its coefficient
becomes 1); that looser reading is not settled here.

**Result.** False (unitriangular reading). For k = 1 the unique rational solution (A132870) has
T(30,0) = R/2 with R odd; so no integer triangle exists for k = 1. The same happens for k = 3
(row 30, column 0). For k = 2 (A177390 itself) all entries are integers through row 36.
Known: A132870 states since Nov 19 2017 (M. F. Hasler, noticed by Alois P. Heinz) that from row 30
on the entries are not integers, and its name was restricted to 0 <= n <= 29. A177390's conjecture
was not updated.

**Argument.** Uniqueness: write J's row n as unknowns. In J^e (e = kn), entry (n, j) equals
e * J(n,j) plus terms in rows < n and in J(n,l) for l > j (a product path from n to j leaves row n
exactly once; if it leaves straight to column j, the other e - 1 factors are diagonal 1s). So
solving from j = n-1 down to 0 determines row n. Computing rows 0..30 for k = 1 gives integers for
rows 0..29 and T(30,0) = R(0)/2 with R(0) odd.

Lean: [witness](A177390/A177390.lean).

### [A178482](A178482/): Kimberling's change-of-base conjecture for phi-antipalindromic numbers (known)

**Source.** [A178482](https://oeis.org/A178482) (V. Shevelev, 2010), phi-antipalindromic numbers. "Conjecture: this is
the sequence of numbers k for which f(k) is an integer, where f(x) is the change-of-base function defined at
A214969 using b=phi and c=b^2." (C. Kimberling, Oct 17 2012; OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True (known). The entry now says (J. Shallit, Aug 28 2025) that the conjecture "has been proven by
Ingrid Vukusic and myself", with the alternate characterisation: the positive integers whose base-phi
expansion uses only even exponents of phi.

**Argument.** Not reproduced. The proof is in J. Shallit and I. Vukusic, "New properties of the
φ-representation of integers", arXiv:2509.16150 (2025, rev. 2026): automata for base-phi representations,
checked with the Walnut prover. The entry also records a 21-state automaton for the Zeckendorf
representations of the members.

Lean: —.

### [A178790](A178790/): integrality and the Apery-sum congruence mod p^2 are both proved (Sun; Wang-Sun)

**Source.** OEIS [A178790](https://oeis.org/A178790) (mean of (2k+1)A_k, A_k Apery numbers
A005259), comments by Zhi-Wei Sun: "Conjecture: the number a(n) = n^(-1)*Sum_{k=0..n-1}(2*k+1)*A_k
is always an integer" and "Conjecture: If p=5,7 (mod 8) is a prime then sum_{k=0}^{p-1}A_k=0
(mod p^2); if p=1,3 (mod 8) is a prime greater than 3 and p=x^2+2y^2 with x,y integers then
sum_{k=0}^{p-1}A_k=4x^2-2p (mod p^2)." (OEIS text, CC BY-SA 4.0.)

**Result.** Both parts are theorems.
- Integrality: Z.-W. Sun, Arithmetic properties of Apery numbers and central Delannoy numbers,
  arXiv:1006.2776 (noted in the entry, Jun 17 2010), via
  a(n) = sum_{k<n} C(n-1,k) C(n+k,k) C(n+k,2k+1) C(2k,k).
- Congruence: C. Wang, Z.-W. Sun, p-adic analogues of hypergeometric identities and their
  applications, arXiv:1910.06856 (2019), Theorem 1.1 (stated in the abstract): for every odd
  prime p, sum_{k=0}^{p-1} A_k = 4x^2 - 2p (mod p^2) if p = x^2 + 2y^2, and = 0 (mod p^2) if
  p = 5, 7 (mod 8). The proof reduces the sum to a truncated 4F3 and uses known evaluations of
  that series mod p^2 (their Remark 2.1).

**Argument.** Citation only.

Lean: —.

### [A182484](A182484/): the product is a square for p = 63, so "square iff prime" is false

**Source.** OEIS [A182484](https://oeis.org/A182484): a(n) = Product_{k=1..p-1} k^(2k-p-1), p = prime(n)
(Michel Lagneau, May 01 2012). The conjecture list (OEIS wiki, Talk:Conjectures/List) records:
"a(n) = Product_{k=1..p-1} k^(2k-p-1) is a perfect square if, and only if p = prime(n)." The entry itself
marks this conjecture false, with John W. Layman's counterexample p = 63 (May 01 2012). (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.)

**Reading.** For any integer p >= 2 set P(p) = Product_{k=1..p-1} k^(2k-p-1), a positive rational. "Perfect
square" means the square of an integer.

**Result.** False as stated. P(63) = r^2 for an integer r of 348 digits, and 63 = 7 * 9. For p < 400 the
composite p with P(p) a square are 63, 105, 165, 175, 195, 273, 275, 297, 315, 351, 357, 385, 399; every prime
p < 400 gives a square (certificate/check.py). The "if" half is true for all primes (argument below; not in Lean).

**Argument.** Counterexample: compute num(63) = Product_{k>=32} k^(2k-64) and den(63) = Product_{k<32}
k^(64-2k); then num(63) = r^2 den(63) with the r in the Lean file.

"If" half (outside Lean). For odd p every exponent 2k-p-1 is even, so P(p) = R(p)^2 with
R(p) = Product k^(k-(p+1)/2), and P(p) is an integer square iff R(p) is an integer. For a prime q, Legendre
counting gives v_q(R(p)) = (1/2) Sum_{j>=1} M_j (q^j (M_j + 1) - p - 1) with M_j = floor((p-1)/q^j), since the
multiples q^j m, m <= M_j, contribute Sum (2 q^j m - p - 1) = M_j (q^j (M_j+1) - p - 1). Each factor
q^j (M_j + 1) exceeds p - 1. For p prime it is not p (p would have the proper factor q^j), so it is >= p + 1 and
every term is >= 0. For composite p the terms with q^j | p are -M_j / 2 < 0, and P(p) is a square exactly when the
other terms outweigh them; at p = 63, q = 3 gives -10 - 3 + 17 = 4
and q = 7 gives -4 + 17 = 13. (Even p >= 4 never gave a square below 400; even p is composite anyway.)

Lean: [witness](A182484/A182484.lean).

### [A187941](A187941/): a(n) = 2^n exactly for n prime or n = 1 (n ≥ 1); fails literally at n = 0

**Source.** [A187941](https://oeis.org/A187941) (least number with exactly n even divisors,
offset 0), comment: "Conjecture: a(n) = 2^n only if n is prime or if n = 1." (OEIS text,
CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** a(n) = least m ≥ 1 with exactly n even divisors. The entry has offset 0 and
a(0) = 1 = 2^0, with 0 neither prime nor 1, so the literal statement fails at n = 0; the
intended statement is for n ≥ 1.

**Result.** For n ≥ 1: a(n) = 2^n if and only if n is prime or n = 1. At n = 0 the literal
claim fails (a(0) = 2^0).

**Argument.** Odd m has no even divisors, and the even divisors of 2y are 2·(divisors of y), so
m with n ≥ 1 even divisors is 2y with d(y) = n.
- *n composite*, n = uv with u, v ≥ 2: 2^u 3^(v−1) = 2·(2^(u−1) 3^(v−1)) has u·v = n even
  divisors and 2^u 3^(v−1) < 2^u 4^(v−1) ≤ 2^u 2^(u(v−1)) = 2^n, so a(n) < 2^n.
- *n prime*: d(y) = n prime forces y = q^(n−1) with q prime (d is multiplicative), so
  m = 2y ≥ 2^n, and 2^n has n even divisors. *n = 1*: m ≥ 2 = 2^1.

Lean: [full proof](A187941/A187941_mathlib.lean).

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

### [A193437](A193437/): p^floor(n/p) divides a(n) for primes p = 1 (mod 3)

Lean: —.

### [A193438](A193438/): p^floor(n/p) divides a(n) for primes p = 1 (mod 3), resp. p = 1 (mod 4)

**Source.** [A193437](https://oeis.org/A193437): e.g.f. exp(Sum_{n>=0} x^(3n+1)/(3n+1)), the number of permutations of
n elements with every cycle length = 1 (mod 3). [A193438](https://oeis.org/A193438): the same with 4 in place of 3.
Conjectures (Paul D. Hanna, in the entries): a(n) is divisible by p^floor(n/p) for every prime p = 1 (mod 3),
respectively p = 1 (mod 4). (OEIS text, checked 2026-11-06; both entries now link Kallat's paper.)

**Result.** True, and stronger: v_p(a(n)) >= v_p(n!) >= floor(n/p). Known: A. Kallat, "A p-adic valuation calculus
for permutations with restricted cycle lengths", arXiv:2610.40342 (Oct 29 2026), Theorem 8.15 and Remark 8.16, with a
Lean 4 + Mathlib proof in its ancillary files (`anc/lean/lean-restricted/CongruenceRestricted/Saturation.lean`:
`saturated_valuation`, `sat_residue`).

**Argument.** (re-derived independently). Let L be the allowed cycle lengths, r = 3 or 4, p = 1 (mod r). Then
pl = l (mod r), so l is in L iff pl is in L. Write each l in L as u p^k with p not dividing u; u is in L. Then
Sum_{l in L} x^l / l = Sum_{u in L, p ∤ u} (1/u) Sum_k (x^u)^(p^k) / p^k, so the e.g.f. is
A(x) = Prod_{u} E_p(x^u)^(1/u), with E_p(y) = exp(Sum_k y^(p^k)/p^k) the Artin–Hasse exponential. E_p has
p-integral coefficients (Dwork's lemma) and 1/u is a p-adic integer, so each factor and the x-adically convergent
product lie in Z_(p)[[x]]. Hence a(n)/n! is p-integral. This is the Dieudonné–Dwork criterion for sets closed under
multiplication and division by p, as in Kallat's Theorem 8.15.

Lean: —.

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

### [A209998](A209998/): penultimate term of row n equals A199923(n)

**Source.** [A209998](https://oeis.org/A209998) (Clark Kimberling, 2012): triangle of coefficients of v(n,x), with
u(1,x) = v(1,x) = 1, u(n,x) = x u(n-1,x) + 2x v(n-1,x) + 1, v(n,x) = (x+1) u(n-1,x) + 2x v(n-1,x) + 1.
"Conjecture: penultimate term in row n is A199923(n)." [A199923](https://oeis.org/A199923)(n) =
Sum_{k=0..3^(n-1)} gcd(k, 3^(n-1)), a(0) = 1. (OEIS text, CC BY-SA 4.0, revision #8, checked 2026-11-06.)

**Reading.** The %F lines print the v-recursion with x*v(n-1,x); the entry's Mathematica program and the data use
2x*v(n-1,x) (row 2 is "2 3", which only the 2x version gives). We use the program's recursion. Row n has
n entries (v(n,x) has degree n-1) and ends with 3^(n-1), as the entry says.

**Result.** Misstated by one index. The penultimate term of row n is A199923(n-1) = 2(n+1)3^(n-3) for every
n >= 2 (proved). As printed (A199923(n)) it fails already at row 2: penultimate term 2, A199923(2) = 8.

**Argument.** Write U_n, V_n for the x^(n-1) coefficients and U'_n, V'_n for the x^(n-2) coefficients of u(n,x),
v(n,x). Comparing coefficients: U_n = V_n = U_(n-1) + 2V_(n-1), so U_n = V_n = 3^(n-1); and
U'_n = U'_(n-1) + 2V'_(n-1), V'_n = U'_(n-1) + U_(n-1) + 2V'_(n-1), with U'_2 = 1, V'_2 = 2. Induction gives
U'_n = (2n-1)3^(n-3) and V'_n = 2(n+1)3^(n-3). For A199923: G_m = Sum_{k<3^m} gcd(k, 3^m) satisfies
G_(m+1) = 2*3^m + 3 G_m (group k by k mod 3), so G_m = (2m+3)3^(m-1), and A199923(m+1) = G_m + 3^m
= 2(m+3)3^(m-1) (S. Irvine's formula a(n) = 2(n+2)3^(n-2)). With m = n-2 this is V'_n.

Lean: [full proof](A209998/A209998_mathlib.lean).

### [A212346](A212346/): a(n) = (n+3)(n^2-4)/6 for n >= 3

**Source.** [A212346](https://oeis.org/A212346) (N. J. A. Sloane, 2012): coefficient of x^0 in the marked mesh
pattern generating function Q_{n,132}^{(0,4,0,0)}(x). Comment: "Conjecture stated in Formula holds through a(35)";
formula: "Conjecture: this appears to equal (n+3)(n^2-4)/6 for n >= 3". (OEIS text, CC BY-SA 4.0, revision #34 of
Nov 05 2025, checked 2026-11-06.)

**Reading.** Q_{n,132}^{(0,4,0,0)}(x) = sum over 132-avoiding permutations s of 1..n of x^m, m = number of entries
of s with at least 4 larger entries to their left (quadrant II). So a(n) counts 132-avoiding permutations in which
every entry has at most 3 larger entries to its left.

**Result.** True: a(n) = (n+3)(n^2-4)/6 for every n >= 3. Barker's recurrence and g.f. in the entry follow.

**Argument.** Let N_k(n) count 132-avoiding permutations of length n in which every entry has fewer than k larger
entries to its left (a = N_4).
1. *Decomposition.* In a 132-avoider with n at position i+1, every entry left of n exceeds every entry right of n.
   The left block (size i) and right block (size n-1-i) are arbitrary 132-avoiders; a left entry's larger-left
   entries are those inside the left block; a right entry has the i left entries, n, and its larger-left entries
   inside the right block. Hence N_k(0) = 1, N_0(n) = 0 for n >= 1, and
   N_k(n) = sum_{i=0}^{n-1} N_k(i) N_{k-1-i}(n-1-i). (This is the x = 0 case of the generating function theorem for
   Q^{(0,k,0,0)}_{132} of Kitaev, Remmel and Tiefenbruck, which the entry's Mathematica program transcribes.)
2. *Closed forms.* Terms with i >= k and a nonempty right block vanish, so for n >= k-1:
   N_k(n+1) = N_k(n) + sum_{i<k-1} N_k(i) N_{k-1-i}(n-i). This gives N_1(n) = 1; N_2(n) = n (n >= 1);
   N_3(n+1) = N_3(n) + n + 1 for n >= 2, so 2N_3(n) = n^2 + n - 2 (n >= 2); and for n >= 3
   N_4(n+1) = N_4(n) + N_3(n) + (n-1) + 2 with N_4(3) = 5. Induction gives 6N_4(n) = (n+3)(n^2-4) for n >= 3, since
   (n+4)((n+1)^2-4) - (n+3)(n^2-4) = 3(n^2+n-2) + 6(n-1) + 12.

Lean: [full proof](A212346/A212346_mathlib.lean).

### [A212652](A212652/): a(n) = min of d + (h-1)/2 over n = d*h with h odd, and n lies in row a(n) of A209260

**Source.** [A212652](https://oeis.org/A212652) (offset 1), Max Alekseyev (2008): a(n) is the least positive
integer M such that n = T(M) - T(k) for an integer k with 0 <= k <= M, T = A000217. The scan record (from the
OEIS wiki conjecture list) quotes L. Edson Jeffery's conjectures: a(n) = min B_n, where B_n is the set of
integers d + (h-1)/2 with n = d*h (h odd), and n appears in row a(n) of [A209260](https://oeis.org/A209260).
A209260 Conjecture 2 (Jeffery, Feb 13 2013) adds that n appears in row b of [A141419](https://oeis.org/A141419)
for every b in B_n. The entry now lists a(n) = Min_{odd d|n} (n/d + (d-1)/2) as a formula and keeps "Conjecture:
n appears in row a(n) of A209260". A later comment (O. E. Pol, Jan 07 2025) conjectures that a(n) is the smallest
largest part over the partitions of n into consecutive parts. (OEIS text, CC BY-SA 4.0, A212652 revision #84 of
Jan 11 2025, checked 2026-11-06.)

**Reading.** A141419 row r is T(r) - T(r-k), 1 <= k <= r. A209260 row r is row r of A141419 with the entries
already present in an earlier row of A141419 removed (the construction stated in A209260; certificate/check.py
reproduces the A209260 b-file, 100 rows, this way). "d + (h-1)/2 is integral" means h odd.

**Result.** All true, for every n >= 1:
- a(n) = min over odd h | n of n/h + (h-1)/2;
- n lies in row M of A141419 iff M = n/h + (h-1)/2 for some odd h | n;
- n lies in row a(n) of A209260 and in no other row;
- a(n) is the least largest part of a partition of n into consecutive positive parts.

**Argument.** n = T(M) - T(k) with k < M means 2n = L * S with L = M - k >= 1 and S = M + k + 1 = 2k + L + 1;
L + S = 2M + 1 is odd, so exactly one of L, S is odd, and M = (L + S - 1)/2.
- L odd: h = L, n/h = S/2, M = n/h + (h-1)/2.
- L even: h = S, n/h = L/2, M = n/h + (h-1)/2.
Conversely, for n = d*h with h = 2j+1 put M = d + j, and k = d - j - 1 if h <= 2d (L = h), k = j - d if h > 2d
(L = 2d); both give T(M) - T(k) = n. So the set of M that represent n is exactly B_n, which gives the formula and
the A141419 statement. Since n is in row M of A141419 iff M represents n, the first row of A141419 containing n is
row a(n), so n survives in row a(n) of A209260 and is removed from every later row. Finally (k+1) + ... + M =
T(M) - T(k), so Pol's reading is the definition.

Lean: [full proof](A212652/A212652_mathlib.lean).

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

### [A213507](A213507/): a(n) is never divisible by 2, 5, 13, 29, 31, 37, 41, 43, 53, 71, 97

**Source.** [A213507](https://oeis.org/A213507) (Hanna, 2012): e.g.f. exp(sum_{n>=1} Catalan(n) x^n/n); a = 1, 1, 3,
17, 149, 1809, ... Comment: "Conjecture: a(n) is not divisible by {2,5,13,29,31,37,41,43,53,71,97}." Formulas added
by Peter Bala (Aug 16 2026): e.g.f. C(x)^2 exp(-x C(x)^2), C the Catalan g.f., and a(n+k) - (-1)^k a(n) = 0 (mod k).
(OEIS text checked 2026-11-06.)

**Result.** True. For every listed prime p, a(n) mod p is periodic with period dividing 2p and a(n+p) = -a(n) (mod p);
a(0), ..., a(p-1) are nonzero mod p, so no a(n) is divisible by p.

**Argument.** 1. E.g.f. With C = 1 + xC^2 and D = x d/dx: D log(C^2 exp(-xC^2)) = 2xC'/C - xC^2 - 2x^2 C C'. From
   C' = C^2/(1 - 2xC), xC^2 = C - 1 and 1 - 2xC = (2 - C)/C this equals xC^2 = C - 1 = sum_{n>=1} Catalan(n) x^n,
   so exp(sum Catalan(n) x^n/n) = C^2 exp(-xC^2).
2. Congruence. Bala's theorem (2017 note, Theorem 1 and Lemma 1): if the e.g.f. of b is F(y) exp(y H(y)) with
   F, H in Z[[y]] and H(0) = 1, then b(n+k) = b(n) (mod k) for all n, k. Put y = -x, b(n) = (-1)^n a(n):
   F(y) = C(-y)^2 and H(y) = C(-y)^2 are integral with H(0) = 1, so a(n+k) = (-1)^k a(n) (mod k).
3. Finite check. With k = p: a(n+p) = -a(n) (mod p), so it suffices that p does not divide a(0), ..., a(p-1); this holds
   for all eleven primes (certificate). (For p = 2: a(n+2) = a(n) mod 2 and a(0) = a(1) = 1.)

Lean: needs Mathlib.

### [A213648](A213648/): fixed points lie in A000057

**Source.** [A213648](https://oeis.org/A213648) (offset 2): "The minimum number of 1's in the relation
n*[n,1,1,...,1,n] = [x,...,x] between simple continued fractions." Comment: "Conjecture: the fixed points of this
sequence are in A000057." [A000057](https://oeis.org/A000057): primes dividing at least one term of every
Fibonacci-type sequence, equivalently primes p whose Fibonacci entry point z(p) (A001177) is p + 1. (OEIS text,
A213648 revision #68 of Aug 18 2026, checked 2026-11-06.)

**Result.** True, and settled in the entry itself: M. Jeremie Lafitte (Levitas), Aug 10 2026, added a formula
section proving a(n) = A001177(n) - 1 = min{m ≥ 1 : n | F(m+1)} (the symmetric continuant matrix
M(n) M(1)^m M(n) = [[P, Q], [Q, F(m+1)]] and the Euclidean algorithm), so the fixed points are the n with
z(n) = n + 1. A001177 states "a(n) = n + 1 if and only if n is in A000057" (Benoit Cloitre, 2007) without proof;
we supply the step that z(n) = n + 1 forces n prime.

**Argument (z(n) = n + 1 implies n prime).** Write z(m) for the entry point; m | F(k) iff z(m) | k.
1. For p^e ∥ n, z(p^e) | z(n) = n + 1, which is coprime to p, so p ∤ z(p^e). Since 5 | z(5^e) = 5^e, 5 ∤ n.
2. Let a = z(p). F(at) ≡ t F(a) F(a+1)^(t-1) (mod F(a)^2) and p ∤ F(a+1), so v_p(F(at)) = v_p(F(a)) when p ∤ t.
   With t = z(p^e)/a this gives p^e | F(a), so z(p^e) = z(p), which divides p - (5/p) (for p = 2: z(2) = 3, and
   z(4) = 6 is even, so 4 ∤ n).
3. Hence n + 1 divides L = lcm over p | n of (p - (5/p)). If n = p^e then p^e + 1 ≤ p + 1, so e = 1. If n has
   r ≥ 2 odd prime factors and is odd, L ≤ 2 Π (p+1)/2 ≤ 2 (2/3)^r Π p < n + 1. If n = 2m (m odd, m > 1), n + 1 is
   odd and divides the odd part of L, which is at most 3 Π_{p | m} (p+1)/2 < 2m + 1. Contradiction in both cases.

Lean: [checked](A213648/A213648_mathlib.lean).

### [A214724](A214724/): p | a(n) for n >= p when p = m^2 + 1 is prime

**Source.** [A214724](https://oeis.org/A214724) (Paul D. Hanna, Jul 26 2012): e.g.f. exp(Sum_{n>=0}
x^(n^2+1)/(n^2+1)). Comment: "Conjecture: p | a(n) for n>=p when p is a prime of the form m^2+1 (A002496)."
The entry (revision #17, Oct 17 2026, checked 2026-11-06) now adds "[Proved in Kallat (2026).]".

**Result.** True; proved by A. Kallat, *Universal Shift Congruences for Weighted Permutation Sequences*,
arXiv:2610.15849 (2026), Theorem `thm:hanna`, with a Lean 4 proof (`hanna_conjecture`) in
[ahaankallat/congruence-phenomena-higher-order-lean](https://github.com/ahaankallat/congruence-phenomena-higher-order-lean),
file `CongruenceTheoryHigherOrder/OEISHannaRichman.lean`. That Lean theorem is stated for the weighted-permutation
sequence `Aw hannaW` (weights 1 on lengths n^2+1, 0 elsewhere); the identification with the e.g.f. is the
exponential formula.

**Argument (second reading, independent of the paper).** By the exponential formula a(n) is the number of
permutations of {1..n} all of whose cycle lengths lie in S = {k^2 + 1 : k >= 0}; note 1 ∈ S and p ∈ S. Let
n >= p and let σ be the p-cycle (1 2 ... p). The group <σ> of order p acts by conjugation on these permutations
(conjugation keeps the cycle type), so a(n) is congruent mod p to the number of fixed permutations, those that
commute with σ. The centraliser of σ in S_n is <σ> × Sym({p+1..n}), and σ^k has cycle type (p) for k != 0 and
1^p for k = 0, both allowed. So the fixed permutations number p · a(n - p), and p | a(n). (The paper argues
differently: A(n+p) ≡ A(n)A(p) mod p and A(p) ≡ w_1^p + w_p - 1 ≡ 0 mod p.)

Lean: —.

### [A214758](A214758/): Coman's midpoint claim for Carmichael numbers is false (46657)

**Source.** [A214758](https://oeis.org/A214758) (Carmichael numbers divisible by a smaller Carmichael number). Comment
by Marius Coman (Aug 2012): "Conjecture: A Carmichael number C1 can be written as C1 = (C2 + C3)/2, where C2 and C3
are also Carmichael numbers, only if both C1 and C3 are divisible by C2." Same entry, Charles R Greathouse IV
(Dec 08 2014): "Counterexample: 46657 = (29341 + 63973)/2." (OEIS text, CC BY-SA 4.0.)

**Result.** False. 46657 = 13·37·97, 29341 = 13·37·61, 63973 = 7·13·19·37 are Carmichael numbers,
2·46657 = 29341 + 63973, and neither 29341 nor 63973 divides 46657 (so swapping C2 and C3 does not help). Below 10⁶
there are 6 midpoint triples of Carmichael numbers and 5 of them are counterexamples; 46657 is the least C1.

Lean: [witness](A214758/A214758_mathlib.lean).

### [A215010](A215010/): equiangular polygons with sides in arithmetic progression are not only hexagons

**Source.** [A215010](https://oeis.org/A215010) (Garcia, 2012): integer side lengths t + m d of the simple convex
equiangular hexagons with sides in arithmetic progression. Comment: "Conjecture: hexagons are the only simple
convex polygons with equal interior angles with such property, due to the fact that cos(Pi/3) = 1/2." (OEIS text
checked 2026-11-06.)

**Reading.** "Such property": the n side lengths, in some order, are t, t+d, ..., t+(n-1)d with d >= 1.

**Result.** False. The equiangular 10-gon with consecutive sides t + m_k d, m = (0, 6, 2, 8, 4, 5, 1, 7, 3, 9),
closes for every t, d >= 1; for t = d = 1 its sides are 1, 7, 3, 9, 5, 6, 2, 8, 4, 10. More generally an
equiangular n-gon with sides 1, ..., n exists for many composite n (Kvant problem M644: n = 1980).

**Argument.** With w = exp(2 pi i/10), the polygon closes iff sum_k (t + m_k d) w^k = 0. The sum of all w^k is 0,
so it suffices that sum_k m_k w^k = 0. Since w^5 = -1, this is sum_(k<5) (m_k - m_(k+5)) w^k
= -5(1 - w + w^2 - w^3 + w^4) = -5 (1 + w^5)/(1 + w) = 0. (The choice m_k = 5[k odd] + (k mod 5) is a sum of a
function of k mod 2 and a function of k mod 5, and each part sums to 0 over cosets.) A closed polygon with
positive sides whose direction turns left by 2 pi/10 at every vertex (one full turn) is convex and simple, with
all interior angles 4 pi/5.

Lean: [full proof](A215010/A215010_mathlib.lean).

### [A215672](A215672/): Coman's q((r+1)q − r) claim for Poulet numbers is false (617093)

**Source.** [A215672](https://oeis.org/A215672) (Fermat pseudoprimes to base 2 with three prime factors). Comment by
Marius Coman (Aug 2012): "Conjecture: Any Poulet number P with three or more prime divisors has at least one prime
divisor q for that can be written as P = q*((r + 1)*q - r), where r is a natural number." Same entry, Charles R
Greathouse IV (Dec 07 2014): the conjecture fails for a(80) = 617093 = 43 · 113 · 127. (OEIS text, CC BY-SA 4.0.)

**Result.** False; 617093 is the least counterexample. Below 10⁷ the counterexamples are 617093, 1534541, 2537641,
7455709; below 10¹³ there are 3352 (Feitsma–Galway list).

**Argument.** P = q((r+1)q − r) means P/q = q + r(q − 1). For q = 43, 113, 127: P/q = 14351, 5461, 4859, and
14351 − 43 = 14308, 5461 − 113 = 5348, 4859 − 127 = 4732 are not divisible by 42, 112, 126 respectively.

Lean: [witness](A215672/A215672_mathlib.lean).

### [A216371](A216371/): for odd primes with one coach, the top row is a permutation of 1, 3, ..., 2q-1

**Source.** OEIS [A216371](https://oeis.org/A216371) (Gary W. Adamson, Sep 05 2012): odd primes p with
A135303((p-1)/2) = 1, where A135303(n) = phi(2n+1)/(2 A003558(n)) is the number of coaches of 2n+1 and A003558(n)
is the least m > 0 with 2^m = +-1 (mod 2n+1). Conjecture (Adamson, Sep 08 2012): if p is a term and p = 4q-1 or
4q+1, the top row of its coach is a permutation of the first q odd integers (11: [1, 5, 3]; 13: [1, 3, 5];
37: [1, 9, 7, 15, 11, 13, 3, 17, 5]). (OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Reading.** Hilton-Pedersen coach of an odd b: starting from a_1 = 1, write b - a_i = 2^(k_i) a_(i+1) with
a_(i+1) odd, until a_(i+1) = 1; the top row is a_1, ..., a_r (the bottom row holds the k_i). This reproduces the
three examples. In both cases q = floor((p+1)/4).

**Result.** True for every term p.

**Argument.** Let p = 2r+1 and S = {1, ..., r}. The folded doubling h(x) = 2x (if 4x < p) or p - 2x maps S to S
and is multiplication by 2 on the classes {+-x} mod p, so h^j(1) = +-2^j. If no 0 < m < r has 2^m = +-1 (mod p)
(Greathouse's characterization of the terms), the values h^j(1), j < r, are distinct, so h is one r-cycle on S.
A coach step a -> c = odd part of p - a is undone by doubling: h^i(c) = 2^i c is even for 0 < i <= k-1 and
h^k(c) = p - 2^k c = a. Hence c is the previous odd value before a along the h-cycle, so the coach map is a
bijection of the odd elements of S and its orbit from 1 runs backward through all of them: the top row is a
permutation of the q odd numbers 1, 3, ..., 2q-1 in S. Terms satisfy Greathouse's condition: by Fermat
(2^r)^2 = 1, so 2^r = +-1 and A003558(r) divides r; A135303 = 2r/(2 A003558(r)) = 1 then forces A003558(r) = r.

Lean: [full proof](A216371/A216371_mathlib.lean).

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

### [A218483](A218483/): Coman's 8pn + p² conjectures are true (form ⇔ P ≡ 1 mod 8)

**Source.** [A218483](https://oeis.org/A218483) (Fermat pseudoprimes to base 2 congruent to 1 mod 8; old name "of the
form 8*p*n + p^2, where p is prime and n natural"). Comments by Marius Coman (Oct 2012): (1) if a base-2 Fermat
pseudoprime can be written as 8pn + p² (n an integer, p one of its prime factors), it can be written so for any of its
prime factors; (2) if P = p1·p2 is 8·p1·n + p1², then P = 8·p2·(−n) + p2²; (3) if it cannot be written so for one
prime factor, it cannot for any. Also: no base-2 pseudoprime is 40n + 15. Charles R Greathouse IV (Dec 07 2014): "All
three conjectures are true (obvious from new characterization)." (OEIS text, CC BY-SA 4.0.)

**Result.** True. For odd P and a prime p ∣ P: P = 8pn + p² for an integer n ⇔ P ≡ 1 (mod 8). Base-2 pseudoprimes
are odd, so (1) and (3) follow; (2) holds for any p1 ≠ 0, p2. No base-2 pseudoprime is 15 mod 40.

**Argument.** Write P = p·m. P = 8pn + p² ⇔ m = 8n + p ⇔ m ≡ p (mod 8). For odd p, p² ≡ 1 (mod 8), so
m ≡ p ⇔ pm ≡ 1 (mod 8). For (2): p2 = 8n + p1, so p2² − 8p2n = p2(p2 − 8n) = p2·p1. For 15 mod 40: 5 ∣ P ∣ 2^(P−1) − 1,
but P − 1 ≡ 2 (mod 4) and 2^(4k+2) ≡ 4 (mod 5).

Lean: [full proof](A218483/A218483_mathlib.lean).

### [A218755](A218755/): differences are multiples of 36

Lean: [full proof](A219543/A219543_mathlib.lean).

### [A219085](A219085/): jump points of x^(1/d) form a linear recurrence sequence

**Source.** OEIS [A219085](https://oeis.org/A219085), a(n) = floor((n + 1/2)^3), the jump points of x^(1/3).
Comment (C. Kimberling, 2012): "Conjecture: if d is a positive integer and f(x) = x^(1/d), then the solutions of
J(k) form a linearly recurrent sequence", where J(k) is {f(k)} < 1/2 < {f(k+1)}. A later comment in the entry:
"This conjecture was proved by David Moews; see Problem 21 in 'Unsolved Problems and Rewards'." (OEIS text,
CC BY-SA 4.0, checked 2026-11-06.)

**Result.** True; known (D. Moews, Jan 2013, Kimberling's Problem 21). Reproved here: the solutions are
⌊(n+1/2)^d⌋ = ⌊(2n+1)^d / 2^d⌋, and since (2n+1)^d mod 2^d depends only on n mod 2^(d-1), this is a polynomial
plus a periodic sequence, which satisfies a linear recurrence ((E−1)^(d+1) applied after (E^p − 1)).

Lean: [full proof](A219085/A219085_mathlib.lean).

### [A219196](A219196/): a(15) = a(16) = 131070 and a(17..32) = 8589934590

**Source.** OEIS [A219196](https://oeis.org/A219196), a(n) = A027642(A131577(n)), the denominator of the
Bernoulli number B_{2^(n−1)} (B₀ for n = 0). Comment: "Conjecture: a(15) = a(16) = 131070, a(17) through
a(32) = 8589934590." (OEIS text, CC BY-SA 4.0.)

**Result.** True, and answered in the entry: Robert Israel (Sep 21 2015) notes that by von Staudt–Clausen
a(n) is 2 times the product of the Fermat primes ≤ 2^(n−1) + 1, so a(n) = 8589934590 for 17 ≤ n ≤ 2^33.

**Argument.** For k ≥ 1, den B_{2k} = ∏ p over primes p with p − 1 | 2k (von Staudt–Clausen). For
2k = 2^m, p − 1 | 2^m means p = 2^j + 1 with j ≤ m. For j ≤ 31 the primes 2^j + 1 are 2, 3, 5, 17, 257,
65537 (j = 0, 1, 2, 4, 8, 16). So a(15), a(16) (m = 14, 15) = 2·3·5·17·257 = 131070 and a(17..32)
(m = 16..31) = 131070·65537 = 8589934590.

Lean: [full proof](A219196/A219196_mathlib.lean).

### [A219543](A219543/): Bernoulli denominators ≡ 3 or 6 (mod 9) differ by multiples of 36

**Source.** OEIS [A219543](https://oeis.org/A219543) (denominators of Bernoulli numbers ≡ 3 mod 9) and
[A218755](https://oeis.org/A218755) (≡ 6 mod 9), both subsets of A090801 (distinct Bernoulli denominators).
Each entry: "Conjecture: all the first differences ... of the sequence are multiples of 36." (OEIS text,
CC BY-SA 4.0.)

**Result.** True, and answered in both entries: Charles R. Greathouse IV (Nov 22 2012), "The conjecture is
true, since elements of A090801 are 2 mod 4."

**Argument.** The denominators of B₀, B₁ and of B_j for odd j ≥ 3 are 1, 2, 1, which are not ≡ 3 or 6 (mod 9).
For k ≥ 1, von Staudt–Clausen gives that 2 divides the denominator of B_{2k} and 4 does not, so it is
≡ 2 (mod 4). With ≡ 3 (mod 9) this gives ≡ 30 (mod 36) (A219543); with ≡ 6 (mod 9) it gives ≡ 6 (mod 36)
(A218755). Any two terms of either sequence therefore differ by a multiple of 36.

Lean: [full proof](A219543/A219543_mathlib.lean).

### [A220956](A220956/): "a(n) = 0 iff n is an odd prime" is false; n = 16843² = 283686649 is a composite zero

**Source.** [A220956](https://oeis.org/A220956), a(n) = (C(2n,n) − C(2n−2,n−1)) mod n² − n − 2. Comment:
"Conjecture: a(n) = 0 iff n is an odd prime." (OEIS text, CC BY-SA 4.0, read 2026-11-06; b-file to n = 10100.)

**Result.** False. For odd n ≥ 3, a(n) = 0 exactly when C(2n−1,n−1) ≡ 1 (mod n²). Composite n with this
congruence are known ([A267824](https://oeis.org/A267824): 283686649 = 16843², 4514260853041 = 2124679², squares of
the Wolstenholme primes; McIntosh, "On the converse of Wolstenholme's theorem", Acta Arith. 71 (1995)). So
a(283686649) = 0 with 283686649 composite. The "if" direction holds for every odd prime (Babbage/Wolstenholme for
p ≥ 5, and a(3) = 0 directly).

**Argument.** Put B = C(2n−1,n−1), c = C(2n−2,n−1). Then C(2n,n) = 2B and nB = (2n−1)c, so with
D = C(2n,n) − c: (2n−1)(D − (n+2)) = (3n−2)(B − 1) − 2n². Since 0 < n + 2 < n², a(n) = 0 iff n² | D − (n+2).
2n − 1 is prime to n, and 3n − 2 is prime to n for odd n, so a(n) = 0 iff n² | B − 1.

Lean: [full proof](A220956/A220956_mathlib.lean).

### [A221564](A221564/): a(3k+1) = 2k for the FO4C3 shuffle

**Source.** [A221564](https://oeis.org/A221564), the number of FO4C3 moves (flip the top four cards over as a
unit, then cut three cards from top to bottom) that restore a packet of n cards in order and orientation.
Comment: "Conjecture: a(3k+1) = 2k." (OEIS text, CC BY-SA 4.0, read 2026-11-06.)

**Result.** True (known): A. Howroyd (Apr 27 2020) added the cycle description and the formula
a(3n+1) = 2n, a(3n) = a(3n−1) = 2n(n−1) to the entry. Reproved here in Lean for a(3k+1).

**Argument.** Number positions 0..n−1 from the top. One move sends position 0 to 0 (flipped), positions
1, 2, 3 to n−1, n−2, n−3 (flipped) and p ≥ 4 to p − 3. For n = 3k+1 the positions ≡ 2 (mod 3) form one cycle of
length k with one flip, the positions ≡ 0, 1 (mod 3) (except 0) form one cycle of length 2k with two flips, and
the top card flips each move. So 2k moves restore everything, and the card at position 2 is back unflipped only
after a multiple of 2k moves.

Lean: [full proof](A221564/A221564_mathlib.lean).

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

### [A223925](A223925/): a(2n) = 4^n divides A132049(2n)

**Source.** [A223925](https://oeis.org/A223925) (Paul Curtz, 2013): a(2n+1) = 2n-1, a(2n) = 4^n. Comment:
"Conjecture: a(2n) is always a divisor of A132049(2n)." [A132049](https://oeis.org/A132049): numerator of
2n A000111(n-1)/A000111(n) in lowest terms. (OEIS text, CC BY-SA 4.0, A223925 revision #37 of Jul 30 2018, A132049
revision #49 of Jun 28 2026, checked 2026-11-06.)

**Result.** True, and sharp: v_2(A132049(2n)) = 2n exactly for every n >= 1, so 4^n divides A132049(2n) and
A132049(2n)/4^n is odd.

**Argument.** A132049(2n) is the numerator of 4n T_n / E_n with T_n = A000111(2n-1) = A000182(n) (tangent number)
and E_n = A000111(2n) = A000364(n) (secant number).
1. E_n is odd (classical: E_n == 1 mod 2, from the secant series sec x = 1/cos x mod 2, or the Seidel triangle
   mod 2). So the gcd removed in lowest terms is odd and v_2(numerator) = v_2(4n T_n) = 2 + v_2(n) + v_2(T_n).
2. T_n = 2^{2n}(2^{2n}-1)|B_{2n}|/(2n) = 2^{2n-2} G_n / n with G_n = 2(2^{2n}-1)|B_{2n}| the Genocchi number
   A110501(n). By von Staudt-Clausen B_{2n} = A - sum_{(p-1) | 2n} 1/p with A an integer; for odd p in the sum,
   p | 2^{2n} - 1 (Fermat), and the p = 2 term contributes 2^{2n} - 1, which is odd. Hence G_n is an odd integer and
   v_2(T_n) = 2n - 2 - v_2(n).
3. So v_2(A132049(2n)) = 2 + v_2(n) + 2n - 2 - v_2(n) = 2n.
The ingredients (secant numbers odd, tangent-Bernoulli formula, von Staudt-Clausen, Genocchi numbers odd) are
classical; the conjecture is a direct consequence. Curtz's remark that the quotients begin like A110501 is the
Genocchi factor of step 2.

Lean: needs Mathlib.

### [A224529](A224529/): a(np) ≡ a(n) mod p for (p/23) = 1 (proved by Osburn and Sahu)

**Source.** OEIS [A224529](https://oeis.org/A224529) (f_n of Osburn and Sahu), comment by
Michael Somos (Sep 21 2013): "Conjecture 1.1 of Osburn and Sahu is if p is a prime and
JacobiSymbol(p, 23) = 1 and n>0 then a(n * p) == a(n) (mod p)."

**Reading.** f(z) = Σ_{m,n} q^{m²+mn+6n²}, t = η(z)η(23z)/f(z), and a(n) = f_n is the
coefficient of tⁿ in f written as a power series in t (the entry's definition).

**Result.** True; proved. Conjecture 1.1 in the cited paper is the conjecture of Chan, Cooper
and Sica, and the paper proves it: Theorem 1.2 of R. Osburn, B. Sahu, *Congruences via
modular forms*, Proc. AMS 139 (2011) 2375–2381 (arXiv:0912.0173) gives
f_{np^r} ≡ f_{np^{r−1}} (mod p^r) for all n, r ≥ 1 and primes p with (p/23) = 1; r = 1 is the
claim. The comment's wording ("conjecture") is out of date, not a different claim.

**Argument.** (Osburn–Sahu, not re-derived.) f and t relate to the weight-3 Eisenstein space
E₃(Γ₀(23), (·/23)); the congruences follow from the coefficient congruences of those
Eisenstein series by the Beukers-type argument for power series in a modular function.

Lean: —.

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

### [A225611](A225611/): Sun's Legendre-symbol determinant vanishes on a residue class

Lean: [full proof](A228095/A225611_mathlib.lean).

### [A226160](A226160/): a(n+1)/a(n) → exp(1/φ) = 1.855276958... (harmonic-number threshold)

**Source.** OEIS [A226160](https://oeis.org/A226160): least positive integer k with 1 + 1/2 + ... + 1/k > n/φ, φ the golden ratio.
Conjecture: "a(n+1)/a(n) converges to 1.8552..." (OEIS text, CC BY-SA 4.0.) The entry adds "Conjecture
confirmed" with limit exp(1/φ) = 1.855276958... (J.-F. Alcover, 2013, from the expansion of the harmonic numbers).

**Result.** True: a(n+1)/a(n) → exp(1/φ).

**Argument.** H_k - log k decreases to Euler's γ, and H_k < log k + γ + 1/(2k). With c = 1/φ,
H_(a-1) ≤ c n < H_a for a = a(n), so log(a - 1) + γ < c n < log a + γ + 1/(2a). Hence
log a(n) = c n - γ + o(1), and a(n+1)/a(n) = exp(c + o(1)) → exp(c).

Lean: [full proof](A226160/A226160_mathlib.lean).

### [A226163](A226163/): Sun's Legendre-symbol determinant vanishes on a residue class

Lean: —.

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

### [A227145](A227145/): a(F_n) = F_(n-2)

**Source.** [A227145](https://oeis.org/A227145), Frank Ruskey, Jul 04 2013: "Numbers satisfying an infinite nested
recurrence relation", a(n) = n - 1 - a(n-1) - a(a(n-2)) - a(a(a(n-3))) - ..., a(n) = 0 for n <= 1. Comment:
"Conjecture: a(F_n) = F_{n-2} for n>1". (OEIS text, CC BY-SA 4.0, revision #30 of Nov 05 2025, checked
2026-11-06.)

**Reading.** The sum runs over i = 1..n (as in the entry's Mathematica program); terms with i >= n vanish
because a(0) = 0. The Lean theorem is stated for every function a : ℤ → ℤ satisfying the recurrence, and
`exists_solution` shows there is one; `eq_C` shows it is unique.

**Result.** True: a(F_m) = F_(m-2) for every m >= 2. Known: Celaya and Ruskey (arXiv:1307.0153, Prop. 10)
proved the even case; Burcsi, Celaya and Ruskey, "An infinite nested recurrence relation that takes on
Fibonacci values at Fibonacci indices" (Fibonacci Quarterly format, copy at
sites.math.rutgers.edu/~zeilberg/akherim/ruskey15.pdf), proved both cases (their Corollary 2.2). Reproved here
with a full Lean proof.

**Argument.** (Self-contained; it follows the morphic-word picture of Celaya and Ruskey but avoids their tree.)
1. *The word.* Let sig map a letter k to the block (k+1) 0^(k+1), and let w = w_0 w_1 ... be the infinite word
   with w = 0 sig(w). With L(p) = w_0 + ... + w_(p-1) and st(p) = 1 + 2p + L(p), block p of w (positions
   st(p) .. st(p) + w_p + 1) reads w_p + 1, 0, ..., 0, and the blocks tile all positions >= 1.
2. *The candidate.* c(n) = number of nonzero letters among w_0 .. w_(n-1). The nonzero letters at positions
   >= 1 are exactly the block starts, so c(st(p)) = p, and a nonzero letter at t = st(p) has
   w_(c(t+1)-1) = w_t - 1.
3. *Iterates.* By induction on j, c^j(u+1) - c^j(u) = 1 if j <= w_u and 0 otherwise.
4. *Coverage.* For t >= 1 the number of j in 1..t with j <= w_(t-j) is 1 if w_t = 0 and 0 otherwise: such a j
   says the block starting at t - j reaches t, and blocks are disjoint.
5. *Recurrence.* Steps 3 and 4 give c(N+1) + sum_{i=1..N} c^i(N+1-i) = N by induction on N, which is the entry's
   recurrence for c. A solution of the recurrence is unique (strong induction; all iterates stay below n
   because c(m) <= m). So a = c.
6. *Fibonacci values.* L(st(p)) = L(p) + p and the letter before st(p) is 0 (p >= 1). Starting from
   L(F_1) = F_0 and L(F_2) + 1 = F_1, induction gives st(F_(2k+1)) = F_(2k+3) + 1 and st(F_(2k+2)) = F_(2k+4),
   hence c(F_(2k+3)) = F_(2k+1) and c(F_(2k+4)) = F_(2k+2); also c(F_2) = c(1) = 0.

Lean: [full proof](A227145/A227145_mathlib.lean).

### [A227609](A227609/): OEIS A227609

Lean: —.

### [A227781](A227781/): a(n) = 4 iff 8 | n, a(n) = 3 iff n = 4 mod 8

Lean: [full proof](A227784/A227784_mathlib.lean).

### [A227784](A227784/): -1 as a sum of fourth powers / squares mod n

**Source.** [A227781](https://oeis.org/A227781) "Least number of squares which add to -1 mod n" and
[A227784](https://oeis.org/A227784) "Least number of fourth powers which add to -1 mod n" (both offset 1,
Charles R Greathouse IV, 2013). Conjectures in the entries:
- A227781: "a(n) = 4 if and only if n is divisible by 8 and a(n) = 3 if and only if n is 4 mod 8."
- A227784: "a(n) = 15 if n = 9 mod 16 and a(n) = 7 if n = 8 mod 16, otherwise a(n) <= 4."
(OEIS text, CC BY-SA 4.0, checked 2026-11-06; the history shows no change to either conjecture.)

**Reading.** A227784 as printed is false: a(9) = 2 (1^4 + 2^4 = 17 = -1 mod 9), and the b-file has a(n) = 15
exactly for n = 0 mod 16 (n <= 10000) while the n = 9 mod 16 values lie in 1..4. Fourth powers mod 16 are 0, 1,
so "the associated lower bounds are obvious" fits n = 0 mod 16 only. We read "9 mod 16" as a typo for "0 mod 16"
and prove that version; the literal version is refuted separately.

**Result.** For n >= 1:
- A227781: a(n) = 4 iff 8 | n; a(n) = 3 iff n = 4 (mod 8); a(n) <= 2 otherwise. True as stated.
- A227784: a(n) = 15 if n = 0 (mod 16), a(n) = 7 if n = 8 (mod 16), a(n) <= 4 if 8 does not divide n.
  True with the corrected residue; false as printed (n = 9).

**Argument.** Let r_d(n) be the least k with -1 a sum of k d-th powers in Z/nZ.
1. *Padding and CRT.* 0 is a d-th power, so a representation with k terms gives one with any m >= k terms. If
   gcd(m, n) = 1 and -1 is a sum of k d-th powers mod m and mod n, the CRT ring isomorphism
   Z/mn = Z/m x Z/n gives one mod mn. Hence r_d(mn) = max(r_d(m), r_d(n)) for coprime m, n, and r_d(m) >= r_d(m')
   when m' | m (reduce mod m').
2. *Odd prime powers.* For an odd prime p: -1 is a sum of two squares mod p (Mathlib `ZMod.sq_add_sq`). For fourth
   powers, the set A of fourth powers mod p (with 0) has |A| >= 1 + (p-1)/4, since x -> x^4 is at most 4-to-1 on
   nonzero residues; Cauchy-Davenport gives |A+A+A+A| >= min(p, 4|A| - 3) = p, so -1 is a sum of four fourth
   powers mod p. Not every term is 0 (since -1 != 0), so some term y has p not dividing d*y^(d-1) (d = 2, 4). Hensel
   lifting of that one variable (y -> y + p^j s with s = -t u, where u*d*y^(d-1) + v*p = 1) gives a representation
   with the same number of terms mod every p^j. With step 1: r_2(m) <= 2 and r_4(m) <= 4 for odd m.
3. *Powers of 2.* Squares: mod 2, 1 = 1^2; mod 4, -1 = 3 needs three squares (squares are 0, 1) and has them;
   mod 8, squares are 0, 1, 4 and no three sum to 7; for 8 | n, n - 1 is a sum of four squares (Lagrange).
   Fourth powers: mod 2, 4, 8, 16 they are 0, 1, so -1 needs 1, 3, 7, 15 of them, and 1, 3, 7 ones suffice mod 2,
   4, 8. For 2^e with e >= 4: there is an odd y with y^4 = -15 mod 2^e (e = 4: y = 1; if y^4 + 15 = 2^e t with t odd,
   replace y by y + 2^(e-2)), so -1 = 14*1 + y^4.
4. Combining 2 and 3 with step 1 gives every claimed value; the lower bounds come from reducing mod 4, 8 or 16.

Lean: [full proof](A227784/A227784_mathlib.lean).

### [A227968](A227968/): OEIS A227968

Lean: —.

### [A227971](A227971/): OEIS A227971

Lean: —.

### [A228005](A228005/): OEIS A228005

Lean: —.

### [A228304](A228304/): OEIS A228304

Lean: —.

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

### [A229136](A229136/): a(n) = A131885(n) * 2^(n-1) (proved in the entry, reproved in Lean)

**Source.** [A229136](https://oeis.org/A229136) (offset 1), "Number of solutions to Sum_{i=1..n} x_i^2
== 1 (mod 4) with x_i in 0..3." Comment: "Conjecture: a(n) = A131885(n)*2^(n-1) for n >= 1.
[Corrected by Petros Hadjicostas, Dec 20 2019]". [A131885](https://oeis.org/A131885): a(0..3) = 1, 2,
4, 6 and a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) for n >= 4. (OEIS text, CC BY-SA 4.0; A229136 revision
#55 of Aug 16 2025, checked 2026-11-06.)

**Reading.** The scan record quotes the older form a(n) = A131885(n)*2^n, which is false for every
n >= 1 (a(1) = 2, A131885(1)*2 = 4); the exponent n-1 is the entry's current text and matches the
data.

**Result.** True for every n >= 1: a(n) = A131885(n) * 2^(n-1). Already proved in the entry by
P. Hadjicostas (Dec 20 2019) from the recurrence a(n) = 4a(n-1) - 8a(n-2) + 2^(2n-3), which he takes
from the theory of A330619. The argument below is self-contained.

**Argument.** Let c_r(n) count the vectors in {0..3}^n with sum of squares = r mod 4. The squares
of 0, 1, 2, 3 are 0, 1, 0, 1 mod 4, so splitting off x_1 gives c_r(n+1) = 2 c_r(n) + 2 c_{r-1}(n)
(indices mod 4), with c(0) = (1, 0, 0, 0). Then c_0 - c_1 + c_2 - c_3 = 0 for n >= 1 (each step maps
the alternating sum to 0). In vector form c(n+1) = 2(I + P)c(n) with P the cyclic shift, and
8(I+P)^3 - 32(I+P)^2 + 48(I+P) - 32 I = -8(I - P + P^2 - P^3), whose residue-1 row is 8 times the
alternating sum. So c_1(n+4) = 8c_1(n+3) - 24c_1(n+2) + 32c_1(n+1) for n >= 0. With c_1(1), c_1(2),
c_1(3) = 2, 8, 24 = A131885(n)*2^(n-1) for n = 1, 2, 3, induction gives the formula, since
2^(n+3) A131885(n+4) = 8*2^(n+2)A131885(n+3) - 24*2^(n+1)A131885(n+2) + 32*2^n A131885(n+1).

Lean: [full proof](A229136/A229136_mathlib.lean).

### [A230168](A230168/): every prime 45·2^n − 1 ends in 9

**Source.** OEIS [A230168](https://oeis.org/A230168), primes of the form 45·2^n − 1. Comment:
"Conjecture: each term in the sequence ends with digit 9." (OEIS text, CC BY-SA 4.0.)

**Result.** True, and already answered in the entry: Alonso del Arte (Oct 11 2013) notes that every
term is ≡ 89 (mod 90), hence ends in 9.

**Argument.** n = 0 gives 44, not prime. For n ≥ 1, 45·2^n = 10·(9·2^(n−1)), so 45·2^n − 1 ≡ 9 (mod 10).

Lean: [full proof](A230168/A230168_mathlib.lean).

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

### [A002383](A002383/): A002383 \ {3} = A085104 ∩ A059055 (open; inclusion ⊆ proved)

Lean: [checked](A007645/A007645_mathlib.lean).

### [A054979](A054979/): "every e-perfect number is divisible by 36" is equivalent to the open Straus-Subbarao question

**Source.** OEIS [A054979](https://oeis.org/A054979) (e-perfect numbers, sum of exponential
divisors = 2k), comment by Jon Perry (Nov 13 2012): "Conjecture: Every e-perfect number is
divisible by 36, see A219016." (OEIS text, CC BY-SA 4.0.)

**Result.** Partial; the claim is equivalent to a known open problem.
- 4 | n holds for every e-perfect n (from Straus-Subbarao, below).
- 9 | n for every e-perfect n is equivalent to: no e-perfect number is coprime to 3. That is the
  question raised by Straus and Subbarao; Fabrykowski and Subbarao showed that an e-perfect
  number not divisible by 3 exceeds 10^664 (with further necessary conditions), and
  Lelechenko (arXiv:1405.7597, 2014) still lists it as open. No later resolution found.
So the conjecture is open, and it is exactly the "3 does not divide" question.

**Argument.** σ_e is multiplicative with σ_e(p^a) = sum_{d | a} p^d, and σ_e(p) = p.
So if p || n then σ_e(n)/n = σ_e(n/p)/(n/p): n is e-perfect iff n/p is.
(i) Straus-Subbarao (1974): no odd e-perfect numbers. Hence n is even, and if 2 || n then n/2
would be an odd e-perfect number, so 4 | n.
(ii) If 3 || n then n/3 is e-perfect and coprime to 3. So "9 | n for all e-perfect n" holds iff
"3 | n for all e-perfect n", which is the open question. Conversely a counterexample to the
open question is itself a counterexample to the conjecture.
The b-file (10000 terms, Eldar) has every term divisible by 36 (checked 2026-11-06).

Lean: —.

### [A073117](A073117/): Cloitre's eventual-increment conjecture (partial: listed values confirmed)

**Source.** [A073117](https://oeis.org/A073117), a(n+1) = a(n) + (a(n) mod n), a(1) = 1. Comment by B. Cloitre
(Aug 20 2002): for integers a and b(1), if b(n+1) = b(n) + (b(n) mod (n+a)), there is an integer x(a, b(1)) with
b(n+1) = b(n) + x(a, b(1)) for all large n; listed: x(0,1) = x(1,1) = x(2,1) = 97, x(3,1) = 1, x(4,1) = 3,
x(5,1) = 3, x(6,1) = 6, x(97,1) = 43, x(0,11) = 2. (OEIS text, CC BY-SA 4.0, rev #20, read 2026-11-06.)
The same dynamics is A094405/A066910 (partial sums S of A094405 satisfy S(n) = S(n-1) + (S(n-1) mod n)).

**Result.** Partial. The nine listed values are correct (proved). The general statement is open.

**Argument.** Stable state: if b(N) = x(N + a + 1) with 0 ≤ x < N + a, then b(N) mod (N + a) = x and
b(N+1) = x(N + a + 2), so b grows by x from then on. The nine cases reach a stable state at N = 397, 396, 395,
4, 11, 10, 25, 124, 5 respectively.

Why the general case is hard: write b(n) = k(n+a) + r and e = r − k. While the quotient k stays fixed, e
doubles at each step (e' = 2e), and in general e' ≡ 2e (mod n + a + 1) inside a window of length n + a. The
sequence becomes eventually linear exactly when e reaches 0. Heuristically this happens with probability about
1/n per step, so the stopping time has a tail of order 1/t: for b(1) = 1..100000 (a = 0, A094405 form) every
seed stabilises, the latest at n = 9363863 (seed 31873). Proving that e always reaches 0 is a Collatz-type
problem.

Lean: [full proof](A073117/A073117.lean).

### [A094358](A094358/): Munafo's conjecture is equivalent to "all Fermat numbers are squarefree"

**Source.** [A094358](https://oeis.org/A094358), "Squarefree products of factors of Fermat numbers". Comment:
"Conjectured (by Munafo, see link) to be the same as: numbers n such that 2^^n == 1 mod n, where 2^^n is
A014221(n)." The entry adds that one inclusion follows from Alekseyev's observations and the CRT, and that "the
converse is true iff all Fermat numbers are squarefree". (OEIS text, CC BY-SA 4.0, revision #66, checked
2026-11-06.)

**Result.** Not settled. Proved (in Lean): (1) every term of A094358 satisfies 2^^n == 1 (mod n); (2) Munafo's
conjecture holds if and only if every Fermat number is squarefree, an open problem. The equivalence is the one
asserted in the entry; the proof here is complete.

**Argument.** 1. For n >= 2, 2^^n = 2^(2^(2^^(n-2))), so 2^^n == 1 (mod n) gives n | 2^(2^j) - 1 with j = 2^^(n-2). Conversely,
   if n | 2^(2^j) - 1 then n is odd, the order of 2 mod n divides 2^j, so it is 2^i with 2^i <= phi(n) < n, so
   i < n <= 2^^(n-2) + 1, and 2^i divides 2^^(n-1) = 2^(2^^(n-2)); hence 2^^n == 1 (mod n).
2. 2^(2^j) - 1 = F_0 F_1 ... F_(j-1), and Fermat numbers are pairwise coprime (Mathlib).
3. A term of A094358 is the product of its distinct primes, each dividing some F_k; it divides F_0 ... F_(J-1) for
   J large, so (1) applies.
4. If all F_k are squarefree, every divisor of F_0 ... F_(j-1) is squarefree and its primes divide some F_k, so
   the two sets agree. If p^2 | F_k for a prime p, then n = p^2 divides 2^(2^(k+1)) - 1, so 2^^n == 1 (mod n),
   but p^2 is not squarefree: the sets differ.

Lean: [full proof](A094358/A094358_mathlib.lean).

### [A139250](A139250/): holes of the toothpick structure are rectangles (side lengths still open)

**Source.** OEIS [A139250](https://oeis.org/A139250), conjecture listed on the OEIS wiki
(Talk:Conjectures/List): "Consider the rectangles in the sieve (including the squares). The area
of each rectangle (A = b*c) and the edges (b and c) are powers of 2, but at least one of the edges
(b or c) is <= 2." (OEIS text, CC BY-SA 4.0.)

**Reading.** Unit length = half a toothpick. A toothpick is a closed axis-parallel segment of
length 2 with lattice centre c and endpoints c ± e (e a unit vector); it covers the three lattice
points c - e, c, c + e. Stage 1 is the vertical toothpick centred at the origin. At stage n ≥ 2,
for every toothpick placed at stage n - 1 and every endpoint p of it, p is *exposed* if no other
toothpick placed so far contains p; a toothpick perpendicular to the parent and centred at p is
added at every exposed p. (This is the OEIS rule "an end is exposed if it does not touch the end
or the middle of another toothpick"; `certificate/sim.py` and `certificate/check_lemmas.py`
reproduce A139250.) L is the union of all toothpicks over all stages (the "sieve"). A *hole* (a
"rectangle in the sieve") is a bounded connected component of R² \ L. Every point lies inside the
box |x| ≤ 2^(k-1) - 1, |y| ≤ 2^(k-1) for large k, and that box has its whole boundary in L from
stage 2^k on, so holes are exactly the bounded faces seen inside these boxes.

**Result.** Partial.
- New proof (statement known): every hole is the open rectangle (x0, x0+w) × (y0, y0+h) with
  integers w, h ≥ 1, its whole boundary in L and no point of L inside (Theorem 1). Applegate, Pol
  and Sloane state that all internal regions are rectangles ("We omit the proof"); the proof below
  is local and uses no self-similarity.
- New: each side of a hole is covered by collinear toothpicks of one single stage, and every such
  toothpick centred inside the side has its parent outside the hole (Corollary 2).
- Open here: the side lengths are powers of 2 and the shorter side is ≤ 2. Checked to stage 512
  (116496 holes, round r14) and re-checked to stage 256 by `check_lemmas.py`. Shapes seen at
  stage 2^K: 1×2^j for j ≤ K-3 and 2×2^j for j ≤ K-2.

**Argument.** *Lemma 1 (orientation and parity).* Toothpicks of stage n are vertical iff n is odd. Vertical
toothpicks have centres with x + y even, horizontal ones with x + y odd.
Proof: induction on n. A child is perpendicular to its parent and centred at a parent endpoint
c ± e, which changes the parity of x + y.

*Lemma 2 (no overlap).* No unit segment lies in two toothpicks.
Proof: both unit segments of a toothpick t contain its centre p. Let t be placed at stage n and
let u ≠ t be placed at stage ≤ n with a common unit segment, so u contains p. If u is placed before
stage n, then u is not the parent (the parent is perpendicular and meets t only at p, sharing no
segment), so p was not exposed, a contradiction. If u is placed at stage n, then u ∥ t (Lemma 1);
u ≠ t gives a different centre, and a common unit segment forces the centres to be at distance 1
along the line, which have different parities of x + y, contradicting Lemma 1.

*Lemma 3 (no corners and no dead ends).* For a lattice point p let D(p) be the set of unit
directions d with the segment [p, p+d] in L. Then D(p) is empty, {N, S}, {E, W}, or has at least
3 elements.
Proof: if p is the centre of some toothpick, D(p) contains an opposite pair, and any set with an
opposite pair is in the list. Otherwise every unit segment of L at p lies in a toothpick whose
centre is not p, so p is an endpoint of it. Suppose D(p) is nonempty and let t be a toothpick
ending at p with the smallest stage n. If no other toothpick of stage ≤ n contains p, then p is
exposed after stage n and a toothpick is centred at p at stage n + 1, a contradiction. So some
u ≠ t of stage ≤ n contains p, as an endpoint since p is not a centre, so u has stage n by
minimality. By Lemma 1 u ∥ t, and by Lemma 2 they lie on opposite sides of p, so D(p) contains an
opposite pair.

*Square completion.* Call two edge-adjacent unit cells *joined* if their common edge is not in L.
If a cell a is joined to its horizontal neighbour b and to its vertical neighbour d, let p be the
corner common to a, b, d. Two perpendicular directions at p are missing from D(p). Each set allowed
by Lemma 3 other than ∅ contains one of any two perpendicular directions, so D(p) = ∅ and the
fourth cell at p is joined to b and to d.

*Theorem 1.* Every hole is an open lattice rectangle whose boundary lies in L and whose interior
misses L.
Proof: L is a union of unit lattice segments, so a component of R² \ L is the union of a class of
cells under the joined relation together with the open edges and lattice points between them. Take
a hole and its finite set C of cells. In a row, a *run* is a maximal sequence of consecutive cells
of C, each joined to the next. If one cell of a run R is joined to the cell above it, square
completion applied step by step along R shows that every cell of R is joined to the cell above and
that these cells are joined to each other; so they lie in one run R' of the row above, and the same
argument downwards gives R' = R + (0, 1). Hence C is a stack of equal runs, that is a w × h
rectangle of cells. Its interior edges are not in L, its interior lattice points have D = ∅, and
each boundary edge is in L (otherwise the outside cell would be joined to C).

*Corollary 2 (sides are one-stage chains).* Let p be a lattice point strictly inside a side of a
hole. D(p) contains both side directions and not the inward one. If p is a centre, its toothpick
lies along the side and its parent ends at p from outside. If p is not a centre, the proof of
Lemma 3 gives two parallel toothpicks of the same (smallest) stage ending at p from opposite sides;
they cannot be perpendicular to the side (one would point inward), so they are the two side
toothpicks meeting at p. Walking along the side, consecutive toothpicks therefore have equal stage.

*Toward the size claims (proved lemmas plus a numerically checked decomposition).*
- Mirror lemma (proved). In the full structure no toothpick other than the stage-1 one is centred
  on the x-axis, and the stage-1 and stage-2 toothpicks are the only ones centred on the y-axis; an
  end reaching an axis is reached at the same stage by its mirror image, so it is never exposed.
  Hence the quadrant x, y ≥ 0 evolves as the wall process in which every axis point counts as
  covered, started from the pieces (0,0)-(0,1) and (0,1)-(1,1).
- Seam lemma (proved). Split a wall process by a lattice line ℓ into two half-plane processes that
  treat ℓ as a wall. If for every point of ℓ both sides touch it first at the same stage (or never),
  the joint process is the union of the two, and L carries no segment of ℓ there; a hole meeting ℓ
  is then the union of a boundary room of each side between consecutive touch points.
- Corner decomposition (checked for k = 2..6 by `certificate/decomp_check.py`, not proved). With
  A = 2^(k-1), the quadrant at stage 2^(k+1) is the quadrant at stage 2^k (box [0, A-1] × [0, A],
  sealed, one exposed end at (A, A)), plus the quadrant process restarted at (A, A), plus its mirror
  image in x = A (above the box), plus a *strip process* in x ≥ A - 1, 0 ≤ y ≤ A with walls on all
  three sides started from the half toothpick (A, A)-(A, A-1). The seam y = A has touch points
  (A + 2^i - 1, A) at stage 2^k + 2^(i+1) - 1 from both sides, as the seam lemma needs. The strip of
  height h run 2h stages splits into three copies of the strip of height h/2 (translated, translated,
  flipped) and a fourth block of a new type (lower left), bounded by the sealed line y = h/2 + 1, the
  walls x = 0, y = 0 and the seam x = h/2.

Lean: —.

### [A213381](A213381/): n^n mod (n+2) — zeros and the A176003 values (parts 3–4 open)

**Source.** [A213381](https://oeis.org/A213381), "a(n) = n^n mod (n+2)." Conjectures: (1) indices of zeros are
2^(x+2)−2, x ≥ 0; (2) a(n) = n if n is in A176003 (3q − 2, q = 1 or prime); (3) every k ≥ 0 appears at least
once; (4) every k ≥ 0 appears infinitely often. Robert Israel (May 2015, in the entry) proved (1) and (2).
(OEIS text, CC BY-SA 4.0, checked 2026-11-06.)

**Result.** Partial. (1) and (2) are true (Israel's proofs, formalised here). (3) and (4) are open: a(n) = k
means (−2)^{m−2} ≡ k (mod m) with m = n+2, a congruence of the same type as Graham's 1960 conjecture on
2^n ≡ k (mod n) (OEIS A036236; e.g. the least n with 2^n ≡ 3 (mod n) is 4700063497).

**Argument (1), (2).** n ≡ −2 (mod n+2), so n^n ≡ (−2)^n and (n+2) | n^n iff (n+2) | 2^n iff n+2 = 2^j with
j ≤ n, i.e. n = 2^j − 2 with j ≥ 2. For n = 3q − 2 with q prime, q ∉ {2, 3}: n ≡ 1 (mod 3) gives n^n ≡ n (mod 3);
n = 3(q−1) + 1 and Fermat give n^n ≡ n (mod q); CRT and n < 3q give n^n mod 3q = n. q = 1, 2, 3 by computation.

Lean: [full proof](A213381/A213381_mathlib.lean).

### [A215926](A215926/): the power-of-2 conjectures reduce to almost perfect numbers

**Source.** OEIS [A215926](https://oeis.org/A215926), smallest deficient k such that k·n is perfect or
abundant. Comments: "Conjecture: a(n) is 1, 3, or a power of 2." and "Conjecture: The first occurrence of
2^m happens at A014210(m)" (A014210(m) = nextprime(2^m)). (OEIS text, CC BY-SA 4.0.) Both are open
`research open` statements in google-deepmind/formal-conjectures (`OeisA215926`, m ≥ 1 for the second).

**Result (partial).** Call k *almost perfect* if σ(k) = 2k − 1 (powers of 2 are; no others are known).
1. Conjecture 2 holds for m if and only if no almost perfect k that is not a power of 2 satisfies
   nextprime(2^m) ≤ 2k − 1 and k < 2^m.
2. If such a k exists for some m, Conjecture 1 also fails (at n = nextprime(2^m)).
3. No almost perfect numbers other than powers of 2 exist below 2·10⁷, so Conjecture 2 holds for 1 ≤ m ≤ 24
   (the b-file covers m ≤ 13).
So Conjecture 2 is equivalent to a statement about almost perfect numbers (an open problem, Guy B2) and
Conjecture 1 implies it.

**Argument.** Write A(n) = σ(n)/n; k·n is non-deficient iff A(kn) ≥ 2. Let p = nextprime(2^m), so
2^m < p < 2^(m+1) (Bertrand).
- *a(p).* For k < p, p ∤ k and σ(kp) = σ(k)(p + 1). With d = 2k − σ(k) ≥ 1 (k deficient), kp is
  non-deficient iff (2k − d)(p + 1) ≥ 2kp iff 2k ≥ d(p + 1). Since k < p this forces d = 1 and p ≤ 2k − 1.
  k = 2^m works (2^(m+1) ≥ p + 1), a power 2^j with j < m does not (2^(j+1) ≤ 2^m < p + 1), and 3 does not.
  So a(p) = 2^m unless an almost perfect k, not a power of 2, has p ≤ 2k − 1 and k < 2^m; then a(p) is such a
  k, which is neither 1, 3 nor a power of 2 (this gives 2).
- *Nothing earlier.* For 2 ≤ n < p, a(n) ≤ max(3, 2^(m−1)), so a(n) ≠ 2^m. Write n = 2^e·u, u odd.
  If u = 1, a(n) = 3. If u is prime, u + 1 ≤ 2^m (u < 2^m when e = 0 since n < p and n ≠ 2^m; u < p/2 < 2^m
  when e ≥ 1), and 2^j works once 2^(e+j+1) ≥ u + 1, so j ≤ m − 1. If u is composite with least prime
  factor q ≤ √u, then A(u) ≥ 1 + 1/q and A(2^s·u) = (2 − 2^(−s))·A(u) ≥ 2 once 2^s ≥ (q + 1)/2, so 2^j works
  with 2^j ≤ q < 2^m, again j ≤ m − 1.
  Powers of 2 are deficient, so a(n) ≤ 2^j.

Lean: [witness](A215926/A215926_mathlib.lean).

### [A219033](A219033/): the sequence is infinite; the 6*A185208(n) ratio conjecture is false

**Source.** [A219033](https://oeis.org/A219033) (Jon Perry, 2012): numbers k such that k = x + y,
sigma_1(k) = sigma_1(x) + sigma_1(y) and sigma_2(k) = sigma_2(x) + sigma_2(y). Five conjectures in the entry: the
sequence is infinite; it has only even terms; the parts are even; no term satisfies the sigma_3 equality; "With the
lower partition as 6*A185208(n) and the upper partition 214/3 = 71.3333... of this, then the equalities are
satisfied." (OEIS text, CC BY-SA 4.0, revision #36 of Feb 24 2026, checked 2026-11-06.) A185208: numbers with no
divisor d > 1 such that d + 1 is a prime power.

**Result.** 1. Conjecture 1 is true: 434m is a term for every m coprime to 2*3*7*31*107 (parts 428m and 6m).
2. Conjecture 5 is false: 107 is in A185208, but x = 6*107 = 642, y = 428*107 = 45796 gives
   sigma_1(46438) - sigma_1(45796) - sigma_1(642) = 749 != 0 (and the sigma_2 difference is 240429).
3. Conjectures 2-4 (even terms, even parts, no sigma_3 solution) remain open; they hold for k <= 16100.

**Argument.** 434 = 2*7*31, 428 = 4*107, 6 = 2*3. sigma_1: 768 = 756 + 12; sigma_2: 240500 = 240450 + 50. If m is
coprime to 4*3*7*31*107 then m is coprime to 434, 428 and 6, and multiplicativity of sigma_k gives
sigma_k(434m) = sigma_k(434)sigma_k(m) = (sigma_k(428) + sigma_k(6))sigma_k(m) = sigma_k(428m) + sigma_k(6m) for
k = 1, 2. The m = 278628t + 1 are pairwise distinct and coprime to 278628, so the sequence is infinite. For m = 107
the factor 107 divides 428, sigma_1(428*107) = sigma_1(4)sigma_1(107^2) = 7*11557 = 80899, sigma_1(642) =
12*108 = 1296, sigma_1(46438) = 768*108 = 82944, and 82944 - 80899 - 1296 = 749. The first-12 partitions quoted in
the entry are the m in A185208 below 107; A185208 contains every prime other than 2 and the Mersenne primes, and
107 is the first member sharing a factor with 428.

Lean: [full proof](A219033/A219033_mathlib.lean).

### [A227012](A227012/): the case g(n) = n^3, f(k) = 1/k

**Source.** OEIS [A227012](https://oeis.org/A227012), a(n) = ⌊M(n)⌋ with M(n) the harmonic mean of
(n−1)^3 + 1, ..., n^3. Comment (C. Kimberling, 2013): "Conjecture: if f(k) = u/(v*k + w), where u,v,w are integers,
and g(n) is a polynomial, then the sequence with n-th term m(n) = floor(M(n)) is linearly recurrent", followed by
three refined cases; case (3) is g cubic with recurrence coefficients 3, −3, 1, 1, −3, 3, −1, e.g. A227012. The
entry's formulas (recurrence for n ≥ 10, g.f., closed forms) are marked "conjectured". (OEIS text, CC BY-SA 4.0,
checked 2026-11-06.) This directory also indexes the related records grouped with it in the scan: A219085
(settled, [`../A219085/`](A219085/README.md)), A225919 (settled, [`../A225919/`](A225919/README.md)),
A225920–A225922 (open).

**Result (partial).** For the entry's own sequence: a(n) = ((2n−1)^3 + 4) div 8 = ⌊(n − 1/2)^3 + 1/2⌋ for
n ≥ 3 (a(1) = 1, a(2) = 4). Hence the entry's recurrence a(n) = 3a(n−1) − 3a(n−2) + a(n−3) + a(n−4) − 3a(n−5) +
3a(n−6) − a(n−7) holds for n ≥ 10, and its g.f. and closed forms follow. The general conjecture (all u, v, w and
polynomials g) is not settled here.

**Argument.** Let A = (n−1)^3, B = n^3, L = B − A, s = H_B − H_A, M = L/s, T = (n − 1/2)^3 + 1/2.
1. Midpoint rule for the convex 1/x: 1/k ≤ ln((k+1/2)/(k−1/2)) ≤ 1/k + 1/(9k^3). Summing, V − 1/(18A^2) ≤ s ≤ V
   with V = ln((B+1/2)/(A+1/2)) = 2 artanh(z), z = L/(A+B+1), and 2z(1 + z^2/3) ≤ V ≤ 2z(1 + z^2/3 +
   z^4/(5(1−z^2))).
2. These give rational-function bounds L/V_up ≤ M ≤ L/(V_lo − 1/(18A^2)); both lie strictly within 1/8 of T for
   all n ≥ 12 (exact sign analysis of the numerator and denominator polynomials, sympy). For 3 ≤ n ≤ 11 interval
   arithmetic gives |M − T| < 1/8 directly. (M − T = −1/(80n) + O(n^(−2)).)
3. T = ((2n−1)^3 + 4)/8 has odd numerator, so its fractional part is 1/8, 3/8, 5/8 or 7/8; with |M − T| < 1/8,
   ⌊M⌋ = ⌊T⌋. ⌊T⌋ is a cubic polynomial plus a sequence of period 4, which satisfies the recurrence with
   characteristic polynomial (x−1)^3 (x^4 − 1).

Lean: —.

