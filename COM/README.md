# Coman, Conjectures on Fermat Pseudoprimes

M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes*, 2013. C = conjecture (part one), P = open problem (part four). Statements are paraphrased.

116 entries: 114 resolved by this project, 2 answered elsewhere, 0 disputed or partial.

Of the 114 resolutions: 109 proved in full in Lean, 5 with the finite facts (witnesses) checked in Lean and the remaining steps on paper, 0 on paper only (re-derived by a second reader; 0 of these need Mathlib to formalise).

Columns: **Lean** says how far Lean checks the result (`full proof`: the whole statement; `witness`: the finite facts, with the steps outside Lean named in the problem README; `needs Mathlib`: written proof only). **Prior art** (review 2026-11-04, sources in each problem README): `new` = no source found stating the answer, `partly-known`, `known`; "(immediate)" = follows in a few lines from a known theorem. **Verdict**: proved, disproved, or trivial/misstated. **Result**: one-line summary. **Method** links to [methods/](../methods/README.md). Each problem directory holds the README (source, reading, result, argument, evidence, review level, prior art), the Lean file and `certificate/` scripts.

## Resolved by this project

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [C003](C003/) | proved | (n^(nk+k+n-1) - 1)/(n^2 - 1) is a base-n psp for infinitely many k | [full proof](C003/C003_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [parametric-family](../methods/parametric-family/README.md) |
| [C004](C004/) | disproved | 3-Poulet numbers without a factor 23 mod 30 are not all of the stated shape | [full proof](C004/C004.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C006](C006/) | disproved | Poulet numbers p^2 + 81p + 3pq with p = 30k+13, q = 30k+41: only two | [full proof](C006/C006_mathlib.lean) | new (immediate) | [reduction-to-constant](../methods/reduction-to-constant/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C011](C011/) | trivial or misstated | No 3-Carmichael (6x+1)(6y+1)(6z-1): true part and false part | [full proof](C011/C011_mathlib.lean) | partly-known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [C012](C012/) | disproved | Digit-sum relations for Carmichael numbers with all factors 6k+1 | [full proof](C012/C012_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C013](C013/) | proved | (30n+7)(60n+13)(150n+31) is Carmichael when all factors are prime | [full proof](C013/C013_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [C014](C014/) | proved | (30n-29)(60n-59)(90n-89)(180n-179) is Carmichael when all factors are prime | [full proof](C014/C014_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [C015](C015/) | proved | (330n+7)(660n+13)(990n+19)(1980n+37) is Carmichael when all factors are prime | [full proof](C015/C015_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [C016](C016/) | proved | (30n-7)(90n-23)(300n-79) is Carmichael when all factors are prime | [full proof](C016/C016_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [C017](C017/) | proved | (30n+13)(90n+37)(150n+61) is Carmichael when all factors are prime | [full proof](C017/C017_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [finite-identity](../methods/finite-identity/README.md) |
| [C019](C019/) | disproved | 3-Carmichael factor pattern d1(n+1) - n fails | [full proof](C019/C019_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C021](C021/) | proved | p(2p+1) - 2kp is a base-(p+1) psp: true for odd p, false for p = 2 | [full proof](C021/C021.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C022](C022/) | proved | p(2p-1) - 2kp is a base-(p-1) psp | [full proof](C022/C022.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C023](C023/) | proved | pq psp base p+1 when q^2 = 2p - 1: fails at (5, 3) | [full proof](C023/C023_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C024](C024/) | disproved | p(kp - k + 1) is not always a psp to bases kp - k and kp - k + 2 | [full proof](C024/C024.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C025](C025/) | disproved | Not every prime is (Cq - 1)/(q - 1) | [full proof](C025/C025.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md) |
| [C026](C026/) | disproved | 360ab + 1 = c^2 does not give Carmichael multiples of ab | [full proof](C026/C026.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [C027](C027/) | disproved | n^E = n (mod 544) fails for the Euler pseudoprime 561 | [full proof](C027/C027_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C029](C029/) | disproved | Poulet p2 = (p1 - d)n + d fails for 561 and 341 | [full proof](C029/C029.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C031](C031/) | disproved | Poulet numbers with three or more factors: P = q((r+1)q - r) fails | [full proof](C031/C031.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C032](C032/) | disproved | Exceptions are not only 5461(42k - 13) | [full proof](C032/C032_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C035](C035/) | trivial or misstated | P = 8pn + p^2 for one prime factor implies all (trivial) | [full proof](C035/C035.lean) | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [C037](C037/) | proved | Infinitely many Poulet numbers (n+1)p^2 - np with p Poulet | [witness](C037/C037.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C042](C042/) | trivial or misstated | Carmichael numbers divisible by p and 2p - 1 (true, short) | [full proof](C042/C042_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [C044](C044/) | trivial or misstated | Carmichael numbers (30a+1)(30b+1)(30c+11) do exist | [full proof](C044/C044_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C045](C045/) | disproved | Three-term APs of Carmichael numbers without divisibility | [full proof](C045/C045_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C050](C050/) | proved | Infinitely many base-3 psp (3^(4k+2) - 1)/8 | [full proof](C050/C050_mathlib.lean) | known | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C051](C051/) | proved | Poulet numbers divisible by 23 and 67 are 23\*67\*(66n + 23) | [full proof](C051/C051.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C054](C054/) | proved | Poulet numbers divisible by 11 and 61 are 11\*61\*(60n + 11) | [full proof](C054/C054.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C055](C055/) | disproved | The C054 shape fails for p = 30k + 11, q = 180k + 61 | [full proof](C055/C055.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C058](C058/) | disproved | 2-Poulet numbers (q 2^a 3^b 5^c +- 1) 2^n + 1 fail | [full proof](C058/C058_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C076](C076/) | proved | Infinitely many Poulet numbers divisible by 15 with SCD1 beginning 2, 4, 7 | [witness](C076/C076.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C077](C077/) | proved | Infinitely many Poulet numbers divisible by 15 with SCD1 beginning 2, 4, 23 | [witness](C077/C077.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C086](C086/) | disproved | The twin pair (3, 5) does not arise from a 2-Poulet number | [full proof](C086/C086_mathlib.lean) | new (immediate) | [reduction-to-constant](../methods/reduction-to-constant/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C088](C088/) | disproved | Only two 2-Poulet numbers with p2 - p1 = 84 | [full proof](C088/C088_mathlib.lean) | new (immediate) | [reduction-to-constant](../methods/reduction-to-constant/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C089](C089/) | disproved | Carmichael numbers divisible by 7 and 13: cofactor not always 1 or 13 mod 18 | [full proof](C089/C089_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C090](C090/) | trivial or misstated | Carmichael numbers divisible by 19 and 37 are 703(18k + 1) | [full proof](C090/C090.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C091](C091/) | disproved | Carmichael numbers n(a(n-1)+1)(b(n-1)+1): fails for 162401 | [full proof](C091/C091_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C095](C095/) | disproved | P - 80n prime fails for 1105 | [full proof](C095/C095.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [C096](C096/) | disproved | P - 150n prime fails for 561 | [full proof](C096/C096.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [C099](C099/) | disproved | Carmichael 1800n^2 +- 840n +- prime: residue obstruction | [full proof](C099/C099_mathlib.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C101](C101/) | proved | p(p+2) + 1729 for twin primes: prime factors 2, 3 and 1, 7, 13, 19 mod 30 | [full proof](C101/C101_mathlib.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [C102](C102/) | trivial or misstated | Odd Poulet numbers are (a^2 - b^2)/8 (trivial) | [full proof](C102/C102.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C103](C103/) | disproved | Digital root and prime factors of Carmichael numbers: fails for 62745 | [full proof](C103/C103_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C108](C108/) | disproved | Carmichael numbers n(n + p)/8 with p a prime power: fails for 162401 | [full proof](C108/C108_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C112](C112/) | trivial or misstated | Carmichael numbers n(n + a)/(a + 1) (trivial) | [full proof](C112/C112.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C116](C116/) | disproved | Only two Carmichael numbers p^4 + 60p | [full proof](C116/C116_mathlib.lean) | new (immediate) | [reduction-to-constant](../methods/reduction-to-constant/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C123](C123/) | disproved | Carmichael numbers pq + q - p: fails for 1024651 | [full proof](C123/C123_mathlib.lean) | new | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C124](C124/) | proved | 3-Carmichael numbers divisible by 5: p(q - 2^n) holds | [full proof](C124/C124_mathlib.lean) | partly-known | [elementary-proof](../methods/elementary-proof/README.md), [reduction-to-constant](../methods/reduction-to-constant/README.md) |
| [C125](C125/) | disproved | 5p + 2^n is not always prime infinitely often | [full proof](C125/C125_mathlib.lean) | partly-known | [covering-congruences](../methods/covering-congruences/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C126](C126/) | false | false (non-constructively, via Wright's theorem); P = 15709 settled at m = 749 | [full proof](P066/P066_mathlib.lean) | new | [complete-table-scan](../methods/complete-table-scan/README.md), [covering-congruences](../methods/covering-congruences/README.md) |
| [C127](C127/) | disproved | (P + 5^m)/30 is composite or non-integral for every m, for infinitely many Poulet P with 5 \| P, 3 ∤ P | [witness](C127/C127.lean) | partly-known | [covering-congruences](../methods/covering-congruences/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C128](C128/) | disproved | (P + 5^m)/10 is composite for every m, for infinitely many Poulet P with 15 \| P | [witness](C128/C128.lean) | partly-known | [covering-congruences](../methods/covering-congruences/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C136](C136/) | disproved | Primes (n + d^k)/d: none for P = 561, d = 3 | [full proof](C136/C136.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [C137](C137/) | disproved | Primes (P + n)/(n + 1) are bounded | [full proof](C137/C137.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [C138](C138/) | proved | Primes p with p^2 = n(P - 1) + 1 | [full proof](C138/C138_mathlib.lean) | new (immediate) | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C139](C139/) | disproved | Primes (q^2 + n)/(n + 1) are bounded | [full proof](C139/C139.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [C140](C140/) | disproved | Primes sqrt((q^2 + n)/(n + 1)) are bounded | [full proof](C140/C140.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [C146](C146/) | disproved | 36(P - d) divisibility for 3-Poulet numbers fails | [full proof](C146/C146.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C147](C147/) | disproved | 36(P - d) divisibility for 2-Poulet numbers fails | [full proof](C147/C147.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C148](C148/) | disproved | 360(d2 - 1)/(d1 - 1) is not always an integer | [full proof](C148/C148.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C149](C149/) | disproved | The C148 relation fails for a base-3 psp | [full proof](C149/C149.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C150](C150/) | disproved | 12 d1 (P - d2) divisibility fails | [full proof](C150/C150.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C151](C151/) | trivial or misstated | Carmichael numbers divisible by 8911 are 8911(198n + 1) | [full proof](C151/C151.lean) | new (immediate) | [elementary-proof](../methods/elementary-proof/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [C162](C162/) | proved | Infinitely many Poulet numbers (42m + 1)(42n + 1) | [full proof](C162/C162_mathlib.lean) | partly-known | [known-theorem](../methods/known-theorem/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C173](C173/) | disproved | Carmichael numbers divisible by 37 and 73 need not be 1 mod 10 | [full proof](C173/C173_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C174](C174/) | disproved | Carmichael numbers divisible by 37 and 73 need not have a factor 23 mod 30 | [full proof](C173/C173_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C179](C179/) | disproved | Carmichael numbers p^4 + 60p (duplicate of C116) | [full proof](C116/C116_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [reduction-to-constant](../methods/reduction-to-constant/README.md) |
| [C180](C180/) | disproved | Carmichael numbers in the classes 3, 17, 23, 27 mod 30 exist | [full proof](C180/C180_mathlib.lean) | known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [C183](C183/) | trivial or misstated | 2^k p n + p^2 for one factor implies all (trivial) | [full proof](C183/C183.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [C184](C184/) | trivial or misstated | P - 5 is a sum of distinct powers of 2 (trivial) | [full proof](C184/C184_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [C188](C188/) | disproved | Carmichael numbers pq + q - p (duplicate of C123) | [full proof](C123/C123_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C190](C190/) | disproved | 2823 is not a sum of three squares | [full proof](C190/C190.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C194](C194/) | trivial or misstated | x(P1 - 1) = y(P2 - 1) has other solutions (trivial) | [full proof](C194/C194.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [C195](C195/) | disproved | Poulet numbers as m + n + q with primes in one class mod 30 | [full proof](C195/C195.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C196](C196/) | disproved | Poulet numbers as 2m + n with primes in one class mod 30 | [full proof](C195/C195.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [C200](C200/) | disproved | No Poulet numbers of the C200 shape for n = 3 | [full proof](C200/C200.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [P004](P004/) | disproved | Carmichael numbers 7\*13\*(18k+1) (restates C089) | [full proof](C089/C089_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P005](P005/) | trivial or misstated | Carmichael numbers 19\*37\*(18k+1) (restates C090) | [full proof](C090/C090.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [P008](P008/) | disproved | Carmichael numbers n(2n-1)(5n-4) and forms I/II (restates C091) | [full proof](C091/C091_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P015](P015/) | trivial or misstated | 2^C mod 560 for Carmichael numbers C | [full proof](P015/P015.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P016](P016/) | disproved | Carmichael numbers 1 mod 10, 12 or 14: fails | [full proof](P016/P016_mathlib.lean) | partly-known | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P018](P018/) | proved | Carmichael triples p(C1 - 1) - C2 = C3 | [full proof](P018/P018_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P022](P022/) | proved | Carmichael numbers 176n + 1 | [full proof](P022/P022_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P026](P026/) | disproved | P - 80n and P - 150n prime (restates C095, C096) | [full proof](C095/C095.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P038](P038/) | disproved | Carmichael 1800n^2 +- 840n +- prime (restates C099) | [full proof](C099/C099_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [P040](P040/) | proved | C^2 - 2C - 30k is never prime for C = 162401 | [full proof](P040/P040_mathlib.lean) | new (immediate) | [modular-obstruction](../methods/modular-obstruction/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P042](P042/) | proved | p(p+2) + C for twin primes (contains C101) | [full proof](C101/C101_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [P044](P044/) | proved | Carmichael numbers 561 + 272n | [full proof](P044/P044_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P045](P045/) | proved | Carmichael numbers C = n(C - 1) - p(p + 2) | [full proof](P045/P045.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P046](P046/) | trivial or misstated | Odd Poulet numbers (a^2 - b^2)/8 (restates C102) | [full proof](C102/C102.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [P047](P047/) | disproved | Digital root and prime factors (restates C103) | [full proof](C103/C103_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P051](P051/) | disproved | C = n(n+p)/8 and three related conjectures | [full proof](C108/C108_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P052](P052/) | trivial or misstated | C = n(n+a)/(a+1) (restates C112) | [full proof](C112/C112.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [P055](P055/) | disproved | Carmichael numbers p^4 + 60p (restates C116) | [full proof](C116/C116_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [reduction-to-constant](../methods/reduction-to-constant/README.md) |
| [P062](P062/) | proved | Prime triples p, p + C1 - 1, p + C2 - 1 summing to a Carmichael number | [full proof](P062/P062_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P064](P064/) | disproved | C = pq + q - p (restates C123) | [full proof](C123/C123_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P065](P065/) | disproved | C = p(q - 2^n) and 5p + 2^n (C124 and C125) | [full proof](C125/C125.lean) | partly-known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [covering-congruences](../methods/covering-congruences/README.md) |
| [P066](P066/) | disproved | (P + 5^m) prime conjectures for Poulet numbers | [full proof](P066/P066_mathlib.lean) | new | [covering-congruences](../methods/covering-congruences/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [P068](P068/) | proved | Poulet numbers with P1 + P2 - 1 Poulet | [full proof](P068/P068.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P069](P069/) | proved | Poulet numbers with P1 + rev(P2) - 2 Poulet | [full proof](P069/P069.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P078](P078/) | disproved | Primes (n + d^k)/d (restates C136) | [full proof](C136/C136.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P080](P080/) | proved | Four conjectures on primes from Poulet numbers and primes (C137-C140) | [full proof](C137/C137.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [P085](P085/) | disproved | Five divisibility conjectures for 2- and 3-Poulet numbers (C146-C150) | [full proof](C146/C146.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P089](P089/) | trivial or misstated | Carmichael multiples of 8911 (restates C151) | [full proof](C151/C151.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [elementary-proof](../methods/elementary-proof/README.md) |
| [P103](P103/) | proved | Poulet numbers (42m+1)(42n+1) (restates C162) | [full proof](C162/C162_mathlib.lean) | partly-known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [known-theorem](../methods/known-theorem/README.md) |
| [P115](P115/) | disproved | Carmichael numbers divisible by 37 and 73 (C173, C174) | [full proof](C173/C173_mathlib.lean) | known | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P122](P122/) | proved | Carmichael and Poulet numbers p + q + r with primes in one class | [full proof](P122/P122_mathlib.lean) | new (immediate) | [explicit-counterexample](../methods/explicit-counterexample/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [P128](P128/) | disproved | C versus d^4; Carmichael numbers p^4 + 60p (contains C116) | [full proof](C116/C116_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [reduction-to-constant](../methods/reduction-to-constant/README.md) |
| [P132](P132/) | trivial or misstated | 2^k p n + p^2 representation (restates C183) | [full proof](C183/C183.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [P133](P133/) | trivial or misstated | P - 5 as a sum of powers of 2 (restates C184) | [full proof](P133/P133_mathlib.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |
| [P145](P145/) | disproved | C = pq + q - p (restates C188 = C123) | [full proof](C123/C123_mathlib.lean) | new | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [explicit-counterexample](../methods/explicit-counterexample/README.md) |
| [P147](P147/) | disproved | C = a^2 + b^2 + c^2 - 2 (restates C190) | [full proof](C190/C190.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md), [modular-obstruction](../methods/modular-obstruction/README.md) |
| [P150](P150/) | trivial or misstated | x(P1 - 1) = y(P2 - 1) (restates C194) | [full proof](C194/C194.lean) | new (immediate) | [restatement-or-misstatement](../methods/restatement-or-misstatement/README.md) |

## Answered in the literature; written up or confirmed here

| Problem | Verdict | Result | Lean | Prior art | Method |
|---|---|---|---|---|---|
| [P126](P126/) | answered | Poulet numbers P = (d^2 + d)/2 with d a prime factor of P | [full proof](P126/P126_mathlib.lean) | known | [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |
| [P127](P127/) | answered | Poulet numbers P2 = 2\*P1 - 1 with P1 Poulet | [full proof](P127/P127_mathlib.lean) | known | [finite-witness-counterexample](../methods/finite-witness-counterexample/README.md), [complete-table-scan](../methods/complete-table-scan/README.md) |

## Short proofs

Copied from each problem README (source paraphrase, result, argument).

### [C003](C003/): (n^(nk+k+n-1) - 1)/(n^2 - 1) is a base-n psp for infinitely many k

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 3. Paraphrase: For every integer n > 1 the expression (n^(nk+k+n-1) - 1)/(n^2 - 1) is a Fermat pseudoprime to base n for infinitely many k.

**Result.** True.

**Argument.** nk + k + n - 1 = (n+1)(k+1) - 2. Take a prime p with p = -1 (mod n+1), p not dividing n(n^2 - 1), and
k = 2(p+1)/(n+1) - 1 (a positive integer once p > n). Then the exponent is 2p and the number is
N = (n^(2p) - 1)/(n^2 - 1). Cipolla (1904): for a prime p not dividing n(n^2 - 1), N is composite
(N = ((n^p - 1)/(n - 1)) * ((n^p + 1)/(n + 1))) and n^(N-1) = 1 (mod N). Dirichlet gives infinitely many
such p (only the residue -1 mod n+1 is needed).

Lean: [full proof](C003/C003_mathlib.lean).

### [C004](C004/): 3-Poulet numbers without a factor 23 mod 30 are not all of the stated shape

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 4. Paraphrase: Every 3-Poulet number with no prime factor = 23 (mod 30) can be written p((n+1)p - n)((m+1)p - m) or p(np - (n+1))(mp - (m+1)).

**Reading.** The printed formula collapses to p^3 (it reads (n+1)*p - n*p); the evident intent, matching the scan,
is P = p * X * Y with p a prime factor and X, Y both n(p-1) + p (n >= 0) or both n(p-1) - 1 (n >= 1),
i.e. X, Y both = 1 or both = -1 modulo p - 1.

**Result.** False. Counterexample 158369 = 29 * 43 * 127.

**Argument.** 158369 is a base-2 psp; its factors are 29, 13, 7 (mod 30). For p = 29, 43, 127 the cofactor
5461, 3683, 1247 has no factorization X * Y of the required kind (bounded divisor search). Below 1e13
there are 8344 such failures (the scan reported 8357, likely counting the few data entries above 1e13).

Lean: [full proof](C004/C004.lean).

### [C006](C006/): Poulet numbers p^2 + 81p + 3pq with p = 30k+13, q = 30k+41: only two

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 6. Paraphrase: There are infinitely many Poulet numbers p^2 + 81p + 3pq with p = 30k + 13 and q = 30k + 41 prime.

**Reading.** The same k is used for p and q (both of Coman's examples, (13, 41) and (43, 71), use one k), so q = p + 28.
With independent k the question stays open; this item does not address that reading.

**Result.** False under the same-k reading: the only such Poulet numbers are 2821 and 14491.

**Argument.** With q = p + 28, N = p(4p + 165) and N - 1 = (p-1)(4p + 169) + 168. Since p | N and 2^(N-1) = 1 (mod p),
ord_p(2) divides both p - 1 and N - 1, hence 168, so p | 2^168 - 1. Among the 17 prime factors of
2^168 - 1 only 13 and 43 are 13 mod 30; both give Poulet numbers (2821, 14491). Brute force over p < 10^6
agrees.

Lean: [full proof](C006/C006_mathlib.lean).

### [C011](C011/): No 3-Carmichael (6x+1)(6y+1)(6z-1): true part and false part

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 11. Paraphrase: No Carmichael number with three prime factors has the shape (6x+1)(6y+1)(6z-1); all are (+,+,+), (-,-,-) or (+,-,-) modulo 6.

**Result.** Misstated. The 'no (+,+,-)' part is true and short; the 'all are of these shapes' part fails for 561 = 3 * 11 * 17.

**Argument.** A prime factor p = 1 (mod 6) gives 6 | p - 1 | C - 1 (Korselt), so C = 1 (mod 6), while
(6x+1)(6y+1)(6z-1) = 5 (mod 6). The factor 3 of 561 is neither 1 nor 5 mod 6. Below 1e10 the 3-Carmichael
numbers have factor patterns (1,1,1), (1,5,5), (5,5,5) and only 561 has (3,5,5).

Lean: [full proof](C011/C011_mathlib.lean).

### [C012](C012/): Digit-sum relations for Carmichael numbers with all factors 6k+1

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 12. Paraphrase: Every Carmichael number C with all prime factors = 1 (mod 6) satisfies one of: (1) C is Harshad; (2) n s(C) - n + 1 divides C for some integer n; (3) s((C+1)/2) divides C; (4) n s((C+1)/2) - n + 1 divides C; (5) s(C) = s((C+1)/2) (s = digit sum).

**Reading.** n = 0 in (2) or (4) gives the divisor 1 and makes the conjecture empty, so n != 0 (n of either sign).

**Result.** False. Counterexample 405739681 = 229 * 457 * 3877.

**Argument.** s(C) = 43, s((C+1)/2) = 40. 43 and 40 do not divide C. A divisor |n*42 + 1| (resp. |n*39 + 1|) with n != 0
is a divisor > 1 that is +-1 modulo 42 (resp. 39); none of the 7 divisors > 1 of C is.

Lean: [full proof](C012/C012_mathlib.lean).

### [C013](C013/): (30n+7)(60n+13)(150n+31) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 13. Paraphrase: The number (30n+7)(60n+13)(150n+31) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 30n+6: t+1, 2t+1, 5t+1; C - 1 = t(10t^2 + 17t + 8); 2t | C - 1 as t is even, 5t | C - 1 as t = 1 (mod 5). So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

Lean: [full proof](C013/C013_mathlib.lean).

### [C014](C014/): (30n-29)(60n-59)(90n-89)(180n-179) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 14. Paraphrase: The number (30n-29)(60n-59)(90n-89)(180n-179) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: u = 30(n-1): u+1, 2u+1, 3u+1, 6u+1; C - 1 = u(36u^3 + 72u^2 + 47u + 12), divisible by 6u as 6 | u. So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

Lean: [full proof](C014/C014_mathlib.lean).

### [C015](C015/): (330n+7)(660n+13)(990n+19)(1980n+37) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 15. Paraphrase: The number (330n+7)(660n+13)(990n+19)(1980n+37) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 330n+6: t+1, 2t+1, 3t+1, 6t+1; same expansion as C014, 6 | t. So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

Lean: [full proof](C015/C015_mathlib.lean).

### [C016](C016/): (30n-7)(90n-23)(300n-79) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 16. Paraphrase: The number (30n-7)(90n-23)(300n-79) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 30n-8: t+1, 3t+1, 10t+1; C - 1 = t(30t^2 + 43t + 14), t = 1 (mod 3) and t = 2 (mod 10). So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

Lean: [full proof](C016/C016_mathlib.lean).

### [C017](C017/): (30n+13)(90n+37)(150n+61) is Carmichael when all factors are prime

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 17. Paraphrase: The number (30n+13)(90n+37)(150n+61) is a Carmichael number whenever its factors are all prime.

**Result.** True.

**Argument.** Chernick-type form: t = 30n+12: t+1, 3t+1, 5t+1; C - 1 = t(15t^2 + 23t + 9), t = 0 (mod 3) and t = 2 (mod 5). So every factor minus 1 divides C - 1 for every n, and Korselt's criterion applies when the factors are distinct primes. (Numerically: Korselt divisibility for n < 5000; examples listed by the check.)

Lean: [full proof](C017/C017_mathlib.lean).

### [C019](C019/): 3-Carmichael factor pattern d1(n+1) - n fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 19. Paraphrase: For every 3-Carmichael number d1 d2 d3 (d1 < d2 < d3) either d2 and d3 are both d1(n+1) - n, or both d1 n - (n+1) (n natural).

**Result.** False. Counterexample 162401 = 17 * 41 * 233 (41 = 233 = 9 mod 16). 637 failures below 1e13.

**Argument.** The two patterns say d2, d3 = 1 or -1 modulo d1 - 1; 41 is 9 mod 16.

Lean: [full proof](C019/C019_mathlib.lean).

### [C021](C021/): p(2p+1) - 2kp is a base-(p+1) psp: true for odd p, false for p = 2

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 21. Paraphrase: If p and 2p + 1 are prime, then p(2p+1) - 2kp is a Fermat pseudoprime to base p + 1 for some natural k.

**Result.** True for every odd p (k = (p-1)/2, n = p(p+2)); false for p = 2.

**Argument.** For odd p, k = (p-1)/2 gives n = p(p+2). The base p + 1 is 1 mod p and -1 mod p + 2, and n - 1 is even,
so (p+1)^(n-1) = 1 modulo p and modulo p + 2, hence modulo n (coprime). Primality of 2p + 1 is not
needed. For p = 2 (2 and 5 prime) the candidates are n = 10, 6, 2 (k = 0, 1, 2): 3^9 = 3 (mod 10),
3^5 = 3 (mod 6), and 2 is prime, so no k works.

Lean: [full proof](C021/C021.lean).

### [C022](C022/): p(2p-1) - 2kp is a base-(p-1) psp

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 22. Paraphrase: If p and 2p - 1 are prime and p > 3, then p(2p-1) - 2kp is a Fermat pseudoprime to base p - 1 for some natural k.

**Result.** True.

**Argument.** k = (p+1)/2 gives n = p(p-2), composite. p - 1 is -1 mod p and 1 mod p - 2, n - 1 is even, so (p-1)^(n-1) = 1 mod p and mod p - 2, hence mod n. Only p odd, p >= 5 is used.

Lean: [full proof](C022/C022.lean).

### [C023](C023/): pq psp base p+1 when q^2 = 2p - 1: fails at (5, 3)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 23. Paraphrase: If p, q are prime and q^2 = 2p - 1, then pq is a Fermat pseudoprime to base p + 1.

**Result.** False: (p, q) = (5, 3) gives 15 and 6^14 = 6 (mod 15). True for every other pair.

**Argument.** Modulo p the base is 1. Modulo q: pq - 1 = p(q-1) + (p - 1) and p - 1 = (q-1)(q+1)/2, so q - 1 | pq - 1
and Fermat gives (p+1)^(pq-1) = 1 provided q does not divide p + 1 = (q^2 + 3)/2, i.e. q != 3.
For q = 3, p = 5: gcd(6, 15) = 3 and 6^k = 6 (mod 15).

Lean: [full proof](C023/C023_mathlib.lean).

### [C024](C024/): p(kp - k + 1) is not always a psp to bases kp - k and kp - k + 2

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 24. Paraphrase: For prime p > 3 and k > 1, n = p(kp - k + 1) is a Fermat pseudoprime to both bases kp - k and kp - k + 2.

**Result.** False: p = 5, k = 2 gives n = 45 and 10^44 = 10 (mod 45); p = 5, k = 5 gives n = 105 and 20^104 = 85 (mod 105).

**Argument.** A base sharing the factor p with n cannot satisfy b^(n-1) = 1. The bases are -k and 2 - k mod p, and
kp - k + 1 = 1 - k mod p; for p < 60, k < 30 the claim fails exactly when k = 0, 1 or 2 (mod p)
(the scan's 'true when p does not divide k' is incomplete; the claim is false either way).

Lean: [full proof](C024/C024.lean).

### [C025](C025/): Not every prime is (Cq - 1)/(q - 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 25. Paraphrase: Every prime p can be written (Cq - 1)/(q - 1) with C a Carmichael number and q prime.

**Result.** False: no prime below 561 (e.g. p = 2) has this form.

**Argument.** (Cq - 1)/(q - 1) = C + (C - 1)/(q - 1) >= C >= 561, the least Carmichael number.

Lean: [full proof](C025/C025.lean).

### [C026](C026/): 360ab + 1 = c^2 does not give Carmichael multiples of ab

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 26. Paraphrase: If a, b are prime and 360ab + 1 = c^2 with c prime, then infinitely many Carmichael numbers have the form abd.

**Result.** False: (a, b, c) = (2, 7, 71) and (3, 67, 269) satisfy the hypothesis and no Carmichael number is divisible by 14 or by 201.

**Argument.** Carmichael numbers are odd, so 14 never divides one. If 201 = 3 * 67 divides a Carmichael number C, then
C is odd, so 2^(C-1) = 1 (mod 67); ord_67(2) = 66 gives 66 | C - 1, so 3 | C - 1, contradicting 3 | C.
More generally a, b = 90a + 1, c = 180a + 1 all prime gives 360ab + 1 = c^2 and a | b - 1 blocks every
Carmichael multiple (a = 3, 13, 17, 31, 37, 47, ...). With a, b odd, distinct and neither dividing the
other minus one, Larsen's theorem gives infinitely many Carmichael multiples (corrected form; see the
scan note).

Lean: [full proof](C026/C026.lean).

### [C027](C027/): n^E = n (mod 544) fails for the Euler pseudoprime 561

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 27. Paraphrase: n^E = n (mod 544) for every natural n and every Euler pseudoprime E.

**Result.** False: n = 2, E = 561 gives 2^561 = 512 (mod 544).

**Argument.** 561 is composite and 2^280 = 1 (mod 561), equal to the Jacobi symbol (2/561) = 1 (561 = 1 mod 8), so 561 is an Euler pseudoprime to base 2.

Lean: [full proof](C027/C027_mathlib.lean).

### [C029](C029/): Poulet p2 = (p1 - d)n + d fails for 561 and 341

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 29. Paraphrase: If a Poulet number p2 is divisible by d and a smaller 2-Poulet number p1 is divisible by d, then p2 = (p1 - d)n + d for a natural n.

**Result.** False: p2 = 561, d = 11, p1 = 341 = 11 * 31; 561 mod 330 = 231, not 11.

**Argument.** Direct computation.

Lean: [full proof](C029/C029.lean).

### [C031](C031/): Poulet numbers with three or more factors: P = q((r+1)q - r) fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 31. Paraphrase: Every Poulet number with at least three prime factors has a prime factor q with P = q((r+1)q - r), r natural.

**Result.** False: 617093 = 43 * 113 * 127. 3352 failures below 1e13.

**Argument.** P/q must be r(q-1) + q, i.e. = 1 mod q - 1 and >= q; P/q mod (q-1) is 29, 85, 71 for q = 43, 113, 127.

Lean: [full proof](C031/C031.lean).

### [C032](C032/): Exceptions are not only 5461(42k - 13)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 32. Paraphrase: The Poulet numbers divisible by a smaller Poulet number and not of the form p((m+1)p - m)((n+1)p - n) are exactly multiples 5461(42k - 13).

**Reading.** p is taken to be a prime factor of the Poulet number (for 3048841, with three prime factors, any factorization into three factors >= 2 uses the three primes, so nothing changes).

**Result.** False: 3048841 = 61 * 151 * 331 is divisible by the Poulet number 49981 = 151 * 331, is not of the form, and is not a multiple of 5461.

**Argument.** For p = 61 the cofactors are 31 mod 60; for p = 151 and 331 the cofactor 61 is not 1 mod p - 1.

Lean: [full proof](C032/C032_mathlib.lean).

### [C035](C035/): P = 8pn + p^2 for one prime factor implies all (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 35. Paraphrase: If a Poulet number is 8pn + p^2 for one of its prime factors p (n an integer), then the same holds for every prime factor.

**Result.** True and trivial: the condition is P = 1 (mod 8), independent of p.

**Argument.** P = pm. 8pn + p^2 = P with n an integer means m = p (mod 8). For odd p, multiplying by p (p^2 = 1 mod 8) turns this into P = 1 (mod 8), and back.

Lean: [full proof](C035/C035.lean).

### [C037](C037/): Infinitely many Poulet numbers (n+1)p^2 - np with p Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 37. Paraphrase: There are infinitely many Poulet numbers (n+1)p^2 - np, n >= 1, with p a Poulet number.

**Result.** True (via Larsen 2025).

**Argument.** (n+1)561^2 - 561n = 561 + 314160(n + 1), so the Poulet numbers of this shape with p = 561 are exactly
those N = 561 (mod 314160 = 561 * 560) with N > 561^2. The progression contains the Carmichael number 561
(and is Carmichael compatible: g = 561, lambda(561) = 80 | 560), so by Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025), Theorem 1 it contains infinitely many
Carmichael numbers, all Poulet. Below 1e13: 10054063041, 709277461761, 795066389601, 7650392590401.

Lean: [witness](C037/C037.lean).

### [C042](C042/): Carmichael numbers divisible by p and 2p - 1 (true, short)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 42. Paraphrase: A Carmichael number divisible by primes p and 2p - 1 equals p(2p-1)(n(2p-2) + p).

**Result.** True (trivial given Korselt).

**Argument.** Korselt: 2p - 2 | C - 1. With C = p(2p-1)m and 2p - 1 = 1, p^2 = 1 modulo 2(p-1) (p odd; p = 2 is impossible
since C is odd), pm = 1, so m = p (mod 2p - 2); the least positive such m is p, so m = n(2p-2) + p, n >= 0.
No failure among 3480 cases below 1e13.

Lean: [full proof](C042/C042_mathlib.lean).

### [C044](C044/): Carmichael numbers (30a+1)(30b+1)(30c+11) do exist

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 44. Paraphrase: Every Carmichael number = 1 (mod 10) with all prime factors = 1 (mod 10) (with any number of prime factors) is (30a+1)(30b+1)(30c+1), (30a+11)(30b+11)(30c+11) or (30a+1)(30b+11)(30c+11); in particular none is (30a+1)(30b+1)(30c+11).

**Reading.** The statement explicitly covers Carmichael numbers with more than three prime factors, so the three
factors are products of primes. If the factors had to be prime the claim would be true: a prime factor
= 1 (mod 30) forces C = 1 (mod 3), while (1)(1)(11) = 2 (mod 3).

**Result.** False as stated: 1044430736441 = 41 * 191 * 281 * 521 * 911 = (41*191)(281*521)(911) = 7831 * 146401 * 911, residues 1, 1, 11 mod 30.

**Argument.** All five primes are 11 mod 30 and 11^2 = 1 (mod 30). Below 1e13 there are 30 Carmichael numbers = 11 (mod 30)
with all prime factors = 1 (mod 10); all their prime factors are 11 mod 30; the 3-factor ones (e.g. 1909001)
fit (1)(1)(11) only with a = 0, the 5-factor ones (1044430736441, 1894509409001, 3558903712001) with
a, b >= 1.

Lean: [full proof](C044/C044_mathlib.lean).

### [C045](C045/): Three-term APs of Carmichael numbers without divisibility

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 45. Paraphrase: C1 = (C2 + C3)/2 with Carmichael C1, C2, C3 only if C2 divides both C1 and C3.

**Result.** False: 29341 + 63973 = 2 * 46657. 798 of the 871 three-term APs below 1e13 violate it.

**Argument.** 46657 is divisible by neither 29341 nor 63973.

Lean: [full proof](C045/C045_mathlib.lean).

### [C050](C050/): Infinitely many base-3 psp (3^(4k+2) - 1)/8

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 50. Paraphrase: There are infinitely many base-3 Fermat pseudoprimes (3^(4k+2) - 1)/8.

**Result.** True.

**Argument.** (3^(4k+2) - 1)/8 = (9^p - 1)/(9 - 1) with p = 2k + 1. Cipolla's theorem with a = 3: for prime p not dividing 3 * 8, i.e. p >= 5, this is a base-3 psp.

Lean: [full proof](C050/C050_mathlib.lean).

### [C051](C051/): Poulet numbers divisible by 23 and 67 are 23*67*(66n + 23)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 51. Paraphrase: Every Poulet number divisible by 23 and 67 is 23*67*(n(67-1) + 23) with n >= 1 (also given as a polynomial in p = 23).

**Result.** True.

**Argument.** ord_67(2) = 66, so 66 | P - 1. With P = 1541m and 1541 = 23 (mod 66), 23^2 = 1 (mod 66) gives m = 23 (mod 66).
m = 23 would give P = 35443, which is not a psp (23^2 | P would need 23 to be a Wieferich prime). All 1249 cases
below 1e13 fit.

Lean: [full proof](C051/C051.lean).

### [C054](C054/): Poulet numbers divisible by 11 and 61 are 11*61*(60n + 11)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 54. Paraphrase: Every Poulet number divisible by 11 and 61 is 11*61*(n(61-1) + 11) with n >= 1 (also given as a polynomial in p = 11).

**Result.** True.

**Argument.** ord_61(2) = 60, so 60 | P - 1. With P = 671m and 671 = 11 (mod 60), 11^2 = 1 (mod 60) gives m = 11 (mod 60).
m = 11 would give P = 7381, which is not a psp (11^2 | P would need 11 to be a Wieferich prime). All 2718 cases
below 1e13 fit.

Lean: [full proof](C054/C054.lean).

### [C055](C055/): The C054 shape fails for p = 30k + 11, q = 180k + 61

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 55. Paraphrase: Every Poulet number with prime factors p = 30k + 11 and q = 180k + 61 is 6p^3(6n+1) - p^2(66n+5) + 30pn, n >= 1.

**Result.** False: 30411201 = 3 * 101 * 167 * 601 (k = 3).

**Argument.** The polynomial is pq(n(q-1) + p) = 60701(600n + 101) for p = 101; its values for n >= 1 start at 42551401 > 30411201.

Lean: [full proof](C055/C055.lean).

### [C058](C058/): 2-Poulet numbers (q 2^a 3^b 5^c +- 1) 2^n + 1 fail

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 58. Paraphrase: Every 2-Poulet number is (q 2^a 3^b 5^c +- 1) 2^n + 1 with n >= 1, a, b, c >= 0 and q a prime, a prime square or a semiprime.

**Result.** False: 514447 = 359 * 1433.

**Argument.** 514446 = 2 * 257223 forces n = 1. Then q 2^a 3^b 5^c = 257222 = 2 * 7 * 19 * 967 or 257224 = 2^3 * 11 * 37 * 79; in both the part prime to 30 has three prime factors, so q has at least three.

Lean: [full proof](C058/C058_mathlib.lean).

### [C076](C076/): Infinitely many Poulet numbers divisible by 15 with SCD1 beginning 2, 4, 7

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 76. Paraphrase: There are infinitely many Poulet numbers divisible by 15 whose set of Smarandache-Coman divisors of order 1 is {2, 4, 7, n1, ..., ni} with i > 0.

**Reading.** SCD1(n) = (S(d1 - 1), ..., S(dm - 1)) over the prime factors d1 < ... < dm, S the Kempner (Smarandache) function, listed in factor order (Coman's definition, Part two, article 24).

**Result.** True (via Larsen 2025).

**Argument.** Members of the progression 342075735 (mod 3234846615 = 435 * 7 * 11 * 13 * 17 * 19 * 23) are divisible by 3, 5 and the third prime, and = 1 modulo every
prime in between, so (being odd when Carmichael) their three least prime factors are 3, 5 and that prime;
S(2) = 2, S(4) = 4, S(28) = 7. A Carmichael number has at least three prime factors and 3*5*p alone is not in the progression,
so i > 0. The progression is Carmichael compatible in Larsen's sense (g = gcd, h = gcd(lambda(g), M) divides
a - 1, 36 does not divide M), so by Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025), Theorem 1 it contains infinitely many Carmichael numbers.

Lean: [witness](C076/C076.lean).

### [C077](C077/): Infinitely many Poulet numbers divisible by 15 with SCD1 beginning 2, 4, 23

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 77. Paraphrase: There are infinitely many Poulet numbers divisible by 15 whose set of Smarandache-Coman divisors of order 1 is {2, 4, 23, n1, ..., ni} with i > 0.

**Reading.** SCD1(n) = (S(d1 - 1), ..., S(dm - 1)) over the prime factors d1 < ... < dm, S the Kempner (Smarandache) function, listed in factor order (Coman's definition, Part two, article 24).

**Result.** True (via Larsen 2025).

**Argument.** Members of the progression 93323697499246215 (mod 307444891294245705 = 705 * (7 * 11 * ... * 43)) are divisible by 3, 5 and the third prime, and = 1 modulo every
prime in between, so (being odd when Carmichael) their three least prime factors are 3, 5 and that prime;
S(2) = 2, S(4) = 4, S(46) = 23. A Carmichael number has at least three prime factors and 3*5*p alone is not in the progression,
so i > 0. The progression is Carmichael compatible in Larsen's sense (g = gcd, h = gcd(lambda(g), M) divides
a - 1, 36 does not divide M), so by Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025), Theorem 1 it contains infinitely many Carmichael numbers.

Lean: [witness](C077/C077.lean).

### [C086](C086/): The twin pair (3, 5) does not arise from a 2-Poulet number

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 86. Paraphrase: For every twin prime pair (q1, q2) there is a 2-Poulet number p1 p2 with q1 = p2 - p1 - 1, q2 = p2 - p1 + 1.

**Result.** False for (3, 5): no 2-Poulet number has p2 - p1 = 4.

**Argument.** For P = p(p+4): P - 1 = 4 (mod p - 1) and P - 1 = -4 (mod p + 3). Fermat gives ord_{p_i}(2) | gcd(p_i - 1, P - 1) | 4, so both primes divide 15 = 2^4 - 1, impossible for two primes 4 apart. (None below 1e13.)

Lean: [full proof](C086/C086_mathlib.lean).

### [C088](C088/): Only two 2-Poulet numbers with p2 - p1 = 84

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 88. Paraphrase: There are infinitely many 2-Poulet numbers p1 p2 with p2 - p1 = 84.

**Result.** False: the only ones are 3277 = 29 * 113 and 5461 = 43 * 127.

**Argument.** As in C086, ord(2) divides 84 for both primes, so both divide 2^84 - 1 = 3^2 * 5 * 7^2 * 13 * 29 * 43 * 113 * 127 * 337 * 1429 * 5419 * 14449; the pairs 84 apart are (29, 113) and (43, 127), both Poulet.

Lean: [full proof](C088/C088_mathlib.lean).

### [C089](C089/): Carmichael numbers divisible by 7 and 13: cofactor not always 1 or 13 mod 18

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 89. Paraphrase: Every Carmichael number divisible by 7 and 13 is 91(18k + 1) or 91(18k + 13).

**Result.** False: 9890881 = 7 * 11 * 13 * 41 * 241, cofactor 108691 = 7 (mod 18). 62 failures below 1e13.

**Argument.** Direct computation.

Lean: [full proof](C089/C089_mathlib.lean).

### [C090](C090/): Carmichael numbers divisible by 19 and 37 are 703(18k + 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 90. Paraphrase: Every Carmichael number divisible by 19 and 37 is 703(18k + 1).

**Result.** True (short). In fact the cofactor is 19 (mod 36).

**Argument.** C is odd, so 2^(C-1) = 1 (mod 37) and ord_37(2) = 36 gives 36 | C - 1. 703 = 19 (mod 36) and 19^2 = 1 (mod 36), so C/703 = 19 (mod 36), hence 1 (mod 18). All 701 cases below 1e13 fit.

Lean: [full proof](C090/C090.lean).

### [C091](C091/): Carmichael numbers n(a(n-1)+1)(b(n-1)+1): fails for 162401

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 91. Paraphrase: Every Carmichael number is n(an - a + 1)(bn - b + 1) or n(an - a - 1)(bn - b - 1) with n its least prime factor and a, b natural.

**Reading.** a, b >= 1. With a = 0 the first form always holds (C/n = 1 mod n - 1 by Korselt), which would make the statement empty.

**Result.** False: 162401 = 17 * 41 * 233.

**Argument.** The two other factors would be = 1 (resp. -1) mod 16 and >= 17 (resp. 15); the factor pairs of 9553 are (1, 9553) and (41, 233), and 41 = 9 (mod 16).

Lean: [full proof](C091/C091_mathlib.lean).

### [C095](C095/): P - 80n prime fails for 1105

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 95. Paraphrase: Every Poulet number P has n with P - 80n prime.

**Result.** False: 1105 = 65 (mod 80), so every 1105 - 80n is a multiple of 5 other than 5.

**Argument.** 1105 - 80n = 5 would need 80n = 1100.

Lean: [full proof](C095/C095.lean).

### [C096](C096/): P - 150n prime fails for 561

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 96. Paraphrase: Every Poulet number P has n with P - 150n prime.

**Result.** False: 561 = 111 (mod 150), so every 561 - 150n is a multiple of 3 other than 3.

**Argument.** 561 - 150n = 3 would need 150n = 558.

Lean: [full proof](C096/C096.lean).

### [C099](C099/): Carmichael 1800n^2 +- 840n +- prime: residue obstruction

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 99. Paraphrase: Every Carmichael number C = 1 (mod 10) not divisible by 3 is 1800n^2 + 840n + p (p prime, 1 mod 30) or 1800n^2 - 840n - q (q prime, 29 mod 30).

**Result.** False: both shapes are 1 (mod 30); 162401 = 11 (mod 30).

**Argument.** 1800 and 840 are multiples of 30; p = 1 and -q = 1 (mod 30).

Lean: [full proof](C099/C099_mathlib.lean).

### [C101](C101/): p(p+2) + 1729 for twin primes: prime factors 2, 3 and 1, 7, 13, 19 mod 30

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 101. Paraphrase: For twin primes p, p + 2, the number p(p+2) + 1729 has only the prime factors 2, 3 and primes = 1, 7, 13, 19 (mod 30).

**Result.** True.

**Argument.** For p > 3, p = 6j - 1 and p(p+2) + 1729 = 36(j^2 + 48). A prime r > 3 dividing j^2 + 48 = j^2 + 3*4^2 has
-3 a quadratic residue, so r = 1 (mod 3); r = 5 never divides j^2 + 48 (squares mod 5 are 0, 1, 4). The
primes = 1 (mod 6) prime to 5 are exactly 1, 7, 13, 19 (mod 30). p = 3: 1744 = 2^4 * 109, 109 = 19 (mod 30).
Checked numerically for p < 2e5.

Lean: [full proof](C101/C101_mathlib.lean).

### [C102](C102/): Odd Poulet numbers are (a^2 - b^2)/8 (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 102. Paraphrase: Every Poulet number ending in 1, 5 or 9 is (a^2 - b^2)/8 with a, b positive integers.

**Result.** True and trivial: a = 2P + 1, b = 2P - 1 works for every P >= 1.

**Argument.** (2P+1)^2 - (2P-1)^2 = 8P.

Lean: [full proof](C102/C102.lean).

### [C103](C103/): Digital root and prime factors of Carmichael numbers: fails for 62745

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 103. Paraphrase: If a Carmichael number C is not Harshad and its digital root s is not 1, then every prime factor d != 3 is n(s-1) +- 1 with n >= 1.

**Result.** False: 62745 = 3 * 5 * 47 * 89 (s = 6, d = 5). 79 failures (scan).

**Argument.** Digit sum 24 does not divide 62745; 5 = 5n +- 1 has no solution.

Lean: [full proof](C103/C103_mathlib.lean).

### [C108](C108/): Carmichael numbers n(n + p)/8 with p a prime power: fails for 162401

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 108. Paraphrase: Every Carmichael number is n(n + p)/8 with n >= 1 and p a prime or a prime power.

**Result.** False: 162401. 363 of the first 3000 Carmichael numbers fail.

**Argument.** 8C = n(n + p) needs n | 8C and n < sqrt(8C); for each of the 16 such divisors the cofactor 8C/n - n has two distinct prime factors.

Lean: [full proof](C108/C108_mathlib.lean).

### [C112](C112/): Carmichael numbers n(n + a)/(a + 1) (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 112. Paraphrase: Every Carmichael number is n(n + a)/(a + 1) with n, a positive integers.

**Result.** True and trivial: n = C - 1, a = C^2 - 3C + 1 works for every C >= 3.

**Argument.** n(n + a) = (C-1)C(C-2) and a + 1 = (C-1)(C-2).

Lean: [full proof](C112/C112.lean).

### [C116](C116/): Only two Carmichael numbers p^4 + 60p

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 116. Paraphrase: There are infinitely many Carmichael numbers p^4 + 60p with p prime (2821 and 29341 for p = 7, 13).

**Result.** False: these two are the only ones.

**Argument.** p | C, so Korselt gives p - 1 | C - 1 = (p-1)(p^3 + p^2 + p + 61) + 60, i.e. p - 1 | 60: p in {2, 3, 5, 7, 11, 13, 31, 61}. Only p = 7, 13 give Carmichael numbers.

Lean: [full proof](C116/C116_mathlib.lean).

### [C123](C123/): Carmichael numbers pq + q - p: fails for 1024651

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 123. Paraphrase: Every Carmichael number is pq + q - p with p, q primes.

**Result.** False: 1024651 = 19 * 199 * 271. 86 of the first 4000 Carmichael numbers fail.

**Argument.** C - 1 = (p+1)(q-1); for each divisor d of 1024650, d - 1 or 1024650/d + 1 is composite.

Lean: [full proof](C123/C123_mathlib.lean).

### [C124](C124/): 3-Carmichael numbers divisible by 5: p(q - 2^n) holds

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 124. Paraphrase: Every 3-Carmichael number C divisible by 5 is p(q - 2^n) with p a prime factor other than 5, q prime, n >= 1.

**Result.** True: the only 3-Carmichael numbers divisible by 5 are 1105, 2465, 10585, and 1105 = 13(89 - 2^2), 2465 = 17(149 - 2^2), 10585 = 29(367 - 2).

**Argument.** C = 5pq, p < q. Korselt: q - 1 | 5pq - 1 = 5p(q-1) + 5p - 1, so 5p - 1 = h(q-1) with h <= 4 (q - 1 >= p).
Then h(5q - 1) = 25(p-1) + 20 + 4h, and p - 1 | 5q - 1 gives p - 1 | 20 + 4h <= 36, so p <= 37. The finite
enumeration gives the three numbers (also the complete list in the data below 1e13).

Lean: [full proof](C124/C124_mathlib.lean).

### [C125](C125/): 5p + 2^n is not always prime infinitely often

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on
Fermat Pseudoprimes* (2013), Part one, conjecture 125. Paraphrase: for every odd prime
p ≠ 5 there are infinitely many n such that 5p + 2^n is prime.

**Result.** False. For the prime p = 76739471787787, 5p + 2^n is composite for every n ≥ 0.

**Argument.** Covering congruences. The nine primes q = 3, 7, 13, 17, 19, 37, 73, 109, 241
have ord_q(2) dividing 72, and p was chosen by the Chinese remainder theorem so that
q | 5p + 2^n on one class of n mod ord_q(2); the classes cover every residue mod 72.
Since 5p + 2^n > 241, each value has a proper factor.

Lean: [full proof](C125/C125_mathlib.lean).

### [C126](C126/): false (non-constructively, via Wright's theorem); P = 15709 settled at m = 749

**Source.** M. Coman, *Two hundred conjectures and one hundred and fifty open problems on Fermat pseudoprimes*
(2013), Conjecture 126 (also Open Problem 66, Conjecture 1): for every Poulet number P not divisible by 3 or 5
there are m, n >= 1 such that (P + 5^m)/6^n is a prime or a prime power (paraphrased). Examples given: 341
(m = 2, n = 1: 61), 1387 (m = 3, n = 3: 7), 1729 (m = 1, n = 1: 17^2).

**Reading.** 6^n must divide P + 5^m; since P is odd, this needs m odd when P = 1 (mod 3) and m even when
P = 2 (mod 3). The scan found three Poulet numbers with no m < 60: 13747, 14491, 15709.

**Result.** False, non-constructively. The same statement is part (1) of Coman's Open Problem 66; [COM/P066](P066/README.md) proves in Lean that for every P in an explicit coprime residue class modulo M = 197386120142055051194076523980 and all m, n with 6^n | P + 5^m, (P + 5^m)/6^n is not a prime power (covering argument). Wright's theorem (Bull. London Math. Soc. 45 (2013)) puts infinitely many Carmichael numbers, hence Poulet numbers prime to 15, in that class. No explicit counterexample P is known.

Data for the three small hard cases (kept from the first write-up): Partial. P = 15709: (15709 + 5^749)/6 is prime (523 digits), and no m <= 748 works. P = 13747 and
P = 14491: no m <= 4000 (any n) gives a prime or prime power. No covering set with moduli of lcm up to 10^6
exists for these two (about 15-21% of admissible m uncovered), so the conjecture is expected to hold but is not
reached.

**Argument.** Direct search: for each m, divide out 6 while possible and test every quotient for being a
probable prime or a perfect power of one (PARI ispseudoprime, ispower); certificate/c126.gp (m <= 600),
c126b.gp (m <= 4000). The m = 749 value is proved prime by an ECPP certificate (PARI primecert, validated by
primecertisvalid; certificate/cert15709.txt).

Lean: [full proof](P066/P066_mathlib.lean).

### [C127](C127/): (P + 5^m)/30 is composite or non-integral for every m, for infinitely many Poulet P with 5 | P, 3 ∤ P

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat
Pseudoprimes* (2013), Part one, conjecture 127. Paraphrase: every Poulet number P divisible by 5 and
not by 3 has some m >= 1 with (P + 5^m)/30 prime.

**Result.** False, non-constructively, if Larsen's preprint theorem holds. Every P = 19664845
(mod 50862630) makes (P + 5^m)/30 a non-integer for even m and composite for odd m, and this
progression contains infinitely many Carmichael numbers by D. Larsen, arXiv:2504.09056 (2025,
preprint, not refereed). No explicit P is known: no base-2 pseudoprime below 10^13 lies in the class.

**Argument.** The class is P = 0 (mod 5), 1 (mod 6), -5 (mod 31), -5^3 (mod 13), -5^5 (mod 7),
-5^9 (mod 601); M = 30 * 7 * 13 * 31 * 601 = 50862630.
- Even m: P = 1 and 5^m = 1 (mod 3), so 3 ∤ P + 5^m and (P + 5^m)/30 is not an integer.
- Odd m: 2, 3 and 5 divide P + 5^m. The orders of 5 are 3 mod 31, 4 mod 13, 6 mod 7 and 12 mod 601,
  so q | P + 5^m on m = 1 (mod 3) for 31, 3 (mod 4) for 13, 5 (mod 6) for 7, 9 (mod 12) for 601.
  The odd residues mod 12 are 1, 7 (31), 3, 11 (13), 5 (7) and 9 (601), so every odd m is covered.
  Each q is coprime to 30, so q divides (P + 5^m)/30, which is at least (19664845 + 5)/30 > 601.
- Poulet numbers in the class: gcd(19664845, M) = 5, lambda(5) = 4, h = gcd(4, M) = 2 divides
  19664845 - 1, gcd(5, 2 phi(5)) = 1, and 36 ∤ M, so the progression is Carmichael compatible in
  Larsen's sense (definition before his Theorem 1). His Theorem 1 gives infinitely many Carmichael
  numbers in it; Carmichael numbers are Poulet numbers, and these are divisible by 5 and not by 3.

Lean: [witness](C127/C127.lean).

### [C128](C128/): (P + 5^m)/10 is composite for every m, for infinitely many Poulet P with 15 | P

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 128. Paraphrase: Every Poulet number P divisible by 15 has m >= 1 with (P + 5^m)/10 prime.

**Result.** False (non-constructive): every odd P = 27334771482791460 (mod 76580312516934135) makes (P + 5^m)/10 composite for all m >= 1, and this progression contains infinitely many Carmichael numbers.

**Argument.** Covering: q | P + 5^m on the class m = r (mod ord_q(5)) for (q, ord, r) = (7, 6, 1), (13, 4, 0), (19, 9, 2),
(31, 3, 0), (37, 36, 26), (601, 12, 10), (829, 9, 5), (5167, 18, 17); the classes cover Z/36. The progression is
Carmichael compatible (gcd 15, lambda(15) = 4, h = gcd(4, M) = 1, M odd), so by Larsen, Carmichael numbers in all possible arithmetic progressions, arXiv:2504.09056 (2025), Theorem 1 it contains infinitely many
Carmichael numbers; they are Poulet numbers divisible by 15. No explicit P is known.

Lean: [witness](C128/C128.lean).

### [C136](C136/): Primes (n + d^k)/d: none for P = 561, d = 3

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 136. Paraphrase: For every Poulet number P = n + d with d a prime factor, there are infinitely many primes (n + d^k)/d.

**Result.** False: P = 561, d = 3 gives no prime at all.

**Argument.** (558 + 3^k)/3 = 186 + 3^(k-1): 187 = 11 * 17 for k = 1, a multiple of 3 above 3 for k >= 2. (Also no prime for (1105, 5), (1905, 5) for k < 12.)

Lean: [full proof](C136/C136.lean).

### [C137](C137/): Primes (P + n)/(n + 1) are bounded

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 137. Paraphrase: For every Poulet number P there are infinitely many primes (P + n)/(n + 1).

**Result.** False: the values are at most P.

**Argument.** P + n <= P(n + 1).

Lean: [full proof](C137/C137.lean).

### [C138](C138/): Primes p with p^2 = n(P - 1) + 1

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 138. Paraphrase: For every Poulet number P there are infinitely many primes p = sqrt(n(P-1) + 1), n >= 1.

**Result.** True.

**Argument.** Any prime p = 1 (mod P - 1), p > 1, works: p = (P-1)t + 1 gives p^2 = n(P-1) + 1 with n = t((P-1)t + 2). There are infinitely many such primes (Dirichlet; elementary for the residue 1).

Lean: [full proof](C138/C138_mathlib.lean).

### [C139](C139/): Primes (q^2 + n)/(n + 1) are bounded

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 139. Paraphrase: For every prime q there are infinitely many primes (q^2 + n)/(n + 1).

**Result.** False: the values are at most q^2.

**Argument.** q^2 + n <= q^2(n + 1).

Lean: [full proof](C139/C139.lean).

### [C140](C140/): Primes sqrt((q^2 + n)/(n + 1)) are bounded

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 140. Paraphrase: For every prime q there are infinitely many primes p with p^2 = (q^2 + n)/(n + 1).

**Result.** False: p <= q.

**Argument.** p^2 <= q^2.

Lean: [full proof](C140/C140.lean).

### [C146](C146/): 36(P - d) divisibility for 3-Poulet numbers fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 146. Paraphrase: For every 3-Poulet number P and each prime factor d: d^2 - d | 36(P - d) or P - d | 36(d^2 - d).

**Result.** False: 149281 = 11 * 41 * 331 (d = 331). 14029 failures below 1e13.

**Argument.** Direct computation.

Lean: [full proof](C146/C146.lean).

### [C147](C147/): 36(P - d) divisibility for 2-Poulet numbers fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 147. Paraphrase: As C146 for squarefree 2-Poulet numbers.

**Result.** False: 49981 = 151 * 331 (both d fail).

**Argument.** Direct computation.

Lean: [full proof](C147/C147.lean).

### [C148](C148/): 360(d2 - 1)/(d1 - 1) is not always an integer

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 148. Paraphrase: For a squarefree 2-Poulet number d1 d2, 360(P - d1)/(d1^2 - d1) = 360(d2^2 - d2)/(P - d2) is a natural number.

**Result.** False: with d1 < d2, 1678541 = 1013 * 1657; for either labeling, 3090091 = 1163 * 2657 (least such). 7157 of 123866 squarefree 2-Poulet numbers below 1e13 fail for both labelings.

**Argument.** Both sides equal 360(d2 - 1)/(d1 - 1). The scan's witness 1678541 passes with the labels swapped (360 * 1012/1656 = 220), so the label-free witness is 3090091.

Lean: [full proof](C148/C148.lean).

### [C149](C149/): The C148 relation fails for a base-3 psp

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 149. Paraphrase: As C148 for every two-factor squarefree Fermat pseudoprime to any base.

**Result.** False: 1241143 = 547 * 2269 is a base-3 psp and fails for either labeling.

**Argument.** Direct computation.

Lean: [full proof](C149/C149.lean).

### [C150](C150/): 12 d1 (P - d2) divisibility fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 150. Paraphrase: For a 3-Poulet number d1 d2 d3 (d1 < d2 < d3): d2^2 - d2 | 12 d1 (P - d2) or P - d3 | 12 d1 (d3^2 - d3).

**Result.** False: 711361 = 7 * 151 * 673.

**Argument.** Direct computation.

Lean: [full proof](C150/C150.lean).

### [C151](C151/): Carmichael numbers divisible by 8911 are 8911(198n + 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 151. Paraphrase: Every Carmichael number divisible by 8911 is 8911(198n + 1).

**Result.** True (short; holds for every Poulet number divisible by 8911).

**Argument.** ord_19(2) = 18 and ord_67(2) = 66 give 198 | C - 1; 8911 = 1 (mod 198). All 250 Poulet multiples of 8911 below 1e13 fit.

Lean: [full proof](C151/C151.lean).

### [C162](C162/): Infinitely many Poulet numbers (42m + 1)(42n + 1)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 162. Paraphrase: There are infinitely many Poulet numbers (42m + 1)(42n + 1).

**Result.** True.

**Argument.** For a prime p = 1 (mod 6), (4^p - 1)/3 = (2^p - 1)((2^p + 1)/3) is a Poulet number (Cipolla) and both factors are 1 (mod 42) (2^p = 2 mod 21 and mod 63); p = 7 gives 5461 = 127 * 43. Infinitely many primes = 1 (mod 6).

Lean: [full proof](C162/C162_mathlib.lean).

### [C173](C173/): Carmichael numbers divisible by 37 and 73 need not be 1 mod 10

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 173. Paraphrase: Every Carmichael number divisible by 37 and 73 is 1 (mod 10).

**Result.** False: 294409 = 37 * 73 * 109 = 9 (mod 10).

**Argument.** Direct computation.

Lean: [full proof](C173/C173_mathlib.lean).

### [C174](C174/): Carmichael numbers divisible by 37 and 73 need not have a factor 23 mod 30

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 174. Paraphrase: Every Carmichael number divisible by 37 and 73 has a prime factor = 23 (mod 30).

**Result.** False: 294409 = 37 * 73 * 109, factors 7, 13, 19 (mod 30).

**Argument.** Every prime divisor is 37, 73 or 109 (Euclid's lemma in the Lean file).

Lean: [full proof](C173/C173_mathlib.lean).

### [C179](C179/): Carmichael numbers p^4 + 60p (duplicate of C116)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 179. Paraphrase: Same as conjecture 116: infinitely many Carmichael numbers p^4 + 60p, p prime.

**Result.** False (see C116).

**Argument and evidence.** This item restates [COM-C116](C116/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C116/C116.lean`](C116/C116.lean).
Lean (Mathlib): [`C116_mathlib.lean`](C116/C116_mathlib.lean) (`C116_main, C116_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C116/C116_mathlib.lean).

### [C180](C180/): Carmichael numbers in the classes 3, 17, 23, 27 mod 30 exist

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 180. Paraphrase: No Carmichael number is 3, 17, 23 or 27 (mod 30).

**Result.** False: 330794193633 (3), 66243263297 (17), 1097343303233 (23), 28173681537 (27).

**Argument.** Direct computation.

Lean: [full proof](C180/C180_mathlib.lean).

### [C183](C183/): 2^k p n + p^2 for one factor implies all (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 183. Paraphrase: Apart from definable exceptions, if a Poulet number is 2^k p n + p^2 (k >= 0, n an integer) for one prime factor p, then it is 2^k q m + q^2 for every other prime factor q.

**Result.** True and trivial: k = 0 works for every factor (n = P/p - p).

**Argument.** P = p(P/p) = p(P/p - p) + p^2.

Lean: [full proof](C183/C183.lean).

### [C184](C184/): P - 5 is a sum of distinct powers of 2 (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 184. Paraphrase: For every Poulet number P, P - 5 is a sum of distinct powers of 2.

**Result.** True and trivial: binary expansion of the positive integer P - 5.

**Argument.** Every positive integer has a binary expansion.

Lean: [full proof](C184/C184_mathlib.lean).

### [C188](C188/): Carmichael numbers pq + q - p (duplicate of C123)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 188. Paraphrase: Same as conjecture 123.

**Result.** False (see C123).

**Argument and evidence.** This item restates [COM-C123](C123/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C123/C123.lean`](C123/C123.lean).
Lean (Mathlib): [`C123_mathlib.lean`](C123/C123_mathlib.lean) (`C123_false, C123_witness`) proves the result in full; outside Lean: none.

Lean: [full proof](C123/C123_mathlib.lean).

### [C190](C190/): 2823 is not a sum of three squares

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 190. Paraphrase: Every Carmichael number is a^2 + b^2 + c^2 - 2 with a, b, c prime.

**Result.** False: 2821 + 2 = 2823 = 7 (mod 8) is not a sum of three squares.

**Argument.** Squares are 0, 1, 4 (mod 8).

Lean: [full proof](C190/C190.lean).

### [C194](C194/): x(P1 - 1) = y(P2 - 1) has other solutions (trivial)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 194. Paraphrase: For Poulet numbers P1, P2 sharing a prime factor, x(P1 - 1) = y(P2 - 1) has integer solutions other than x = P2 - 1, y = P1 - 1.

**Result.** True and trivial: (2(P2 - 1), 2(P1 - 1)), or (0, 0).

**Argument.** Scale the trivial solution.

Lean: [full proof](C194/C194.lean).

### [C195](C195/): Poulet numbers as m + n + q with primes in one class mod 30

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 195. Paraphrase: Every Poulet number not divisible by 5 is m + n + q (primes in one class) with all primes in the same class 30k + 1, 30k + 3, 30k + 7 or 30k + 9.

**Reading.** Read literally (mod 30). The listed residues 1, 3, 7, 9 suggest last digits (mod 10); under that reading the claim holds for all 88 such Poulet numbers below 2e5 and is open.

**Result.** False as stated: such sums are 3r (mod 30), hence divisible by 3, and 341 is not.

**Argument.** Direct.

Lean: [full proof](C195/C195.lean).

### [C196](C196/): Poulet numbers as 2m + n with primes in one class mod 30

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 196. Paraphrase: Every Poulet number not divisible by 5 is 2m + n (distinct primes in one class) with all primes in the same class 30k + 1, 30k + 3, 30k + 7 or 30k + 9.

**Reading.** Read literally (mod 30). The listed residues 1, 3, 7, 9 suggest last digits (mod 10); under that reading the claim holds for all 88 such Poulet numbers below 2e5 and is open.

**Result.** False as stated: such sums are 3r (mod 30), hence divisible by 3, and 341 is not.

**Argument.** Direct.

Lean: [full proof](C195/C195.lean).

### [C200](C200/): No Poulet numbers of the C200 shape for n = 3

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part one, conjecture 200. Paraphrase: For every n >= 1 there are infinitely many k >= 1 with 2^(nk)(2^(n(k+1)) + 2^n + 1) + 1 a Poulet number.

**Result.** False: for n = 3 there is no k at all.

**Argument.** The number is (x^(k+1) + 1)(x^k + 1), x = 2^n. For x = 8 = -1 (mod 9), 9 divides it; a psp divisible by 9 would have 6 = ord_9(2) | P - 1, so 3 | P - 1.

Lean: [full proof](C200/C200.lean).

### [P004](P004/): Carmichael numbers 7*13*(18k+1) (restates C089)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 4. Paraphrase: Study Carmichael numbers 91(18k+1); restates conjecture 89 (cofactor 1 or 13 mod 18).

**Result.** False (see C089): 9890881.

**Argument and evidence.** This item restates [COM-C089](C089/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C089/C089.lean`](C089/C089.lean).
Lean (Mathlib): [`C089_mathlib.lean`](C089/C089_mathlib.lean) (`C089_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C089/C089_mathlib.lean).

### [P005](P005/): Carmichael numbers 19*37*(18k+1) (restates C090)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 5. Paraphrase: Study Carmichael numbers 703(18k+1); restates conjecture 90.

**Result.** True (see C090).

**Argument and evidence.** This item restates [COM-C090](C090/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C090/C090.lean`](C090/C090.lean).

Lean: [full proof](C090/C090.lean).

### [P008](P008/): Carmichael numbers n(2n-1)(5n-4) and forms I/II (restates C091)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 8. Paraphrase: Study the Carmichael numbers n(2n-1)(5n-4); the attached conjecture is conjecture 91.

**Result.** False (see C091): 162401.

**Argument and evidence.** This item restates [COM-C091](C091/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C091/C091.lean`](C091/C091.lean).
Lean (Mathlib): [`C091_mathlib.lean`](C091/C091_mathlib.lean) (`C091_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C091/C091_mathlib.lean).

### [P015](P015/): 2^C mod 560 for Carmichael numbers C

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 15. Paraphrase: Study f = 2^C mod 560 for Carmichael numbers C (Coman notes f = 352 for the first fifteen).

**Result.** Answered: for every integer C >= 4, f = 352 exactly when C = 1 (mod 12). (608 of the 646 Carmichael numbers below 1e9 are 1 mod 12.)

**Argument.** 560 = 16 * 5 * 7. For C >= 4, 2^C = 0 (mod 16); 2^C = 2 (mod 5) iff C = 1 (mod 4) and 2^C = 2 (mod 7) iff C = 1 (mod 3); 352 is 0, 2, 2 modulo 16, 5, 7.

Lean: [full proof](P015/P015.lean).

### [P016](P016/): Carmichael numbers 1 mod 10, 12 or 14: fails

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 16. Paraphrase: Study the conjecture that every Carmichael number is 1 (mod 10), 1 (mod 12) or 1 (mod 14).

**Result.** False: 62745 = 3 * 5 * 47 * 89 is 5, 9, 11 modulo 10, 12, 14.

**Argument.** Direct.

Lean: [full proof](P016/P016_mathlib.lean).

### [P018](P018/): Carmichael triples p(C1 - 1) - C2 = C3

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 18. Paraphrase: Are there Carmichael triples with p(C1 - 1) - C2 = C3, p prime, besides (561, 1729, 8911)?

**Result.** Yes: 14293 * 560 - 8911 = 7995169 = 7 * 13 * 103 * 853, with (C1, C2, C3) = (561, 8911, 7995169).

**Argument.** Direct.

Lean: [full proof](P018/P018_mathlib.lean).

### [P022](P022/): Carmichael numbers 176n + 1

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 22. Paraphrase: Are there Carmichael numbers 176n + 1 besides 2465 and 15841?

**Result.** Yes: 340561, 670033, 825265, 1615681, ... (15 below 10^7).

**Argument.** Direct.

Lean: [full proof](P022/P022_mathlib.lean).

### [P026](P026/): P - 80n and P - 150n prime (restates C095, C096)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 26. Paraphrase: Study conjectures 95 and 96.

**Result.** Both false (see C095: 1105; C096: 561).

**Argument and evidence.** This item restates [COM-C095](C095/README.md), [COM-C096](C096/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C095/C095.lean`](C095/C095.lean).

Lean: [full proof](C095/C095.lean).

### [P038](P038/): Carmichael 1800n^2 +- 840n +- prime (restates C099)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 38. Paraphrase: Study conjecture 99.

**Result.** False (see C099).

**Argument and evidence.** This item restates [COM-C099](C099/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C099/C099.lean`](C099/C099.lean).
Lean (Mathlib): [`C099_mathlib.lean`](C099/C099_mathlib.lean) (`C099_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C099/C099_mathlib.lean).

### [P040](P040/): C^2 - 2C - 30k is never prime for C = 162401

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 40. Paraphrase: For every Carmichael number C prime to 15, is some C^2 - 2C - 30k prime? Same question for C1^2 - 2C2 - 30k.

**Result.** No to both: C = 162401 gives C(C-2) = 9 (mod 30), so every positive C^2 - 2C - 30k is a multiple of 3 above 3; likewise 1729^2 - 2*162401 = 9 (mod 30).

**Argument.** 162401 = 2 (mod 3), so C - 2 = 0 (mod 3); and the values are 9 (mod 30), never 3.

Lean: [full proof](P040/P040_mathlib.lean).

### [P042](P042/): p(p+2) + C for twin primes (contains C101)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 42. Paraphrase: Study N = p(p+2) + C for twin primes and a Carmichael number C; the attached conjecture (C = 1729) is conjecture 101.

**Result.** The conjecture is true (see C101).

**Argument and evidence.** This item restates [COM-C101](C101/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C101/C101.lean`](C101/C101.lean) (core, finite facts) and [`../C101/C101_mathlib.lean`](C101/C101_mathlib.lean) (Mathlib, full proof of the C = 1729 conjecture, `C101_main`).

Lean: [full proof](C101/C101_mathlib.lean).

### [P044](P044/): Carmichael numbers 561 + 272n

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 44. Paraphrase: Are there Carmichael numbers 561 + 272n besides 1105 and 2465?

**Result.** Yes: 75361, 162401, 278545, 340561, ...

**Argument.** Direct.

Lean: [full proof](P044/P044_mathlib.lean).

### [P045](P045/): Carmichael numbers C = n(C - 1) - p(p + 2)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 45. Paraphrase: Are there Carmichael numbers C = n(C-1) - p(p+2) (p, p+2 twin primes) besides 1729?

**Result.** Yes: 6601 = 67 * 6600 - 659 * 661 (scan: one exists for each of the first 200 Carmichael numbers).

**Argument.** Direct.

Lean: [full proof](P045/P045.lean).

### [P046](P046/): Odd Poulet numbers (a^2 - b^2)/8 (restates C102)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 46. Paraphrase: Study conjecture 102.

**Result.** True and trivial (see C102).

**Argument and evidence.** This item restates [COM-C102](C102/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C102/C102.lean`](C102/C102.lean).

Lean: [full proof](C102/C102.lean).

### [P047](P047/): Digital root and prime factors (restates C103)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 47. Paraphrase: Study conjecture 103.

**Result.** False (see C103): 62745.

**Argument and evidence.** This item restates [COM-C103](C103/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C103/C103.lean`](C103/C103.lean).
Lean (Mathlib): [`C103_mathlib.lean`](C103/C103_mathlib.lean) (`C103_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C103/C103_mathlib.lean).

### [P051](P051/): C = n(n+p)/8 and three related conjectures

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 51. Paraphrase: Study four conjectures: (1) every Carmichael number is n(n+p)/8 with p a prime or prime power (= conjecture 108); (2) infinitely many Carmichael numbers 104(104+p)/8 with p prime; (3) infinitely many primes 7q - 104 with q = 6k+1 prime; (4) infinitely many primes q1 q2 - 8(q1 + 6) of a stated kind.

**Result.** Conjecture 1 is false (see C108: 162401). Conjectures 2-4 are open and not addressed.

**Argument and evidence.** This item restates [COM-C108](C108/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C108/C108.lean`](C108/C108.lean).
Lean (Mathlib): [`C108_mathlib.lean`](C108/C108_mathlib.lean) (`C108_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C108/C108_mathlib.lean).

### [P052](P052/): C = n(n+a)/(a+1) (restates C112)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 52. Paraphrase: Study conjecture 112.

**Result.** True and trivial (see C112).

**Argument and evidence.** This item restates [COM-C112](C112/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C112/C112.lean`](C112/C112.lean).

Lean: [full proof](C112/C112.lean).

### [P055](P055/): Carmichael numbers p^4 + 60p (restates C116)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 55. Paraphrase: Study Carmichael numbers p^4 + 60p; conjecture 116.

**Result.** False (see C116): only 2821 and 29341.

**Argument and evidence.** This item restates [COM-C116](C116/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C116/C116.lean`](C116/C116.lean).
Lean (Mathlib): [`C116_mathlib.lean`](C116/C116_mathlib.lean) (`C116_main, C116_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C116/C116_mathlib.lean).

### [P062](P062/): Prime triples p, p + C1 - 1, p + C2 - 1 summing to a Carmichael number

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 62. Paraphrase: Are there other p, C1, C2, C3 with p, p + C1 - 1, p + C2 - 1 prime and sum C3 Carmichael, besides (59, 561, 1729, 2465)?

**Result.** Yes: (1812443, 561, 6601, 5444489).

**Argument.** Direct.

Lean: [full proof](P062/P062_mathlib.lean).

### [P064](P064/): C = pq + q - p (restates C123)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 64. Paraphrase: Study conjecture 123.

**Result.** False (see C123): 1024651.

**Argument and evidence.** This item restates [COM-C123](C123/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C123/C123.lean`](C123/C123.lean).
Lean (Mathlib): [`C123_mathlib.lean`](C123/C123_mathlib.lean) (`C123_false, C123_witness`) proves the result in full; outside Lean: none.

Lean: [full proof](C123/C123_mathlib.lean).

### [P065](P065/): C = p(q - 2^n) and 5p + 2^n (C124 and C125)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 65. Paraphrase: Study two conjectures: conjecture 124 (3-Carmichael numbers divisible by 5 are p(q - 2^n)) and conjecture 125 (for every odd prime p != 5, infinitely many n with 5p + 2^n prime).

**Result.** The first is true (see C124), the second false (see C125: p = 76739471787787, covering with period 72).

**Argument and evidence.** This item restates [COM-C124](C124/README.md), [COM-C125](C125/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C125/C125.lean`](C125/C125.lean).

Lean: [full proof](C125/C125.lean).

### [P066](P066/): (P + 5^m) prime conjectures for Poulet numbers

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes*
(2013), Part four (open problems), problem 66, restating conjectures 126-129 of Part one. Paraphrase: (1) every
Poulet number P with 3, 5 not dividing P has m >= 1 with (P + 5^m)/6^n prime or a prime power; (2) every Poulet
P with 5 | P, 3 not dividing P, has m with (P + 5^m)/30 prime; (3) every Poulet P with 15 | P has m with
(P + 5^m)/10 prime; (4) apart from "definable exceptions", every n not divisible by 5 has m with 6n - 5^m prime
or 1.

**Reading.** In (1), n is any exponent with 6^n | P + 5^m (the claim fails for every such n below, so the
choice of n does not matter).

**Result.** - (1) False, non-constructively (new here). For every P = a (mod M) with
  a = 164743819436130905311195649881, M = 197386120142055051194076523980 = 4·3·5·13·313·17·11489·31·7·601·
  390001·19·829·5167, every m and every admissible n, (P + 5^m)/6^n is not a prime power. The class is coprime
  (gcd(a, M) = 1), so it contains infinitely many Carmichael numbers (T. Wright, Bull. London Math. Soc. 45
  (2013) 943-952), which are Poulet numbers with 3, 5 not dividing P. No explicit P is known.
- (2) False: see [COM/C127](C127/README.md) (covering plus Larsen 2025).
- (3) False: see [COM/C128](C128/README.md).
- (4) Ill-posed: the exceptions are not defined; 113 n below 3000 have no such m (scan record COM-C129).

**Argument for (1).** P = 1 (mod 4) gives P + 5^m = 2 (mod 4), so n <= 1. For n = 0, P + 5^m = 2·u with u odd
and u > 1, not a prime power. For n = 1, 3 | P + 5^m forces m odd (P = 1 mod 3). Two disjoint coverings of the
odd m: m = 1 (4), 3 (8), 7 (16), 15 (16) with q = 13, 313, 17, 11489, and m = 0 (3), 1 (6), 5 (12), 11 (24),
2 (9), 5 (9), 17 (18) with q = 31, 7, 601, 390001, 19, 829, 5167 (q | 5^ord - 1 with the stated order). P = -5^r
(mod q) on each class, so for odd m one prime from each covering divides (P + 5^m)/6; two distinct primes, so not
a prime power.

Lean: [full proof](P066/P066_mathlib.lean).

### [P068](P068/): Poulet numbers with P1 + P2 - 1 Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 68. Paraphrase: Other Poulet P1, P2 with P1 + P2 - 1 Poulet besides (561, 1905)?

**Result.** Yes: 1105 + 63973 - 1 = 65077 = 59 * 1103.

**Argument.** Direct.

Lean: [full proof](P068/P068.lean).

### [P069](P069/): Poulet numbers with P1 + rev(P2) - 2 Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 69. Paraphrase: Other Poulet P1, P2 with P1 + rev(P2) - 2 Poulet besides (561, 645)?

**Result.** Yes: 341 + rev(249841) - 2 = 341 + 148942 - 2 = 149281.

**Argument.** Direct.

Lean: [full proof](P069/P069.lean).

### [P078](P078/): Primes (n + d^k)/d (restates C136)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 78. Paraphrase: Study conjecture 136.

**Result.** False (see C136).

**Argument and evidence.** This item restates [COM-C136](C136/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C136/C136.lean`](C136/C136.lean).

Lean: [full proof](C136/C136.lean).

### [P080](P080/): Four conjectures on primes from Poulet numbers and primes (C137-C140)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 80. Paraphrase: Study conjectures 137, 138, 139, 140.

**Result.** Mixed: conjectures 1, 3, 4 (= C137, C139, C140) are false (the primes are bounded); conjecture 2 (= C138) is true.

**Argument and evidence.** This item restates [COM-C137](C137/README.md), [COM-C138](C138/README.md), [COM-C139](C139/README.md), [COM-C140](C140/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C137/C137.lean`](C137/C137.lean).

**Second reader: disputed.** The scan index records 'proved'; only conjecture 2 is true, conjectures 1, 3 and 4 are false (bounded values), so the record should read 'mixed (3 false, 1 true)'.

Lean: [full proof](C137/C137.lean).

### [P085](P085/): Five divisibility conjectures for 2- and 3-Poulet numbers (C146-C150)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 85. Paraphrase: Study conjectures 146-150.

**Result.** All five false (see C146: 149281, C147: 49981, C148: 3090091, C149: 1241143 base 3, C150: 711361).

**Argument and evidence.** This item restates [COM-C146](C146/README.md), [COM-C147](C147/README.md), [COM-C148](C148/README.md), [COM-C149](C149/README.md), [COM-C150](C150/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C146/C146.lean`](C146/C146.lean).

Lean: [full proof](C146/C146.lean).

### [P089](P089/): Carmichael multiples of 8911 (restates C151)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 89. Paraphrase: Study Carmichael numbers divisible by 8911; conjecture 151.

**Result.** True (see C151).

**Argument and evidence.** This item restates [COM-C151](C151/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C151/C151.lean`](C151/C151.lean).

Lean: [full proof](C151/C151.lean).

### [P103](P103/): Poulet numbers (42m+1)(42n+1) (restates C162)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 103. Paraphrase: Study Poulet numbers (42m+1)(42n+1); conjecture 162.

**Result.** True (see C162).

**Argument and evidence.** This item restates [COM-C162](C162/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C162/C162.lean`](C162/C162.lean).
Lean (Mathlib): [`C162_mathlib.lean`](C162/C162_mathlib.lean) (`C162_main`) proves the result in full; outside Lean: none.

Lean: [full proof](C162/C162_mathlib.lean).

### [P115](P115/): Carmichael numbers divisible by 37 and 73 (C173, C174)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 115. Paraphrase: Study conjectures 173 and 174.

**Result.** Both false (see C173/C174: 294409).

**Argument and evidence.** This item restates [COM-C173](C173/README.md), [COM-C174](C174/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C173/C173.lean`](C173/C173.lean).
Lean (Mathlib): [`C173_mathlib.lean`](C173/C173_mathlib.lean) (`C173_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C173/C173_mathlib.lean).

### [P122](P122/): Carmichael and Poulet numbers p + q + r with primes in one class

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 122. Paraphrase: Other Carmichael or Poulet numbers p + q + r with p, q, r prime in the same class coprime to 30, besides 561 = 47 + 167 + 347?

**Result.** Yes: Poulet 4371 = 7 + 7 + 4357 and Carmichael 656601 = 7 + 7 + 656587. Such sums are 3r (mod 30), so only numbers = 3, 9, 21, 27 (mod 30) can qualify.

**Argument.** Direct.

Lean: [full proof](P122/P122_mathlib.lean).

### [P128](P128/): C versus d^4; Carmichael numbers p^4 + 60p (contains C116)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 128. Paraphrase: Study Carmichael numbers relative to the fourth power of the least prime factor; the attached conjecture is conjecture 116/179.

**Result.** The conjecture is false (see C116).

**Argument and evidence.** This item restates [COM-C116](C116/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C116/C116.lean`](C116/C116.lean).
Lean (Mathlib): [`C116_mathlib.lean`](C116/C116_mathlib.lean) (`C116_main, C116_false`) proves the result in full; outside Lean: none.

Lean: [full proof](C116/C116_mathlib.lean).

### [P132](P132/): 2^k p n + p^2 representation (restates C183)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 132. Paraphrase: Study conjecture 183.

**Result.** True and trivial (see C183).

**Argument and evidence.** This item restates [COM-C183](C183/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C183/C183.lean`](C183/C183.lean).

Lean: [full proof](C183/C183.lean).

### [P133](P133/): P - 5 as a sum of powers of 2 (restates C184)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 133. Paraphrase: Study conjecture 184.

**Result.** True and trivial (see C184).

**Argument and evidence.** This item restates [COM-C184](C184/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean (Mathlib): [`P133_mathlib.lean`](P133/P133_mathlib.lean) (same proof as COM-C184's `C184_mathlib.lean`): `P133_main`, every Poulet number P has 5 < P and P - 5 = ∑_{i ∈ S} 2^i for a finite set S. Outside Lean: nothing.

Lean: [full proof](P133/P133_mathlib.lean).

### [P145](P145/): C = pq + q - p (restates C188 = C123)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 145. Paraphrase: Study conjecture 188 (= 123).

**Result.** False (see C123): 1024651.

**Argument and evidence.** This item restates [COM-C123](C123/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C123/C123.lean`](C123/C123.lean).
Lean (Mathlib): [`C123_mathlib.lean`](C123/C123_mathlib.lean) (`C123_false, C123_witness`) proves the result in full; outside Lean: none.

Lean: [full proof](C123/C123_mathlib.lean).

### [P147](P147/): C = a^2 + b^2 + c^2 - 2 (restates C190)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 147. Paraphrase: Study conjecture 190.

**Result.** False (see C190): 2821.

**Argument and evidence.** This item restates [COM-C190](C190/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C190/C190.lean`](C190/C190.lean).

Lean: [full proof](C190/C190.lean).

### [P150](P150/): x(P1 - 1) = y(P2 - 1) (restates C194)

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 150. Paraphrase: Study conjecture 194.

**Result.** True and trivial (see C194).

**Argument and evidence.** This item restates [COM-C194](C194/README.md); the argument, Lean file and scripts are there (not duplicated).
Lean: [`../C194/C194.lean`](C194/C194.lean).

Lean: [full proof](C194/C194.lean).

### [P126](P126/): Poulet numbers P = (d^2 + d)/2 with d a prime factor of P

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 126. Paraphrase: are there Poulet numbers P = (d^2 + d)/2, d a prime factor of P, other than 2701 = (73^2 + 73)/2? The attached infinitude conjecture is conjecture 177 (COM-C177, not settled here).

**Result.** Yes. 18721 = (193^2 + 193)/2 = 97 * 193 and 33153 = (257^2 + 257)/2 = 3 * 43 * 257 are base-2 pseudoprimes. There are 7988 such P below 10^13.

**Argument.** Direct check. A sufficient condition explains most examples: if d is a prime with d = ±1 (mod 8) and m = (d + 1)/2 is prime, then P = d*m and P - 1 = ((d - 1)/2)(d + 2) = (m - 1)(2m + 1); 2 is a square mod d, so ord_d(2) divides (d - 1)/2, and ord_m(2) divides m - 1, hence 2^(P-1) = 1 (mod P). Examples: (73, 37), (193, 97).

Lean: [full proof](P126/P126_mathlib.lean).

### [P127](P127/): Poulet numbers P2 = 2*P1 - 1 with P1 Poulet

**Source.** M. Coman, *Two Hundred Conjectures and One Hundred and Fifty Open Problems on Fermat Pseudoprimes* (2013), Part four, problem 127. Paraphrase: are there Poulet numbers P2 = 2*P1 - 1 with P1 also Poulet, other than 130561 = 2*65281 - 1? The attached infinitude conjecture is conjecture 178 (COM-C178, not settled here).

**Result.** Yes. 31417 = 2*15709 - 1 (31417 = 89*353, 15709 = 23*683) and 41541241 = 2*20770621 - 1. There are 27 such P2 below 10^13.

**Argument.** Direct check.

Lean: [full proof](P127/P127_mathlib.lean).

