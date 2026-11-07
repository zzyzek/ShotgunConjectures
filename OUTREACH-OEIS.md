# OEIS outreach list

OEIS entries whose conjecture this project settled and which OEIS does not yet record as settled
(prior-art review 2026-11-04: current entry, entries citing it, edit history, web, arXiv).
Each draft comment is a starting point: shorten it to OEIS style and sign it. "Partly known" means a source covers part of it; the note says which part.

223 entries.

## Substantive (not an immediate consequence of a known theorem) (103)

### [A026002](https://oeis.org/A026002): Bergot's array with borders n(n−1)+1 has diagonal A026002

- Problem: [OEIS-A026002](OEIS/A026002/README.md) (proved, new). Lean: Lean proof, [`A026002_mathlib.lean`](OEIS/A026002/A026002_mathlib.lean).
- Prior art: No proof found; closed form 2m(i,j) = D(i-1,j+1) + D(i+1,j-1) and Lean proof new as far as found. Argument short.
- Draft comment:

  > The conjecture is true: with the closed form 2·m(i,j) = D(i−1, j+1) + D(i+1, j−1) for all i, j ≥ 1. On the diagonal the two terms are equal (D is symmetric), so m(n,n) = D(n−1, n+1) = a(n). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A026002). - _<Name>_, <Mon DD YYYY>

### [A036284](https://oeis.org/A036284): OEIS A036284

- Problem: [OEIS-A036284](OEIS/A036284/README.md) (proved, new). Lean: Lean proof, [`A037097_mathlib.lean`](OEIS/A037097/A037097_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A036284). - _<Name>_, <Mon DD YYYY>

### [A037096](https://oeis.org/A037096): OEIS A037096

- Problem: [OEIS-A037096](OEIS/A037096/README.md) (proved, new). Lean: Lean proof, [`A037097_mathlib.lean`](OEIS/A037097/A037097_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A037096). - _<Name>_, <Mon DD YYYY>

### [A037097](https://oeis.org/A037097): (x+1)- and (x^3+1)-power factors of periodic binary columns

- Problem: [OEIS-A037097](OEIS/A037097/README.md) (proved, new). Lean: Lean proof, [`A037097_mathlib.lean`](OEIS/A037097/A037097_mathlib.lean).
- Prior art: Corrected exponent stated by Gu in Jul 2026 without proof; no proof found.
- Draft comment:

  > The conjecture is true: - A037097: the corrected statement is true, with exact exponent 2^(n-2) - 1. The older exponent 2^(n-1) - 1 (the scan record's version) is false: a(3) = 12 = x^2 + x^3 = x^2 (x+1) and a(4) = 120 = x^3 (x+1)^3. - A037096: true. - A036284: both conjectures true. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A037097). - _<Name>_, <Mon DD YYYY>

### [A045764](https://oeis.org/A045764): Meeussen's numbers are not values of W(n) = n − d(n) − φ(n) + 1

- Problem: [NT-B10.3](NT/B10.3/README.md) (proved, new). Lean: Lean proof, [`B10_3_mathlib.lean`](NT/B10.3/B10_3_mathlib.lean).
- Prior art: OEIS A045764 lists exactly these numbers and still labels them a conjecture; our result proves every odd term below 1000 (A045764 also contains the even term 2, which our result does not cover). Worth an OEIS comment.
- Draft comment:

  > The conjecture is true for every odd term below 1000: none of them is a value of W(n) = n - d(n) - phi(n) + 1, and the odd non-values below 1000 are exactly 86 numbers 13, 67, 93, 123, ..., 973, 997. For n >= 3, W(n) is odd only if n is an odd square or an even nonsquare, and the bounds phi(n) <= n/2, d(n) <= 2*sqrt(n) (n even) and phi(k^2) <= k^2*(1 - 1/p) with p the least prime factor of k (k odd composite) show that W(n) < 1000 forces n <= 1001^2, which a sieve covers. The even term 2 is not covered by this argument. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/NT/B10.3.

### [A054656](https://oeis.org/A054656): for n >= 23, a(n) = [n-6 prime] + [n-4 prime] + [n-1 prime]

- Problem: [OEIS-A054656](OEIS/A054656/README.md) (proved, new). Lean: Lean proof, [`A054656_mathlib.lean`](OEIS/A054656/A054656_mathlib.lean).
- Prior art: No proof of the conjecture found; the avoid-one-prime Richert induction and the two-primes Bertrand step are ours (both standard in spirit).
- Draft comment:

  > The conjecture is true: for every n >= 23. The bound is sharp: a(22) = 1 (the prime 11) while the formula gives 0. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A054656). - _<Name>_, <Mon DD YYYY>

### [A056142](https://oeis.org/A056142): a(n) palindrome only if all digits of n are equal

- Problem: [OEIS-A056142](OEIS/A056142/README.md) (corrected-and-proved, new). Lean: Lean proof, [`A056142_mathlib.lean`](OEIS/A056142/A056142_mathlib.lean).
- Prior art: Literal statement refuted by the entry's own 3-digit comment; the 4-or-more-digit version is new here.
- Draft comment:

  > The conjecture is misstated as written; the corrected form is true: As stated the conjecture is false: n = 101 has 3 digits and a(101) = 101101 is a palindrome (every 3-digit palindrome n is a counterexample, as Wasserman's comment already implies). For 4 or more digits it is true: if n has d >= 4 digits, a(n) is a palindrome iff all digits of n are equal. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A056142). - _<Name>_, <Mon DD YYYY>

### [A058347](https://oeis.org/A058347): the double-support check counts are symmetric, T(n,k) = T(k,n)

- Problem: [OEIS-A058347](OEIS/A058347/README.md) (proved, new). Lean: Lean proof, [`A058347_mathlib.lean`](OEIS/A058347/A058347_mathlib.lean).
- Prior art: No proof found; closed form via GF(2) rank sums is ours.
- Draft comment:

  > The conjecture is true: With S(n,k) = Σ_M rank(M), the sum of the GF(2)-ranks of all n x k 0-1 matrices, T(n,k) = 2^(nk)(2n + 2k − n·2^(1−k) − k·2^(1−n)) − 2 S(n,k), and both parts are symmetric (rank(Mᵀ) = rank(M)). Equivalently the expected number of checks is 2n + 2k − n·2^(1−k) − k·2^(1−n) − 2·E[rank]. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A058347). - _<Name>_, <Mon DD YYYY>

### [A059970](https://oeis.org/A059970): nim-factorials of 2^n - 1 and 2^n + 2^(n-1) - 1

- Problem: [OEIS-A059970](OEIS/A059970/README.md) (proved, new). Lean: paper proof.
- Prior art: Case n = 2^k of (1) is Wilson's theorem; general cases not found.
- Draft comment:

  > The conjecture is true: Both are true for every n >= 1. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A059970). - _<Name>_, <Mon DD YYYY>

### [A065558](https://oeis.org/A065558): a(2n) = 2 psi(n) (maximal irreducible degree of GL_2(Z/2nZ))

- Problem: [OEIS-A065558](OEIS/A065558/README.md) (proved, partly-known). Lean: paper proof.
- Prior art: Odd p known; p = 2 statement not found, argument here.
- Draft comment:

  > The conjecture is true: Precisely: a(p^r) = p^(r-1)(p+1) for every prime power p^r except a(2) = 2, so a(n) = psi(n) for odd n, and a(2n) = 2 psi(n) for all n >= 1. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A065558). - _<Name>_, <Mon DD YYYY>

### [A069187](https://oeis.org/A069187): core(k) = ⌈√k⌉ exactly for k = 1 and k = n²(n²+1) with n²+1 squarefree

- Problem: [OEIS-A069187](OEIS/A069187/README.md) (proved, new). Lean: Lean proof, [`A069187_mathlib.lean`](OEIS/A069187/A069187_mathlib.lean).
- Prior art: Elementary; no proof found.
- Draft comment:

  > The conjecture is true: with one correction at the start: the terms are 1 and the n²(n²+1) with n ≥ 1 and n²+1 squarefree. A071253(0) = 0 is not a term and 1 is not in A071253. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A069187). - _<Name>_, <Mon DD YYYY>

### [A072939](https://oeis.org/A072939): c(k) → ∞ exactly when n − 1 has odd 2-adic valuation, so a(n) = A036554(n) + 1

- Problem: [OEIS-A072939](OEIS/A072939/README.md) (proved, new). Lean: Lean proof, [`A072939.lean`](OEIS/A072939/A072939.lean).
- Prior art: Stephan's 2003 comment restates the formula without proof.
- Draft comment:

  > The conjecture is true: for n ≥ 1, c(k) → ∞ iff n − 1 = 2^v·u with u odd and v odd. Hence a(n) = A036554(n) + 1, and the entry's m(n) is u, the odd part of n − 1. Otherwise c(k) is eventually 1. (proof verified in Lean 4: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A072939). - _<Name>_, <Mon DD YYYY>

### [A076070](https://oeis.org/A076070): no entry is zero

- Problem: [OEIS-A076070](OEIS/A076070/README.md) (proved, new). Lean: paper proof.
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A076070). - _<Name>_, <Mon DD YYYY>

### [A076072](https://oeis.org/A076072): a multiple of n can always be formed from the digits of the next n numbers

- Problem: [OEIS-A076072](OEIS/A076072/README.md) (proved, new). Lean: paper proof.
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true: for every n >= 1: some arrangement of the digits is a multiple of n. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A076072). - _<Name>_, <Mon DD YYYY>

### [A077602](https://oeis.org/A077602): M(n,1) ~ A077596(n) · sqrt(πn/2) for the Moebius polynomials

- Problem: [OEIS-A077602](OEIS/A077602/README.md) (proved, new). Lean: paper proof.
- Prior art: Asymptotics stated only as conjecture/numerics in OEIS.
- Draft comment:

  > The conjecture is true: for both readings of A077596(n) (the coefficient of x^(k0), or the largest coefficient). Equivalently A077596(n) ~ c 2^n/√n with c = L √(2/π) = 1.2209161..., L = lim M(n,1)/2^n (Kotesovec's numerical constant in A077596). (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A077602). - _<Name>_, <Mon DD YYYY>

### [A078537](https://oeis.org/A078537): row sums of A078536 are the partitions of 4^n into powers of 4

- Problem: [OEIS-A078537](OEIS/A078537/README.md) (proved, new). Lean: Lean proof, [`A078537_mathlib.lean`](OEIS/A078537/A078537_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true: for every base q >= 2 (q = 4 here; q = 2, 3 are A078121, A078122). Write t(m, c) for the number of partitions of c q^m into 1, q, ..., q^m. Then M(n,k) = t(n-k, q^k - 1) (the entry's conjectured formula), more generally [M^s](n,k) = t(n-k, s q^k - 1) for s >= 1, and row n sums to the number of partitions of q^n into powers of q. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A078537). - _<Name>_, <Mon DD YYYY>

### [A082981](https://oeis.org/A082981): the six section conjectures

- Problem: [OEIS-A082981](OEIS/A082981/README.md) (proved, new). Lean: Lean proof, [`A082981_mathlib.lean`](OEIS/A082981/A082981_mathlib.lean).
- Prior art: No proof found. The block structure follows from locality of the insertion and the leftmost live pair.
- Draft comment:

  > The conjecture is true: All six are true. Moreover a(4j+t) = 4c_j + t d_j (t = 1..4, with 4c_{j+1} = 4c_j + 4d_j for t = 4), where (c_0, d_0) = (0, 1) and (c, d) -> (c + d, 4c + 5d); this gives a(n) = 6a(n-4) - a(n-8) and the g.f. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A082981). - _<Name>_, <Mon DD YYYY>

### [A083219](https://oeis.org/A083219): roots of x^n - x^(n-1) - ... - 1 in the left half-plane

- Problem: [OEIS-A083219](OEIS/A083219/README.md) (proved, new). Lean: Lean proof, [`A129756_mathlib.lean`](OEIS/A129756/A129756_mathlib.lean).
- Prior art: Same proof settles the A083219 comment (left half-plane), with the same index shift; A083219 has its own triage record (not recorded here).
- Draft comment:

  > The conjecture is true: with the index shift. For every n, x^(n+1) − x^n − … − x − 1 has n − 2⌊n/4⌋ roots with Re < 0. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A083219). - _<Name>_, <Mon DD YYYY>

### [A087726](https://oeis.org/A087726): a(n) = n^2 if and only if n is squarefree

- Problem: [OEIS-A087726](OEIS/A087726/README.md) (proved, partly-known). Lean: Lean proof, [`A087726_mathlib.lean`](OEIS/A087726/A087726_mathlib.lean).
- Prior art: Squarefree direction known (Schmidt/Scheucher); the converse (a(p^k) > p^(2k) for k >= 2) and the proof of Israel's exact formula are new as far as found.
- Draft comment:

  > The conjecture is true: for n >= 1, a(n) = n^2 iff n is squarefree. Moreover a(n) >= n^2 for all n >= 1, and a(p^k) > p^(2k) for every prime p and k >= 2. Israel's formula is also true: for every prime p and k >= 1, a(p^k) = p^(4 floor(k/2)) + ceil(k/2) p^(2k-2) (p^2 - 1) = (1+3p^2+2k(p^2-1)+(-1)^k(p^2-1)) p^(2k-2)/4. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A087726). - _<Name>_, <Mon DD YYYY>

### [A094787](https://oeis.org/A094787): every prime is a least prime p with p + n a perfect power

- Problem: [OEIS-A094787](OEIS/A094787/README.md) (proved, new). Lean: Lean proof, [`A094787_mathlib.lean`](OEIS/A094787/A094787_mathlib.lean).
- Prior art: Short counting argument; no source found.
- Draft comment:

  > The conjecture is true: for a prime q and m > q put n = m^2 - q; then p + n is not a square for any prime p < q, since (m-1)^2 < m^2 - q + 2, so a(n) = q unless [m^2 - q + 2, m^2 - 1] contains a non-square perfect power. These windows are disjoint for different m, and there are only O(M^(2/3)*log M) non-square perfect powers up to M^2, so some m > q works. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A094787.

### [A096127](https://oeis.org/A096127): a(n) = n+1 exactly when n is a prime power

- Problem: [OEIS-A096127](OEIS/A096127/README.md) (proved, new). Lean: Lean proof, [`A096127_mathlib.lean`](OEIS/A096127/A096127_mathlib.lean).
- Prior art: No proof found; the digit-sum argument is ours.
- Draft comment:

  > The conjecture is true: For n ≥ 2, a(n) ≥ n+1 always, and a(n) = n+1 if and only if n is a prime power. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A096127). - _<Name>_, <Mon DD YYYY>

### [A100682](https://oeis.org/A100682): exception list of Greathouse's formula is incomplete

- Problem: [OEIS-A100682](OEIS/A100682/README.md) (disproved, new). Lean: Lean proof, [`A100682_mathlib.lean`](OEIS/A100682/A100682_mathlib.lean).
- Prior art: No source gives further exceptions. Note: the comment's formula only matches the entry's offset under the shifted reading the README uses.
- Draft comment:

  > Reading the formula as floor(binomial(n,4)^(1/4)) = floor((n - 3/2)/24^(1/4)), the reading that reproduces the listed exceptions 6, 17, 2403, 5318, the conjecture is false: n = 634027531 (index 634027528 of this sequence) is a further exception, with floor(binomial(n,4)^(1/4)) = 286454272 but floor((n - 3/2)/24^(1/4)) = 286454273. Further exceptions in the same reading are 1705327318, 55292025086, ..., near continued-fraction convergents of 384^(1/4). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A100682.

### [A102237](https://oeis.org/A102237): a(n) = 2^n for n > 5

- Problem: [OEIS-A102237](OEIS/A102237/README.md) (proved, new). Lean: Lean proof, [`A102237_mathlib.lean`](OEIS/A102237/A102237_mathlib.lean).
- Prior art: Richert-type induction with an explicit Bertrand bound; not found written for this sequence.
- Draft comment:

  > The conjecture is true: for every n ≥ 6, 2^n is a sum of n distinct primes, so a(n) = 2^n. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A102237). - _<Name>_, <Mon DD YYYY>

### [A103990](https://oeis.org/A103990): sqrt(pi) I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1)

- Problem: [OEIS-A103990](OEIS/A103990/README.md) (proved, new). Lean: Lean proof, [`A103990_mathlib.lean`](OEIS/A103990/A103990_mathlib.lean).
- Prior art: No proof found. The result depends on reading Trott's unpublished algorithm as the canonical integration-by-parts reduction; that reading reproduces all published integrands and terms.
- Draft comment:

  > The conjecture is true: under this reading: sqrt(pi) I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1) for every n >= 1. Equivalently sqrt(pi) I(n,0) = (4n^2 - 6n + 11)/12 - 1/(4(2n+1)). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A103990). - _<Name>_, <Mon DD YYYY>

### [A108863](https://oeis.org/A108863): Motzkin transform of 0, 0, 0, A001651

- Problem: [OEIS-A108863](OEIS/A108863/README.md) (proved, new). Lean: Lean proof, [`A108863_mathlib.lean`](OEIS/A108863/A108863_mathlib.lean).
- Prior art: No proof found; the entry's g.f. is printed without derivation.
- Draft comment:

  > The conjecture is true: the Motzkin transform of b has g.f. G, so equals A108863. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A108863). - _<Name>_, <Mon DD YYYY>

### [A110034](https://oeis.org/A110034): |row sums| of the Fibonacci–Hankel characteristic polynomials are partial sums of A061646

- Problem: [OEIS-A110034](OEIS/A110034/README.md) (corrected-and-proved, new). Lean: Lean proof, [`A110034_mathlib.lean`](OEIS/A110034/A110034_mathlib.lean).
- Prior art: Entry prints a g.f. and a Fibonacci-sum formula without proof; no proof of the conjecture found. n = 0 case of the literal statement fails.
- Draft comment:

  > The conjecture is misstated as written; the corrected form is true: for every n ≥ 1, with a(n) = −Σ_{k=1..n−1} A061646(k) ≤ 0. False as stated at n = 0: a(0) = 1 and the sum is empty (0). Corrected statement: n ≥ 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A110034). - _<Name>_, <Mon DD YYYY>

### [A113249](https://oeis.org/A113249): a(m, 2n+1) is a perfect square (the whole family)

- Problem: [OEIS-A113249](OEIS/A113249/README.md) (proved, partly-known). Lean: Lean proof, [`A113249.lean`](OEIS/A113249/A113249.lean).
- Prior art: The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture. This m is the one Israel proved.
- Draft comment:

  > The conjecture is true for every integer m: a(m,2n+1) = y(m,n)^2 with y(m,n) = 4*y(m,n-1) - m^2*y(m,n-2), y(m,0) = 2, y(m,1) = 8 - m^2. The characteristic polynomial of a(m,n) is (x^2 - m^2)(x^2 + 4x + m^2), so a(m,2n+1) and y(m,n)^2 both satisfy the order-4 recurrence with characteristic polynomial (X - m^2)^2*(X^2 + (2m^2 - 16)X + m^4), and their first four values agree as polynomials in m. For m = 3, y(3,n) is the b(n) of R. Israel's comment above; the case m = 8 is A113254. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A113249.

### [A113251](https://oeis.org/A113251): a(m, 2n+1) is a perfect square (m = 5)

- Problem: [OEIS-A113251](OEIS/A113251/README.md) (proved, partly-known). Lean: Lean proof, [`A113251.lean`](OEIS/A113251/A113251.lean).
- Prior art: The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture.
- Draft comment:

  > The conjecture is true for every integer m, in particular for m = 5: a(m,2n+1) = y(m,n)^2 with y(m,n) = 4*y(m,n-1) - m^2*y(m,n-2), y(m,0) = 2, y(m,1) = 8 - m^2. The characteristic polynomial of a(m,n) is (x^2 - m^2)(x^2 + 4x + m^2), so a(m,2n+1) and y(m,n)^2 both satisfy the order-4 recurrence with characteristic polynomial (X - m^2)^2*(X^2 + (2m^2 - 16)X + m^4), and their first four values agree as polynomials in m. This extends the m = 3 case proved in A113249 and the m = 8 case proved in A113254, and for m = 5 it also follows from the closed form of E. S. Jacob above by the half-angle identity. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A113251.

### [A113253](https://oeis.org/A113253): a(m, 2n+1) is a perfect square (m = 7)

- Problem: [OEIS-A113253](OEIS/A113253/README.md) (proved, partly-known). Lean: Lean proof, [`A113253.lean`](OEIS/A113253/A113253.lean).
- Prior art: The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture.
- Draft comment:

  > The conjecture is true for every integer m, in particular for m = 7: a(m,2n+1) = y(m,n)^2 with y(m,n) = 4*y(m,n-1) - m^2*y(m,n-2), y(m,0) = 2, y(m,1) = 8 - m^2. The characteristic polynomial of a(m,n) is (x^2 - m^2)(x^2 + 4x + m^2), so a(m,2n+1) and y(m,n)^2 both satisfy the order-4 recurrence with characteristic polynomial (X - m^2)^2*(X^2 + (2m^2 - 16)X + m^4), and their first four values agree as polynomials in m. This extends the m = 3 case proved in A113249 and the m = 8 case proved in A113254, and for m = 7 it also follows from the closed form of E. S. Jacob above by the half-angle identity. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A113253.

### [A113256](https://oeis.org/A113256): a(m, 2n+1) is a perfect square (m = 10)

- Problem: [OEIS-A113256](OEIS/A113256/README.md) (proved, partly-known). Lean: Lean proof, [`A113256.lean`](OEIS/A113256/A113256.lean).
- Prior art: The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture.
- Draft comment:

  > The conjecture is true for every integer m, in particular for m = 10: a(m,2n+1) = y(m,n)^2 with y(m,n) = 4*y(m,n-1) - m^2*y(m,n-2), y(m,0) = 2, y(m,1) = 8 - m^2. The characteristic polynomial of a(m,n) is (x^2 - m^2)(x^2 + 4x + m^2), so a(m,2n+1) and y(m,n)^2 both satisfy the order-4 recurrence with characteristic polynomial (X - m^2)^2*(X^2 + (2m^2 - 16)X + m^4), and their first four values agree as polynomials in m. This extends the m = 3 case proved in A113249 and the m = 8 case proved in A113254. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A113256.

### [A127749](https://oeis.org/A127749): see A127750

- Problem: [OEIS-A127749](OEIS/A127749/README.md) (proved, new). Lean: Lean proof, [`A127750_mathlib.lean`](OEIS/A127750/A127750_mathlib.lean).
- Prior art: No proof found; the column recursion and window argument are ours.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A127749). - _<Name>_, <Mon DD YYYY>

### [A127750](https://oeis.org/A127750): row sums mod 2 are the Fredholm-Rueppel sequence

- Problem: [OEIS-A127750](OEIS/A127750/README.md) (proved, new). Lean: Lean proof, [`A127750_mathlib.lean`](OEIS/A127750/A127750_mathlib.lean).
- Prior art: No proof found; the column recursion and window argument are ours.
- Draft comment:

  > The conjecture is true: Both conjectures are true, and so is the A111967 row-sum conjecture: the row sums of A111967 are exactly A036987, and every entry of A111967 is -1, 0 or 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A127750). - _<Name>_, <Mon DD YYYY>

### [A129756](https://oeis.org/A129756): roots of x^n − x^(n−1) − … − x − 1 in the right half-plane

- Problem: [OEIS-A129756](OEIS/A129756/README.md) (proved, new). Lean: Lean proof, [`A129756_mathlib.lean`](OEIS/A129756/A129756_mathlib.lean).
- Prior art: Same proof settles the A083219 comment (left half-plane), with the same index shift; A083219 has its own triage record (not recorded here).
- Draft comment:

  > The conjecture is true: with that index: for n ≥ 1, x^n − x^(n−1) − … − 1 has exactly 1 + 2⌊(n−1)/4⌋ roots with positive real part and n − 1 − 2⌊(n−1)/4⌋ with negative real part (the A083219 comment, same shift). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A129756). - _<Name>_, <Mon DD YYYY>

### [A132827](https://oeis.org/A132827): the array is the dispersion of floor(n*phi + n + 1); the entry's FORMULA is wrong from row 4

- Problem: [OEIS-A132827](OEIS/A132827/README.md) (proved, new). Lean: Lean proof, [`A132827_mathlib.lean`](OEIS/A132827/A132827_mathlib.lean).
- Prior art: No proof found; standard Beatty-complement argument. The FORMULA line error (A005206 should be i - floor(i/phi)) is new.
- Draft comment:

  > The conjecture is true: - True. The dispersion D of f satisfies D(i,j) = (b(i)+1) F(2j) + (i - b(i)) F(2j+1) for all i >= 0, j >= 1, with b(i) = 2i - floor(i*phi) = i - floor(i/phi) (0, 1, 1, 2, 2, 2, 3, 3, 4, ...), and its first 36 antidiagonal terms are the entry's data. - The entry's FORMULA with b = A005206 is wrong for every row i >= 4: it gives A(4,1) = 6, the data have 7. With b(i) = i - floor(i/phi) in place of A005206 it is correct. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A132827). - _<Name>_, <Mon DD YYYY>

### [A134002](https://oeis.org/A134002): n(n+5) = a(a+5) + b(b+5) is solvable iff n^2 + (n+5)^2 is composite

- Problem: [OEIS-A134002](OEIS/A134002/README.md) (proved, partly-known). Lean: Lean proof, [`A134002_mathlib.lean`](OEIS/A134002/A134002_mathlib.lean).
- Prior art: Sierpinski proved the +1 analogue; the +5 version (and its converse) is not stated anywhere found, though the method is the same.
- Draft comment:

  > The conjecture is true, and so is its converse: n(n+5) = a(a+5) + b(b+5) has a solution in positive integers iff M = n^2 + (n+5)^2 is composite (cf. A134003). Since 2M = (2n+5)^2 + 5^2, a solution is a representation 2M = X^2 + Y^2 with X = 2a+5, Y = 2b+5 odd and >= 7; for prime M the only representation is (2n+5)^2 + 5^2 (b = 0), while a composite M has a second one (for 5 | n, n = 5m, take a = 3m+1, b = 4m-2). This is the analog of Sierpinski's result for x(x+1) + y(y+1) = z(z+1) (see A012132). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A134002.

### [A134003](https://oeis.org/A134003): n(n+5) = a(a+5) + b(b+5) has no positive solution when n^2 + (n+5)^2 is prime

- Problem: [OEIS-A134003](OEIS/A134003/README.md) (proved, partly-known). Lean: Lean proof, [`A134003_mathlib.lean`](OEIS/A134003/A134003_mathlib.lean).
- Prior art: As A134002; the literal 'in integers' reading is false (b = 0), which nobody has noted.
- Draft comment:

  > The conjecture is true for positive a, b, the reading matching A134002, but false as literally worded ("in integers"), since a = n, b = 0 is always a solution. If M = n^2 + (n+5)^2 is prime, then 2M = (2n+5)^2 + 5^2 is the only representation of 2M as a sum of two squares (by uniqueness for the prime M), and a positive solution would give another one, 2M = (2a+5)^2 + (2b+5)^2. See A134002 for the converse. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A134003.

### [A152718](https://oeis.org/A152718): inverse Motzkin transform of A054393

- Problem: [OEIS-A152718](OEIS/A152718/README.md) (proved, new). Lean: Lean proof, [`A152718_mathlib.lean`](OEIS/A152718/A152718_mathlib.lean).
- Prior art: No statement of the transform found; the excursion decomposition and Lean proof are ours. Barcucci et al. 2000 not read.
- Draft comment:

  > The conjecture is true: A054393(x) = A152718(x M(x)) as formal power series, so A152718 is the inverse Motzkin transform of A054393. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A152718). - _<Name>_, <Mon DD YYYY>

### [A156833](https://oeis.org/A156833): for n > 1, a(n) = n iff n is prime

- Problem: [OEIS-A156833](OEIS/A156833/README.md) (proved, new). Lean: Lean proof, [`A156834_mathlib.lean`](OEIS/A156834/A156834_mathlib.lean).
- Prior art: Entry still says conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A156833). - _<Name>_, <Mon DD YYYY>

### [A156907](https://oeis.org/A156907): integer series

- Problem: [OEIS-A156907](OEIS/A156907/README.md) (proved, new). Lean: Lean proof, [`A156907_mathlib.lean`](OEIS/A183241/A156907_mathlib.lean).
- Prior art: Entries still say conjectured; standard tools (Dwork, necklace/Dold, Euler product), applications not found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A156907). - _<Name>_, <Mon DD YYYY>

### [A156908](https://oeis.org/A156908): integer series

- Problem: [OEIS-A156908](OEIS/A156908/README.md) (proved, new). Lean: Lean proof, [`A156907_mathlib.lean`](OEIS/A183241/A156907_mathlib.lean).
- Prior art: Entries still say conjectured; standard tools (Dwork, necklace/Dold, Euler product), applications not found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A156908). - _<Name>_, <Mon DD YYYY>

### [A157308](https://oeis.org/A157308): a(m) is odd iff m = 0 or m is a power of 2

- Problem: [OEIS-A157308](OEIS/A157308/README.md) (proved, new). Lean: Lean proof, [`A157308_mathlib.lean`](OEIS/A157308/A157308_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A157308). - _<Name>_, <Mon DD YYYY>

### [A157675](https://oeis.org/A157675): integer series

- Problem: [OEIS-A157675](OEIS/A157675/README.md) (proved, new). Lean: Lean proof, [`A157675_mathlib.lean`](OEIS/A183241/A157675_mathlib.lean).
- Prior art: Entries still say conjectured; standard tools (Dwork, necklace/Dold, Euler product), applications not found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A157675). - _<Name>_, <Mon DD YYYY>

### [A163138](https://oeis.org/A163138): exp(Σ (q^n + A)^n x^n/n) = A is an integer series for every integer q

- Problem: [OEIS-A163138](OEIS/A163138/README.md) (proved, new). Lean: Lean proof, [`A163138_mathlib.lean`](OEIS/A163138/A163138_mathlib.lean).
- Prior art: Entry still says conjecture.
- Draft comment:

  > The conjecture is true: for every integer q (q = 0: Catalan numbers, q = 1: large Schröder numbers, q = 2: A163138). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A163138). - _<Name>_, <Mon DD YYYY>

### [A163921](https://oeis.org/A163921): G(x) = exp(Σ G(L(n) x)^n x^n/n) is integral whenever exp(Σ L(n) x^n/n) is

- Problem: [OEIS-A163921](OEIS/A163921/README.md) (proved, new). Lean: Lean proof, [`A163921_mathlib.lean`](OEIS/A163921/A163921_mathlib.lean).
- Prior art: Entry still says conjecture.
- Draft comment:

  > The conjecture is true: for every such L. A163921 (L = σ, with exp(Σ σ(n) x^n/n) = Π_k (1 - x^k)^(-1)) and A157675 (L = 2^n) are special cases. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A163921). - _<Name>_, <Mon DD YYYY>

### [A164754](https://oeis.org/A164754): a(n) = 4n^2 - 11n + 5 for n >= 3

- Problem: [OEIS-A164754](OEIS/A164754/README.md) (proved, new). Lean: Lean proof, [`A164754_mathlib.lean`](OEIS/A164754/A164754_mathlib.lean).
- Prior art: No proof found; the interval characterisation and family count are ours.
- Draft comment:

  > The conjecture is true: a(n) = 4n^2 - 11n + 5 for every n >= 3. The recurrence and the g.f. follow. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A164754). - _<Name>_, <Mon DD YYYY>

### [A165460](https://oeis.org/A165460): Jacobi-bridge conjecture

- Problem: [OEIS-A165460](OEIS/A165460/README.md) (proved, partly-known). Lean: Lean proof, [`A165463_mathlib.lean`](OEIS/A165463/A165463_mathlib.lean).
- Prior art: Prime case follows from classical class-number formulas; the Jacobi-symbol (composite m) elementary proof and Lean proof are ours.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165460). - _<Name>_, <Mon DD YYYY>

### [A165462](https://oeis.org/A165462): Jacobi-bridge conjecture

- Problem: [OEIS-A165462](OEIS/A165462/README.md) (proved, partly-known). Lean: Lean proof, [`A165463_mathlib.lean`](OEIS/A165463/A165463_mathlib.lean).
- Prior art: Prime case follows from classical class-number formulas; the Jacobi-symbol (composite m) elementary proof and Lean proof are ours.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165462). - _<Name>_, <Mon DD YYYY>

### [A165463](https://oeis.org/A165463): Jacobi-bridge heights at the 1/3 and 1/2 points

- Problem: [OEIS-A165463](OEIS/A165463/README.md) (proved, partly-known). Lean: Lean proof, [`A165463_mathlib.lean`](OEIS/A165463/A165463_mathlib.lean).
- Prior art: Prime case follows from classical class-number formulas; the Jacobi-symbol (composite m) elementary proof and Lean proof are ours.
- Draft comment:

  > The conjecture is true: All three conjectures are true. With m = 12n+7, B = Sum_{i <= (m-1)/3} J(i, m) and A = Sum_{i <= (m-1)/2} J(i, m): B = 2A if m = 7 (mod 24) (n even) and 3B = 2A if m = 19 (mod 24) (n odd). So B = 0 iff A = 0, which gives A165462 and A165463. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165463). - _<Name>_, <Mon DD YYYY>

### [A165940](https://oeis.org/A165940): integer series

- Problem: [OEIS-A165940](OEIS/A165940/README.md) (proved, new). Lean: Lean proof, [`A165940_mathlib.lean`](OEIS/A183241/A165940_mathlib.lean).
- Prior art: Entries still say conjectured; standard tools (Dwork, necklace/Dold, Euler product), applications not found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165940). - _<Name>_, <Mon DD YYYY>

### [A166102](https://oeis.org/A166102): a(n) = 3·A166103(n)

- Problem: [OEIS-A166102](OEIS/A166102/README.md) (proved, new). Lean: Lean proof, [`A166103_mathlib.lean`](OEIS/A166103/A166103_mathlib.lean).
- Prior art: Elementary character argument; not found written.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166102). - _<Name>_, <Mon DD YYYY>

### [A166103](https://oeis.org/A166103): odd k with k ∤ Σ{i ≤ k : J(i,k) = 1} are exactly 3·m², m ∈ A166104

- Problem: [OEIS-A166103](OEIS/A166103/README.md) (proved, new). Lean: Lean proof, [`A166103_mathlib.lean`](OEIS/A166103/A166103_mathlib.lean).
- Prior art: Elementary character argument; not found written.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166103). - _<Name>_, <Mon DD YYYY>

### [A166268](https://oeis.org/A166268): Jacobi-bridge height identity for m = 12n+7

- Problem: [OEIS-A166268](OEIS/A166268/README.md) (proved, partly-known). Lean: Lean proof, [`A166273_mathlib.lean`](OEIS/A166273/A166273_mathlib.lean).
- Prior art: For prime m the identities follow from classical class-number formulas for partial sums of odd real characters (Berndt 1976, Johnson-Mitchell 1977, Hudson-Williams 1982; exact /6 formula not read here). Composite and non-squarefree m covered by the elementary route here.
- Draft comment:

  > The conjecture is true: Proved with A166273, A166271, A166270, A166269 and A166268 in [`../A166273/`](../A166273/README.md); the Lean theorem for this entry is `A166268_main` in [`../A166273/A166273_mathlib.lean`](../A166273/A166273_mathlib.lean). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166268). - _<Name>_, <Mon DD YYYY>

### [A166269](https://oeis.org/A166269): Jacobi-bridge height identity for m = 12n+7

- Problem: [OEIS-A166269](OEIS/A166269/README.md) (proved, partly-known). Lean: Lean proof, [`A166273_mathlib.lean`](OEIS/A166273/A166273_mathlib.lean).
- Prior art: For prime m the identities follow from classical class-number formulas for partial sums of odd real characters (Berndt 1976, Johnson-Mitchell 1977, Hudson-Williams 1982; exact /6 formula not read here). Composite and non-squarefree m covered by the elementary route here.
- Draft comment:

  > The conjecture is true: Proved with A166273, A166271, A166270, A166269 and A166268 in [`../A166273/`](../A166273/README.md); the Lean theorem for this entry is `A166269_main` in [`../A166273/A166273_mathlib.lean`](../A166273/A166273_mathlib.lean). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166269). - _<Name>_, <Mon DD YYYY>

### [A166270](https://oeis.org/A166270): Jacobi-bridge height identity for m = 12n+7

- Problem: [OEIS-A166270](OEIS/A166270/README.md) (proved, partly-known). Lean: Lean proof, [`A166273_mathlib.lean`](OEIS/A166273/A166273_mathlib.lean).
- Prior art: For prime m the identities follow from classical class-number formulas for partial sums of odd real characters (Berndt 1976, Johnson-Mitchell 1977, Hudson-Williams 1982; exact /6 formula not read here). Composite and non-squarefree m covered by the elementary route here.
- Draft comment:

  > The conjecture is true: Proved with A166273, A166271, A166270, A166269 and A166268 in [`../A166273/`](../A166273/README.md); the Lean theorem for this entry is `A166270_main` in [`../A166273/A166273_mathlib.lean`](../A166273/A166273_mathlib.lean). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166270). - _<Name>_, <Mon DD YYYY>

### [A166271](https://oeis.org/A166271): Jacobi-bridge height identity for m = 12n+7

- Problem: [OEIS-A166271](OEIS/A166271/README.md) (proved, partly-known). Lean: Lean proof, [`A166273_mathlib.lean`](OEIS/A166273/A166273_mathlib.lean).
- Prior art: For prime m the identities follow from classical class-number formulas for partial sums of odd real characters (Berndt 1976, Johnson-Mitchell 1977, Hudson-Williams 1982; exact /6 formula not read here). Composite and non-squarefree m covered by the elementary route here.
- Draft comment:

  > The conjecture is true: Proved with A166273, A166271, A166270, A166269 and A166268 in [`../A166273/`](../A166273/README.md); the Lean theorem for this entry is `A166271_main` in [`../A166273/A166273_mathlib.lean`](../A166273/A166273_mathlib.lean). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166271). - _<Name>_, <Mon DD YYYY>

### [A166273](https://oeis.org/A166273): Jacobi-bridge heights at m/6, m/3, m/2 for m = 12n+7

- Problem: [OEIS-A166273](OEIS/A166273/README.md) (proved, partly-known). Lean: Lean proof, [`A166273_mathlib.lean`](OEIS/A166273/A166273_mathlib.lean).
- Prior art: For prime m the identities follow from classical class-number formulas for partial sums of odd real characters (Berndt 1976, Johnson-Mitchell 1977, Hudson-Williams 1982; exact /6 formula not read here). Composite and non-squarefree m covered by the elementary route here.
- Draft comment:

  > The conjecture is true: All true: for m ≡ 7 (mod 24), H(1/3) = 2H(1/6) and H(1/2) = H(1/6); for m ≡ 19 (mod 24), H(1/2) = −3H(1/6) and H(1/3) = −2H(1/6). This holds for every m in these classes, squarefree or not. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166273). - _<Name>_, <Mon DD YYYY>

### [A166407](https://oeis.org/A166407): A166406(n)/(2n+1) is an integer except on A166101, where its denominator is 3

- Problem: [OEIS-A166407](OEIS/A166407/README.md) (proved, new). Lean: paper proof.
- Prior art: Classical tools; the application and the explicit description of A166101 are ours.
- Draft comment:

  > The conjecture is true: Write N = N'·m^2 with N' squarefree and B = −A166406(n)/N = (1/N) Σ_{i≤N} i·J(i,N). Then B is an integer unless N' = 3 and every prime p ≠ 3 dividing m is ≡ 2 (mod 3); in that case B = −2^w/3 (w = number of such primes) and n ∈ A166101. Whenever B is an integer, A166100(n)/N is an integer, so n ∉ A166101. Hence A166101 = {n : 2n+1 = 3m^2, all prime factors p ≠ 3 of m are ≡ 2 (mod 3)} (= 1, 13, 37, 121, 181, ...). (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166407). - _<Name>_, <Mon DD YYYY>

### [A170941](https://oeis.org/A170941): involutions without adjacent transpositions, proportion → 1/e

- Problem: [OEIS-A170941](OEIS/A170941/README.md) (proved, new). Lean: Lean proof, [`A170941_mathlib.lean`](OEIS/A170941/A170941_mathlib.lean).
- Prior art: Companion conjecture A217876 (Poisson(1) limit of adjacent transpositions in involutions) open; same method likely applies.
- Draft comment:

  > The conjecture is true: a(n)/I(n) → e^(−1), where I(n) = A000085(n) is the number of involutions of [n]. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A170941). - _<Name>_, <Mon DD YYYY>

### [A174470](https://oeis.org/A174470): integer series

- Problem: [OEIS-A174470](OEIS/A174470/README.md) (proved, new). Lean: Lean proof, [`A174470_mathlib.lean`](OEIS/A183241/A174470_mathlib.lean).
- Prior art: Entries still say conjectured; standard tools (Dwork, necklace/Dold, Euler product), applications not found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A174470). - _<Name>_, <Mon DD YYYY>

### [A174846](https://oeis.org/A174846): |a(n)/n!|^(-1/n) tends to pi/4 = 0.7853...

- Problem: [OEIS-A174846](OEIS/A174846/README.md) (proved, partly-known). Lean: paper proof.
- Prior art: Value known; proof of existence of the limit (even-n amplitude) written here.
- Draft comment:

  > The conjecture is true: the limit exists and equals pi/4 = 0.78539... < 0.8. Asymptotically a(n)/n! = -pi (4/pi)^n Re(i^(1-n)) / (n log^2 n) (1 + o(1)) for odd n, and |a(n)/n!| is of exact order (4/pi)^n / (n^2 log^2 n) for even n. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A174846). - _<Name>_, <Mon DD YYYY>

### [A176827](https://oeis.org/A176827): the q-analogue a(n,q) is an integer for every positive integer q

- Problem: [OEIS-A176827](OEIS/A176827/README.md) (proved, new). Lean: Lean proof, [`A176827_mathlib.lean`](OEIS/A176827/A176827_mathlib.lean).
- Prior art: Entry still says conjecture.
- Draft comment:

  > The conjecture is true: a(n,q) ∈ ℤ for all n ≥ 0 and integers q ≥ 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A176827). - _<Name>_, <Mon DD YYYY>

### [A176948](https://oeis.org/A176948): every n >= 4 except 6 has an n-gonal number that is not k-gonal for 3 <= k < n

- Problem: [OEIS-A176948](OEIS/A176948/README.md) (proved, new). Lean: Lean proof, [`A176948_mathlib.lean`](OEIS/A176948/A176948_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A176948). - _<Name>_, <Mon DD YYYY>

### [A180654](https://oeis.org/A180654): Σ log(Σ_k C(n,k)^p x^k)^n/(n! n^n) is an integer e.g.f. (Conjectures 1-3)

- Problem: [OEIS-A180654](OEIS/A180654/README.md) (proved, new). Lean: Lean proof, [`A180654_mathlib.lean`](OEIS/A180654/A180654_mathlib.lean).
- Prior art: Entry still says conjecture.
- Draft comment:

  > The conjecture is true: All three conjectures are true. More generally: if P_n ∈ 1 + xℤ[x] and n divides k·[x^k]P_n for all k, then Σ_n log(P_n)^n/(n! n^n) has integer e.g.f. coefficients. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A180654). - _<Name>_, <Mon DD YYYY>

### [A180710](https://oeis.org/A180710): sigma(n) | a(n) fails at n = 64

- Problem: [OEIS-A180710](OEIS/A180710/README.md) (disproved, new). Lean: paper proof.
- Prior art: No counterexample recorded.
- Draft comment:

  > The conjecture is false: sigma(n) | a(n) holds for 1 <= n <= 63, but sigma(64) = 127 and a(64) = 43 (mod 127). a(64) has 658 digits. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A180710). - _<Name>_, <Mon DD YYYY>

### [A181070](https://oeis.org/A181070): integer series

- Problem: [OEIS-A181070](OEIS/A181070/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181070). - _<Name>_, <Mon DD YYYY>

### [A181074](https://oeis.org/A181074): integer series

- Problem: [OEIS-A181074](OEIS/A181074/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181074). - _<Name>_, <Mon DD YYYY>

### [A181076](https://oeis.org/A181076): integer series

- Problem: [OEIS-A181076](OEIS/A181076/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181076). - _<Name>_, <Mon DD YYYY>

### [A181078](https://oeis.org/A181078): integer series

- Problem: [OEIS-A181078](OEIS/A181078/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181078). - _<Name>_, <Mon DD YYYY>

### [A181080](https://oeis.org/A181080): integer series

- Problem: [OEIS-A181080](OEIS/A181080/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181080). - _<Name>_, <Mon DD YYYY>

### [A181082](https://oeis.org/A181082): integer series

- Problem: [OEIS-A181082](OEIS/A181082/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181082). - _<Name>_, <Mon DD YYYY>

### [A181084](https://oeis.org/A181084): integer series

- Problem: [OEIS-A181084](OEIS/A181084/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181084). - _<Name>_, <Mon DD YYYY>

### [A181316](https://oeis.org/A181316): exp(Σ (q-1)((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series for every q > 1

- Problem: [OEIS-A181316](OEIS/A181316/README.md) (proved, new). Lean: Lean proof, [`A181316_mathlib.lean`](OEIS/A181316/A181316_mathlib.lean).
- Prior art: Entry still says conjecture.
- Draft comment:

  > The conjecture is true: for every integer q >= 2. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A181316). - _<Name>_, <Mon DD YYYY>

### [A182372](https://oeis.org/A182372): sets with perimeter n and two-sort partitions are equinumerous

- Problem: [OEIS-A182372](OEIS/A182372/README.md) (proved, new). Lean: paper proof, [`A182372_mathlib.lean`](OEIS/A182372/A182372_mathlib.lean).
- Prior art: No proof found; the shape decomposition and reduction to the Durfee-rectangle q-identity are ours.
- Draft comment:

  > The conjecture is true: for every n ≥ 0, the number of nonempty finite sets S ⊆ ℕ with perimeter n equals the number of two-sort partitions of n. Hence a(n) = (two-sort partitions of n) for n ≥ 1, a(0) = 2, and a(n) = A227134(n) + A227135(n) for all n ≥ 0. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182372). - _<Name>_, <Mon DD YYYY>

### [A182963](https://oeis.org/A182963): integer series

- Problem: [OEIS-A182963](OEIS/A182963/README.md) (proved, new). Lean: Lean proof, [`A183241_mathlib.lean`](OEIS/A183241/A183241_mathlib.lean).
- Prior art: Entries still say conjectured; standard tools (Dwork, necklace/Dold, Euler product), applications not found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182963). - _<Name>_, <Mon DD YYYY>

### [A183128](https://oeis.org/A183128): integer series

- Problem: [OEIS-A183128](OEIS/A183128/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A183128). - _<Name>_, <Mon DD YYYY>

### [A183129](https://oeis.org/A183129): binomial-power Hanna series are integer series

- Problem: [OEIS-A183129](OEIS/A183129/README.md) (proved, new). Lean: Lean proof, [`A183129_mathlib.lean`](OEIS/A183129/A183129_mathlib.lean).
- Prior art: Entries still say conjecture.
- Draft comment:

  > The conjecture is true: All nine are integer series. The argument also explains the entries' remarks that the variants with exponent k, n-k, k^2 are not integral (they violate condition (E2) below). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A183129). - _<Name>_, <Mon DD YYYY>

### [A183241](https://oeis.org/A183241): seven Hanna series are integer series

- Problem: [OEIS-A183241](OEIS/A183241/README.md) (proved, new). Lean: Lean proof, [`A183241_mathlib.lean`](OEIS/A183241/A183241_mathlib.lean).
- Prior art: Entries still say conjectured; standard tools (Dwork, necklace/Dold, Euler product), applications not found.
- Draft comment:

  > The conjecture is true: All seven are integer series (every coefficient is an integer). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A183241). - _<Name>_, <Mon DD YYYY>

### [A195608](https://oeis.org/A195608): first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts

- Problem: [OEIS-A195608](OEIS/A195608/README.md) (proved, new). Lean: Lean proof, [`A195608_mathlib.lean`](OEIS/A195608/A195608_mathlib.lean).
- Prior art: No proof found; elementary closed form via Thue-Morse, proved in Lean. Evil case m = 1 (series {1}) excluded from 3) since A(0) does not exist.
- Draft comment:

  > The conjecture is true: All three conjectures are true. Closed form, with t the Thue–Morse sequence (A010060): S = {2j+1 : t(j) = 0} ∪ {2j+2 : t(j) = t(j+1) = 0}. Sharper form of 3): for m ∈ S, m ≥ 2, A(m+1) − A(m−1) is 5 if m starts its series and 4 otherwise. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A195608). - _<Name>_, <Mon DD YYYY>

### [A195609](https://oeis.org/A195609): first differences 1, 4, 6, runs of length 1 or 3, and A(m+1) − A(m−1) = 5 at run starts

- Problem: [OEIS-A195609](OEIS/A195609/README.md) (proved, new). Lean: Lean proof, [`A195608_mathlib.lean`](OEIS/A195608/A195608_mathlib.lean).
- Prior art: No proof found; elementary closed form via Thue-Morse, proved in Lean. Evil case m = 1 (series {1}) excluded from 3) since A(0) does not exist.
- Draft comment:

  > The conjecture is true: All three conjectures are true. Closed form, with t the Thue–Morse sequence: S = {2j+1 : t(j) = 1} ∪ {2j+2 : t(j) = t(j+1) = 1}. For m ∈ S, A(m+1) − A(m−1) is 5 if m starts its series and 4 otherwise. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A195609). - _<Name>_, <Mon DD YYYY>

### [A195825](https://oeis.org/A195825): plateaus of the columns of the generalized pentagonal-number array

- Problem: [OEIS-A195825](OEIS/A195825/README.md) (proved, new). Lean: Lean proof, [`A195825_mathlib.lean`](OEIS/A195825/A195825_mathlib.lean).
- Prior art: Ingredients classical (triple product); plateau structure and level independence not found.
- Draft comment:

  > The conjecture is true: With m = k + 2: - T(n+1, k) = T(n, k) exactly for A(m+1) ≤ n ≤ (A+1)(m−1) − 2, A ≥ 0. So the plateaus are n ∈ [A(m+1), (A+1)(m−1) − 1], of length k + 1 − 2A, for A = 0, 1, ... while k + 1 − 2A ≥ 2, and the column increases strictly elsewhere. - The level of plateau A is T(A(k+3), k), the same for every k ≥ 2A + 1; so it is A210843(A+1). It equals Σ_{B ≤ A} p₃(B), with p₃ the 3-colored partition numbers A000716 (this also answers A210843's question: it is the Euler transform of 4, 3, 3, 3, ...). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A195825). - _<Name>_, <Mon DD YYYY>

### [A202150](https://oeis.org/A202150): the odd coefficients of the q-analog of π/2 sit exactly at 3n(n+1)

- Problem: [OEIS-A202150](OEIS/A202150/README.md) (proved, new). Lean: Lean proof, [`A202150_mathlib.lean`](OEIS/A202150/A202150_mathlib.lean).
- Prior art: No proof found; identity (*), the Bailey pair and the finite identities are ours.
- Draft comment:

  > The conjecture is true: With (a;q)_n = (1−a)(1−aq)···(1−aq^{n−1}), the g.f. of A202146 is A(q) = Σ_{n≥0} q^n (q;q)_n/(q;q²)_{n+1}, and (∗) Σ_{n≥0} (−q)^n (−q;q)_n/(q;q²)_{n+1} = Σ_{m≥0} (−1)^m q^{3m(m+1)}. Reducing mod 2 ((q;q)_n ≡ (−q;q)_n, q^n ≡ (−q)^n, and 1/(q;q²)_{n+1} has integer coefficients) gives A(q) ≡ Σ_m q^{3m(m+1)} (mod 2): A202146(k) is odd iff k = 3m(m+1), so A202150 lists exactly the odd terms. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A202150). - _<Name>_, <Mon DD YYYY>

### [A209860](https://oeis.org/A209860): A054429 commutes with the permutation A209861/A209862

- Problem: [OEIS-A209860](OEIS/A209860/README.md) (proved, new). Lean: Lean proof, [`A209860_mathlib.lean`](OEIS/A209860/A209860_mathlib.lean).
- Prior art: First proof; Lean proof against the entry's definitions.
- Draft comment:

  > The conjecture is true: A209861(A054429(n)) = A054429(A209861(n)) and A209862(A054429(n)) = A054429(A209862(n)) for all n ≥ 1, and for i ≥ 1, i is a fixed point iff A054429(i) is. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A209860). - _<Name>_, <Mon DD YYYY>

### [A209861](https://oeis.org/A209861): A054429 commutes with the permutation A209861/A209862

- Problem: [OEIS-A209861](OEIS/A209861/README.md) (proved, new). Lean: Lean proof, [`A209860_mathlib.lean`](OEIS/A209860/A209860_mathlib.lean).
- Prior art: First proof; Lean proof against the entry's definitions.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A209861). - _<Name>_, <Mon DD YYYY>

### [A209862](https://oeis.org/A209862): A054429 commutes with the permutation A209861/A209862

- Problem: [OEIS-A209862](OEIS/A209862/README.md) (proved, new). Lean: Lean proof, [`A209860_mathlib.lean`](OEIS/A209860/A209860_mathlib.lean).
- Prior art: First proof; Lean proof against the entry's definitions.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A209862). - _<Name>_, <Mon DD YYYY>

### [A210445](https://oeis.org/A210445): a(n) < n for n > 1 and a(n) < n/2 for n > 47 (least k with kn practical)

- Problem: [OEIS-A210445](OEIS/A210445/README.md) (proved, new). Lean: Lean proof, [`A210445_mathlib.lean`](OEIS/A210445/A210445_mathlib.lean).
- Prior art: No proof found. The argument uses Stewart-Sierpinski plus an explicit practical family {2^a*105, 2^a*165} and a finite check for 47 < p < 2881; not deep but more than a line.
- Draft comment:

  > The conjecture is true. By the Stewart-Sierpinski criterion, if n is composite with largest prime factor P, then k = 2^t with 2^t < P <= 2^(t+1) makes kn practical and k < P <= n/2; for prime p the same k gives a(p) < p. For primes p > 47, a(p) < p/2 follows from the practical family k = 2^a*105, 2^a*165 (for p > 11, kp is practical iff p <= 1 + sigma(k)) for large p and a direct check of the remaining primes. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A210445.

### [A210456](https://oeis.org/A210456): periods of digital roots of n-step Fibonacci numbers (divisibility by 3, Helenius's closed forms)

- Problem: [OEIS-A210456](OEIS/A210456/README.md) (proved, new). Lean: paper proof.
- Prior art: Uses classical tools (Gauss trace congruence, Singer difference sets).
- Draft comment:

  > The conjecture is true: Both conjectures are true. With P(n) the period mod 3: - a(n) = 3·P(n) whenever 3 ∤ P(n); in all cases 3 | a(n) for n ≥ 2. - P(3^m − 1) = 3^{2m} − 1 and P(3^m) = 3^{2m} + 3^m + 1, so a(3^m − 1) = 3^{2m+1} − 3 and a(3^m) = 3^{2m+1} + 3^{m+1} + 3. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A210456). - _<Name>_, <Mon DD YYYY>

### [A212392](https://oeis.org/A212392): n divides a(n) for A(x) = (x + A(A(x)))^2

- Problem: [OEIS-A212392](OEIS/A212392/README.md) (proved, new). Lean: Lean proof, [`A212425_mathlib.lean`](OEIS/A212425/A212425_mathlib.lean).
- Prior art: Abbondandolo-Majer (2026) mention both sequences (Remark 7.2) but not the divisibility.
- Draft comment:

  > The conjecture is true: Proved together with A212425 and the general form for every exponent b ≥ 2 in [`../A212425/`](../A212425/README.md); the b = 2 case is the Lean theorem `A212392_b2` in [`../A212425/A212425_mathlib.lean`](../A212425/A212425_mathlib.lean). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A212392). - _<Name>_, <Mon DD YYYY>

### [A212425](https://oeis.org/A212425): ((b−1)(n−1)+1) divides the coefficients of A(x) = (x + A(A(x)))^b

- Problem: [OEIS-A212425](OEIS/A212425/README.md) (proved, new). Lean: Lean proof, [`A212425_mathlib.lean`](OEIS/A212425/A212425_mathlib.lean).
- Prior art: Abbondandolo-Majer (2026) mention both sequences (Remark 7.2) but not the divisibility.
- Draft comment:

  > The conjecture is true: for every b ≥ 2 (so both conjectures and the general form). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A212425). - _<Name>_, <Mon DD YYYY>

### [A212843](https://oeis.org/A212843): Carmichael numbers (30a+1)(30b+1)(30c+11) do exist

- Problem: [COM-C044](COM/C044/README.md) (trivial or misstated, new). Lean: Lean proof, [`C044_mathlib.lean`](COM/C044/C044_mathlib.lean).
- Prior art: Counterexample not found stated; it sits in the entry's own b-file.
- Draft comment:

  > The "in other words" statement (no such C = (30a+1)*(30b+1)*(30c+11)) is false when the three factors may be composite, as the conjecture allows: the Carmichael number 1044430736441 = 41*191*281*521*911 = 7831*146401*911 (a(848)) has all prime factors == 11 (mod 30), and 7831 == 146401 == 1, 911 == 11 (mod 30). For three prime factors the statement is true, since a prime factor == 1 (mod 30) forces C == 1 (mod 3), while (30a+1)*(30b+1)*(30c+11) == 2 (mod 3). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/COM/C044.

### [A212843](https://oeis.org/A212843): Carmichael numbers with prime factors ≡ 1 (mod 10)

- Problem: [OEIS-A212843](OEIS/A212843/README.md) (proved, partly-known). Lean: Lean proof, [`A212843_mathlib.lean`](OEIS/A212843/A212843_mathlib.lean).
- Prior art: Conjecture (1) is already proved in the entry. Conjecture (2) (true) and the counterexample 1044430736441 to the 'in other words' sentence are not in the entry or elsewhere found.
- Draft comment:

  > Conjecture (2) is true but its "in other words" restatement is false. The prime factors are == 1 or 11 (mod 30); grouping them into three blocks gives an even number of blocks == 11 (mod 30) when C == 1 (mod 30), and when C == 11 (mod 30) all primes are == 11 (mod 30) and odd in number, so one of the three listed forms always exists. The restatement holds for three prime factors but fails for C = 1044430736441 = 41*191*281*521*911 = 7831*146401*911, with 7831 == 146401 == 1 and 911 == 11 (mod 30); conjecture (1) follows from Korselt's criterion, as noted above. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A212843.

### [A214074](https://oeis.org/A214074): a(n) = 3 is not the residue class n ≡ 121 (mod 330)

- Problem: [OEIS-A214074](OEIS/A214074/README.md) (disproved, new). Lean: Lean (partial), [`A214074_mathlib.lean`](OEIS/A214074/A214074_mathlib.lean).
- Prior art: No disproof found.
- Draft comment:

  > The conjecture is false: in both directions. - n₁ = 3438721 = 330·10421 − 209 has a(n₁) = 4 (Lean proves a(n₁) ≥ 4). - n₂ = 1186095 ≡ 75 (mod 330) has a(n₂) = 3 (Lean proves a(n₂) ≥ 3; the gcd for m = 3 is from PARI/GP). The conjecture holds for all n ≤ 40000 (`certificate/scan.out`). (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A214074). - _<Name>_, <Mon DD YYYY>

### [A214449](https://oeis.org/A214449): A214449 is not A118168 with two 1s deleted (first mismatch n = 188)

- Problem: [OEIS-A214449](OEIS/A214449/README.md) (disproved, new). Lean: Lean proof, [`A214449_mathlib.lean`](OEIS/A214449/A214449_mathlib.lean).
- Prior art: Counterexample n = 188 (A214449(188) = 159, A118168(189) = 158) not found anywhere.
- Draft comment:

  > The conjecture (A214449(n) = A118168(n+1)) is false: a(188) = 159, since 158^158 < 188! <= 159^159, but A118168(189) = 158, since 189! lies between 158^158 and 159^159 and is nearer to 158^158. There are 24 mismatches for n <= 1500 (188, 248, 271, 310, ...). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A214449.

### [A215944](https://oeis.org/A215944): Exceptions are not only 5461(42k - 13)

- Problem: [COM-C032](COM/C032/README.md) (disproved, new). Lean: Lean proof, [`C032_mathlib.lean`](COM/C032/C032_mathlib.lean).
- Prior art: Counterexample 3048841 not found stated; A215944 still lists the conjecture.
- Draft comment:

  > The conjecture is false: 3048841 = 61*151*331 is a Poulet number divisible by the smaller Poulet number 49981 = 151*331 and not a multiple of 5461, and it is not of the form p((m+1)p - m)((n+1)p - n) for any natural p, m, n (p^3 <= 3048841 and p | 3048841 force p = 61, and 49981 = (60m+61)(60n+61) has no solution). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/COM/C032.

### [A215944](https://oeis.org/A215944): Coman's 5461(42k − 13) exception claim is false (counterexample 3048841)

- Problem: [OEIS-A215944](OEIS/A215944/README.md) (disproved, new). Lean: Lean (partial), [`A215944_mathlib.lean`](OEIS/A215944/A215944_mathlib.lean).
- Prior art: Counterexample is a(36) of the entry's own b-file, just past the 30 terms Coman checked.
- Draft comment:

  > The conjecture is false: P = 3048841 = 61 · 151 · 331 is a base-2 Fermat pseudoprime, divisible by the smaller base-2 pseudoprime 49981 = 151 · 331, not divisible by 5461, and not of the form p((m+1)p − m)((n+1)p − n) for any natural p, m, n. It is the least counterexample (it is a(36) of A215944, just past the terms Coman checked). Below 10¹³ there are 56782 base-2 pseudoprimes divisible by a smaller one; 4042 of them fail the strict reading (p a prime factor, m, n ≥ 1) without being 5461(42k − 13), and 4019 fail even the broad reading. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A215944). - _<Name>_, <Mon DD YYYY>

### [A217482](https://oeis.org/A217482): tetrahedral numbers T with 3T/2 + 2 a power of 2

- Problem: [OEIS-A217482](OEIS/A217482/README.md) (proved, new). Lean: Lean (partial), [`A217396_mathlib.lean`](OEIS/A217396/A217396_mathlib.lean).
- Prior art: Not found in the literature; the conjecture is still stated in the entry.
- Draft comment:

  > The conjecture is true (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A217482). - _<Name>_, <Mon DD YYYY>

### [A219197](https://oeis.org/A219197): the square root of the A199033 g.f. has no coefficient = 3 (mod 4)

- Problem: [OEIS-A219197](OEIS/A219197/README.md) (proved, new). Lean: paper proof.
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true: Moreover a(n) is odd iff n is even and n AND 2n = 0 (no two adjacent 1-bits), and then a(n) = 1 (mod 4). (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A219197). - _<Name>_, <Mon DD YYYY>

### [A219431](https://oeis.org/A219431): a(odd) ≡ 2 and a(even) ≡ 0 (mod 4)

- Problem: [OEIS-A219431](OEIS/A219431/README.md) (proved, partly-known). Lean: Lean proof, [`A219431_mathlib.lean`](OEIS/A219431/A219431_mathlib.lean).
- Prior art: Input fact on overpartitions mod 4 is classical; the log-derivative congruence appears unproved before.
- Draft comment:

  > The conjecture is true: for all n ≥ 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A219431). - _<Name>_, <Mon DD YYYY>

### [A225919](https://oeis.org/A225919): the greedy harmonic-block sequence for f(k) = 1/(k+4) is linearly recurrent

- Problem: [OEIS-A225919](OEIS/A225919/README.md) (proved, new). Lean: paper proof.
- Prior art: Alekseyev (2022) gave an approximate ceiling formula; no proof of the recurrence found.
- Draft comment:

  > The conjecture is true: a(n) = 4a(n−1) − 4a(n−2) + 3a(n−3) − 2a(n−4) for all n ≥ 5 (a(1..4) = 1, 11, 40, 124). (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A225919). - _<Name>_, <Mon DD YYYY>

### [A227345](https://oeis.org/A227345): a distinct-part partition of n with boundary size k exists iff 3k^2/4 <= n

- Problem: [OEIS-A227345](OEIS/A227345/README.md) (proved, new). Lean: Lean proof, [`A227345_mathlib.lean`](OEIS/A227345/A227345_mathlib.lean).
- Prior art: Elementary; first proof and Lean proof here.
- Draft comment:

  > The conjecture is true: For n >= 1, T(n, k) > 0 iff k >= 1 and 3k^2 <= 4n. Equivalently, the least n with boundary size k is ceil(3k^2/4) (3m^2 for k = 2m, 3m^2 + 3m + 1 for k = 2m + 1), and every larger n also occurs. This also proves the formula a(n) = floor(2 sqrt(n/3)) of A227568 (largest boundary size for n), stated there without proof. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A227345). - _<Name>_, <Mon DD YYYY>

### [A227370](https://oeis.org/A227370): an involution made of the transpositions (2k-1, 2k), k in A061887

- Problem: [OEIS-A227370](OEIS/A227370/README.md) (proved, new). Lean: paper proof, [`A227370_mathlib.lean`](OEIS/A227370/A227370_mathlib.lean).
- Prior art: No proof found; argument ours, reusing the A227786 model.
- Draft comment:

  > The conjecture is true: Both conjectures are true. Let c(N) = A227368(N). For N ≥ 2, c(N) < c(N-1) exactly when N is even and s^2 ≤ N ≤ s^2 + 2s for some even s ≥ 2 (that is N = 2k, k in A061887, k ≥ 2), and the codes sorted increasingly are c(0), c(1), ... with exactly these adjacent pairs swapped. So A227370 is the product of the disjoint transpositions (2k-1, 2k), k in A061887, k ≥ 2, hence an involution. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A227370). - _<Name>_, <Mon DD YYYY>

### [A227786](https://oeis.org/A227786): positions of 2 in A227761

- Problem: [OEIS-A227786](OEIS/A227786/README.md) (proved, new). Lean: Lean proof, [`A227786_mathlib.lean`](OEIS/A227786/A227786_mathlib.lean).
- Prior art: No proof found; the pair/greedy analysis is ours.
- Draft comment:

  > The conjecture is true: For every N, A227761(N) = 2 exactly when N = a(n) for some n >= 2, i.e. N = j^2 - 2 with j >= 3 odd or N = j^2 - 3 with j >= 4 even. Also A227761(N) <= 2 for all N, which answers the question in A227761: there are no terms larger than 2. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A227786). - _<Name>_, <Mon DD YYYY>

### [A228095](https://oeis.org/A228095): Sun's Legendre-symbol determinants vanish on residue classes

- Problem: [OEIS-A228095](OEIS/A228095/README.md) (proved, partly-known). Lean: Lean proof, [`A228095_mathlib.lean`](OEIS/A228095/A228095_mathlib.lean).
- Prior art: Follows from Wu 2021 plus a standard fact; explicit kernel vector and Lean proof are ours.
- Draft comment:

  > The conjecture is true: - A228095: true. For p ≡ 5 (mod 6) the vector v_j = (j/p) is a nonzero kernel vector. - A225611: true (known: Krachun, Petrov, Sun, Vsemirnov 2020); reproved here with the kernel vector v_j = (j/p). - A226163: true (known: OEIS Open project, Adamczewski 2026, with a Lean proof); not redone here. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A228095). - _<Name>_, <Mon DD YYYY>

### [A228469](https://oeis.org/A228469): least c with an alternating trace (Kimberling)

- Problem: [OEIS-A228469](OEIS/A228469/README.md) (proved, new). Lean: Lean proof, [`A228469_mathlib.lean`](OEIS/A228469/A228469_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true: Both conjectures are true for all n. More generally, for every nonempty 0-1 word w the least such c is given by a backward greedy recursion. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A228469). - _<Name>_, <Mon DD YYYY>

### [A228471](https://oeis.org/A228471): least c whose trace begins 1010... (Kimberling)

- Problem: [OEIS-A228471](OEIS/A228471/README.md) (proved, new). Lean: Lean proof, [`A228469_mathlib.lean`](OEIS/A228469/A228469_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A228471). - _<Name>_, <Mon DD YYYY>

### [A229487](https://oeis.org/A229487): Finucane's lists for the iteration n → φ(n) + 1 are complete

- Problem: [NT-B41.5](NT/B41.5/README.md) (proved, new). Lean: Lean proof, [`B41_5_mathlib.lean`](NT/B41.5/B41_5_mathlib.lean).
- Prior art: Proves the terms a(3)=12 and a(4)=30 of OEIS A229487, which is labelled conjectural; worth an OEIS comment. Erdos #409 forum could not be read.
- Draft comment:

  > The conjectured terms a(3) = 12 and a(4) = 30 are correct: the numbers whose trajectory under n -> phi(n) + 1 ends at 5 are exactly 5, 8, 10, 12, and those ending at 7 are exactly 7, 9, 14, 15, 16, 18, 20, 24, 30. The set reaching a prime q is built from q by repeatedly solving phi(n) = m - 1; the inverse totient sets needed are phi^(-1)(4) = {5, 8, 10, 12}, phi^(-1)(6) = {7, 9, 14, 18} and phi^(-1)(8) = {15, 16, 20, 24, 30}, while 7, 9, 11, 13, 14, 15, 17, 19, 23, 29 are not totients. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/NT/B41.5.

## Immediate from a known theorem or short argument, still open in OEIS (120)

### [A004050](https://oeis.org/A004050): only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways

- Problem: [OEIS-A004050](OEIS/A004050/README.md) (proved, partly-known). Lean: Lean (partial), [`A004050_mathlib.lean`](OEIS/A004050/A004050_mathlib.lean).
- Prior art: Two representations give 3^d - 2^a = 3^b - 2^c; for b, c >= 1 Bennett's Thm 1.1 (Stroeker-Tijdeman) leaves only c in {1, -5, -13}, i.e. 11, 35, 259; the zero-exponent cases (5, 17) are elementary. So the result follows from the literature without Ellison; not stated for A085634 anywhere found.
- Draft comment:

  > The conjecture is true: only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways (see A085634). If 2^a + 3^b = 2^c + 3^d with a > c, lifting the exponent gives b < d <= a and |2^a - 3^d| <= 4a, and Ellison's 1971 bound |2^x - 3^y| > 2^x*e^(-x/10) (x >= 12, x not in {13, 14, 16, 19, 27}) forces a <= 27, leaving a finite search. The cases with b, c >= 1 (giving 11, 35, 259) also follow from the solution of Pillai's equation by Stroeker and Tijdeman (1982), in the form of M. A. Bennett (2003), Thm. 1.1. A partial Lean 4 verification (Ellison's 1971 bound outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A004050.

### [A005329](https://oeis.org/A005329): Product (2^i − 1) is the inverse binomial transform of A075272

- Problem: [OEIS-A005329](OEIS/A005329/README.md) (proved, new). Lean: Lean proof, [`A005329_mathlib.lean`](OEIS/A005329/A005329_mathlib.lean).
- Prior art: A075272 states the binomial-transform form as an unproved comment (Reshetnikov 2015); no proof found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A005329). - _<Name>_, <Mon DD YYYY>

### [A005408](https://oeis.org/A005408): one-coach primes and the first q odd numbers

- Problem: [OEIS-A005408](OEIS/A005408/README.md) (proved, partly-known). Lean: Lean proof, [`A005408_mathlib.lean`](OEIS/A005408/A005408_mathlib.lean).
- Prior art: The prime direction is the Coach theorem (phi(b) = 2ck, cited in A216371) plus counting; the converse (composite b excluded) is a short extra step. Same conjecture also in A216371.
- Draft comment:

  > Reading the top row as the set of entries of the coach of 1 (Hilton-Pedersen, see A216371), the conjecture is true. For odd b the map a -> odd part of (b - a) permutes the odd numbers below b/2 that are coprime to b, and the coaches are its cycles; there are exactly q odd numbers below b/2, all coprime to b when b is prime, while a composite odd b has an odd prime factor below b/2 that no coach contains. For prime b this also follows from the Coach theorem phi(b) = 2ck quoted in A216371. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A005408.

### [A005430](https://oeis.org/A005430): the inverse binomial transform of n·C(2n,n) is 2·A132894(n)

- Problem: [OEIS-A005430](OEIS/A005430/README.md) (proved, partly-known). Lean: Lean proof, [`A005430_mathlib.lean`](OEIS/A005430/A005430_mathlib.lean).
- Prior art: Implied at once by two printed but unproved e.g.f.s; no written proof found. Zudilin's printed formula in A132894 is off by a factor 2.
- Draft comment:

  > The conjecture is true: for every n ≥ 0: b(n) = 2·A132894(n) (0, 2, 8, 30, 104, 350, ...). Side finding: W. Zudilin's formula printed in A132894, "a(n) = Sum_{k=0..n} k*C(n,k)*C(2*k,k)*(-1)^(n-k)", is exactly the inverse binomial transform above, so it equals 2·A132894(n), not A132894(n) (n = 1 gives 2, not 1). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A005430). - _<Name>_, <Mon DD YYYY>

### [A008676](https://oeis.org/A008676): coefficients of 1/((1-x^3)(1-x^5)) as a floor formula

- Problem: [OEIS-A008676](OEIS/A008676/README.md) (proved, partly-known). Lean: Lean proof, [`A008676_mathlib.lean`](OEIS/A008676/A008676_mathlib.lean).
- Prior art: Akinari's formula in the entry equals Layman's by floor(2(n+3)/3) = n+2-ceil(n/3), ceil(n/3) = floor((n+2)/3), floor(3(n+3)/5) = n+1-floor(2n/5); so the entry already effectively contains it (Akinari's formula is not proved there).
- Draft comment:

  > The conjecture is true for all n >= 0: by the g.f., a(n) = a(n-3) + a(n-5) - a(n-8) for n >= 8, and the floor formula satisfies the same recurrence (it increases by 1 when n increases by 15) and agrees with a(n) for n = 0..7. It equals T. Akinari's formula a(n) = floor((2n+5)/5) - floor((n+2)/3) above by elementary floor identities. A proof formally verified in Lean 4 (starting from the recurrence implied by the g.f.) is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A008676.

### [A008749](https://oeis.org/A008749): a(n+2) is the first index where the minimal polyiamond perimeter reaches n + 4

- Problem: [OEIS-A008749](OEIS/A008749/README.md) (proved, new). Lean: Lean proof, [`A008749_mathlib.lean`](OEIS/A008749/A008749_mathlib.lean).
- Prior art: Immediate from the Harary-Harborth formula; no written proof found.
- Draft comment:

  > The conjecture is true: for every n >= 1, given the Harary-Harborth formula. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A008749). - _<Name>_, <Mon DD YYYY>

### [A025060](https://oeis.org/A025060): with signs allowed, i·j + j·k + k·i takes every integer

- Problem: [OEIS-A025060](OEIS/A025060/README.md) (trivial or misstated, new). Lean: Lean proof, [`A025060.lean`](OEIS/A025060/A025060.lean).
- Prior art: Two explicit families of triples; trivial.
- Draft comment:

  > The conjecture is true: (i, j) = (2, -1) gives ij + jk + ki = k - 2, which covers every integer except -3, -2, 0 (k not in {-1, 0, 2}), and (i, j) = (4, -3) gives k - 12, which covers -3, -2, 0 with k = 9, 10, 12. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A025060.

### [A025191](https://oeis.org/A025191): row half-sums of A025177 are first differences of A027914 and of A081673/2

- Problem: [OEIS-A025191](OEIS/A025191/README.md) (proved, new). Lean: Lean proof, [`A025191_mathlib.lean`](OEIS/A025191/A025191_mathlib.lean).
- Prior art: Follows quickly from the printed A027914(n) = (3^n + A002426(n))/2; no written proof found.
- Draft comment:

  > The conjecture is true: for every n ≥ 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A025191). - _<Name>_, <Mon DD YYYY>

### [A029795](https://oeis.org/A029795): k and k^3 with the same digits are not eventually all integers

- Problem: [OEIS-A029795](OEIS/A029795/README.md) (disproved, partly-known). Lean: Lean proof, [`A029795_mathlib.lean`](OEIS/A029795/A029795_mathlib.lean).
- Prior art: Corneth's 10^e + 1 argument in A029797 applies verbatim; not recorded in A029795.
- Draft comment:

  > The conjecture is false: it would make every integer >= a(N) a term, but for e >= 1, 10^e + 1 has digits {0, 1} while (10^e + 1)^3 = 10^(3e) + 3*10^(2e) + 3*10^e + 1 contains the digit 3. This is the argument of D. A. Corneth for the same conjecture in A029797. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A029795.

### [A051924](https://oeis.org/A051924): a(n) ≡ n + 2 (mod n^2) also holds at n = 16843^2

- Problem: [OEIS-A051924](OEIS/A051924/README.md) (disproved, partly-known). Lean: Lean proof, [`A051924_mathlib.lean`](OEIS/A051924/A051924_mathlib.lean).
- Prior art: McIntosh's fact plus the two-line equivalence a(n) == n+2 (mod n^2) iff C(2n-1,n-1) == 1 (mod n^2) gives the counterexample; nobody has connected it to A051924.
- Draft comment:

  > The "if" part is true (Wolstenholme's theorem for p >= 5, and a(3) = 14), but the conjecture is false: n = 16843^2 = 283686649 is composite and a(n) == n + 2 (mod n^2). Since a(n)*(2n-1) = binomial(2n-1,n-1)*(3n-2), a(n) == n + 2 (mod n^2) iff binomial(2n-1,n-1) == 1 (mod n^2), and for n = p^2 this reduces to binomial(2p-1,p-1) == 1 (mod p^4), i.e., p is a Wolstenholme prime; McIntosh (1995) showed that n = 16843^2 satisfies binomial(2n-1,n-1) == 1 (mod n^2). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A051924.

### [A054096](https://oeis.org/A054096): column 2 of A054090 is A006183 shifted right

- Problem: [OEIS-A054096](OEIS/A054096/README.md) (proved, partly-known). Lean: Lean proof, [`A054096_mathlib.lean`](OEIS/A054096/A054096_mathlib.lean).
- Prior art: Row-sum recurrence stated in A054091 without proof; with it the conjecture is two lines. No written proof or Lean proof found.
- Draft comment:

  > The conjecture is true: A054096(n) = A006183(n-1) for every n >= 2. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A054096). - _<Name>_, <Mon DD YYYY>

### [A054120b](https://oeis.org/A054120b): T(n,k) = A081577(n,k) − A081577(n−2,k−1)

- Problem: [OEIS-A054120b](OEIS/A054120b/README.md) (proved, new). Lean: Lean proof, [`A054120b_mathlib.lean`](OEIS/A054120b/A054120b_mathlib.lean).
- Prior art: A short induction once Hendel's recurrence is known; no written proof of the second conjecture found.
- Draft comment:

  > The conjecture is true: for all n, k (both sides 0 for k > n). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A054120b). - _<Name>_, <Mon DD YYYY>

### [A061002](https://oeis.org/A061002): denominator(H(p)/H(p−1)) / numerator(H(p−1)/p^2) = p^3

- Problem: [OEIS-A061002](OEIS/A061002/README.md) (proved, new). Lean: Lean proof, [`A061002_mathlib.lean`](OEIS/A061002/A061002_mathlib.lean).
- Prior art: Direct corollary of Wolstenholme's theorem; not stated anywhere found.
- Draft comment:

  > The conjecture is true for all primes p >= 5: write H(p-1) = a/b in lowest terms; by Wolstenholme's theorem p^2 | a and p does not divide b, so H(p)/H(p-1) = (pa + b)/(pa) and H(p-1)/p^2 = (a/p^2)/b are in lowest terms, and the ratio is pa/(a/p^2) = p^3. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A061002.

### [A074766](https://oeis.org/A074766): p(2n) − 2p(n) < 2n for all n

- Problem: [OEIS-A074766](OEIS/A074766/README.md) (proved, new). Lean: paper proof.
- Prior art: Follows in a few lines from Dusart (1999) plus a finite check; no source states it.
- Draft comment:

  > The conjecture is true: by Dusart's 1999 bounds p(k) <= k(log k + log log k - 0.9484) for k >= 39017 and p(k) >= k(log k + log log k - 1) for k >= 2, for n >= 19509 one gets p(2n) - 2p(n) <= 2n(log 2 + 0.0516 + log(1 + log 2/log n)) < 0.82*2n, and n < 19509 is checked directly. A proof is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A074766.

### [A075885](https://oeis.org/A075885): limit a(n)^(1/n) = L (geometric-mean constant)

- Problem: [OEIS-A075885](OEIS/A075885/README.md) (proved, new). Lean: Lean proof, [`A208060_mathlib.lean`](OEIS/A208060/A208060_mathlib.lean).
- Prior art: No proof found; short Riemann-sum argument.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A075885). - _<Name>_, <Mon DD YYYY>

### [A077739](https://oeis.org/A077739): a(n) = 0 exactly for n = 11, 17, 19

- Problem: [OEIS-A077739](OEIS/A077739/README.md) (proved, new). Lean: Lean proof, [`A077739_mathlib.lean`](OEIS/A077739/A077739_mathlib.lean).
- Prior art: 
- Draft comment:

  > The conjecture is true: For n ≥ 1 an admissible N exists iff n ∉ {11, 17, 19}; so A077739(n) = 0 and A077740(n) = 0 iff n ∈ {11, 17, 19}. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A077739). - _<Name>_, <Mon DD YYYY>

### [A077740](https://oeis.org/A077740): a(n) = 0 iff n is 11, 17 or 19

- Problem: [OEIS-A077740](OEIS/A077740/README.md) (proved, new). Lean: Lean proof, [`A077739_mathlib.lean`](OEIS/A077739/A077739_mathlib.lean).
- Prior art: 
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A077740). - _<Name>_, <Mon DD YYYY>

### [A078008](https://oeis.org/A078008): even denominators in the rows of the Farey tree

- Problem: [OEIS-A078008](OEIS/A078008/README.md) (proved, partly-known). Lean: Lean proof, [`A078008_mathlib.lean`](OEIS/A078008/A078008_mathlib.lean).
- Prior art: Exact count not found written; folklore parity argument.
- Draft comment:

  > The conjecture is true: for every n >= 0 row n has exactly a(n) = (2^n + 2(-1)^n)/3 fractions with even denominator. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A078008). - _<Name>_, <Mon DD YYYY>

### [A078122](https://oeis.org/A078122): row sums of the M^3-shift matrix are the partitions of 3^n into powers of 3

- Problem: [OEIS-A078122](OEIS/A078122/README.md) (proved, new). Lean: Lean proof, [`A078122_mathlib.lean`](OEIS/A078122/A078122_mathlib.lean).
- Prior art: No proof found; the block-split argument is ours and short.
- Draft comment:

  > The conjecture is true: together with the formula line. M(n,k) is the number of partitions of 3^n into powers of 3 whose largest part is exactly 3^(n-k); summing over k = 0..n gives all partitions of 3^n into powers of 3. The same argument works for every base m ≥ 2 (Hanna's M^2 and M^4 analogues A078121 and A078536 with partitions of 2^n and 4^n), checked numerically below. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A078122). - _<Name>_, <Mon DD YYYY>

### [A078128](https://oeis.org/A078128): partitions into cubes > 1 — a(n) → ∞ with explicit b(k)

- Problem: [OEIS-A078128](OEIS/A078128/README.md) (proved, partly-known). Lean: Lean proof, [`A078128_mathlib.lean`](OEIS/A078128/A078128_mathlib.lean).
- Prior art: Entry still says conjecture; the proof is immediate from the 8/27 Frobenius argument.
- Draft comment:

  > The conjecture is true: a(n) ≥ m + 1 whenever n ≥ 216m + 182, so b(k) = 216k + 181 works. The quoted values are sharp: a(154) = 0 and a(n) ≥ 1 for n > 154; a(218) = 1 and a(n) ≥ 2 for n > 218. (Numerically the least b(k) are 154, 218, 255, 282, 319, 335 for k = 0..5; 216k + 181 is only an upper bound.) (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A078128). - _<Name>_, <Mon DD YYYY>

### [A078173](https://oeis.org/A078173): max t = n(n+2) and max s = 2n over solutions of rst = n(r+s+t)

- Problem: [OEIS-A078173](OEIS/A078173/README.md) (proved, new). Lean: Lean proof, [`A078173_mathlib.lean`](OEIS/A078173/A078173_mathlib.lean).
- Prior art: Short elementary bound; no prior written proof found.
- Draft comment:

  > The conjecture is true: for every n >= 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A078173). - _<Name>_, <Mon DD YYYY>

### [A080674](https://oeis.org/A080674): counting integers below 10^n with digits only in {6,7,8,9}

- Problem: [OEIS-A080674](OEIS/A080674/README.md) (proved, new). Lean: Lean proof, [`A080674_mathlib.lean`](OEIS/A080674/A080674_mathlib.lean).
- Prior art: Trivial count of strings over {6,7,8,9}.
- Draft comment:

  > The conjecture is true: 0 has the digit 0, and the positive integers below 10^n with no digit in {0, ..., 5} are the strings of length 1..n over {6, 7, 8, 9}, so their number is 4 + 4^2 + ... + 4^n = (4/3)(4^n - 1). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A080674.

### [A081320](https://oeis.org/A081320): 3-smooth part of Fibonacci numbers

- Problem: [OEIS-A081320](OEIS/A081320/README.md) (proved, partly-known). Lean: Lean proof, [`A081320_mathlib.lean`](OEIS/A081320/A081320_mathlib.lean).
- Prior art: The entry already says the periodic part follows from strong divisibility; the a(12k) part is a few lines from Lengyel's valuations.
- Draft comment:

  > The conjecture is true. By Lengyel's valuations (1995), v_2(F(n)) is 0 if 3 does not divide n, 1 if n == 3 (mod 6) and v_2(n) + 2 if 6 | n, and v_3(F(n)) is 0 if 4 does not divide n and v_3(n) + 1 if 4 | n; so for n not divisible by 12 both valuations depend only on n mod 12, and for n = 12k they are v_2(k) + 4 and v_3(k) + 2, giving a(12k) = 144*A065331(k). The first part also follows from strong divisibility, as noted above. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A081320.

### [A083452](https://oeis.org/A083452): n written n times exceeds n^n

- Problem: [OEIS-A083452](OEIS/A083452/README.md) (trivial or misstated, new). Lean: Lean proof, [`A083452.lean`](OEIS/A083452/A083452.lean).
- Prior art: Trivial size comparison.
- Draft comment:

  > The conjecture is true: if n >= 2 has d digits then n < 10^d, so the n-fold concatenation of n is at least n*10^(d(n-1)) > n*n^(n-1) = n^n. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A083452.

### [A083942](https://oeis.org/A083942): a(n) = Sum_{k=1..2^n-1} Catalan(k)

- Problem: [OEIS-A083942](OEIS/A083942/README.md) (proved, new). Lean: Lean proof, [`A083942_mathlib.lean`](OEIS/A083942/A083942_mathlib.lean).
- Prior art: No proof found; immediate (the code is the largest word of its length).
- Draft comment:

  > The conjecture is true: a(n) = Sum_{k=1..2^n-1} C_k. More generally, the position of 1^s 0^s in A014486 is Sum_{k=1..s} C_k for every s. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A083942). - _<Name>_, <Mon DD YYYY>

### [A087324](https://oeis.org/A087324): no term has a perfect-square prime signature

- Problem: [OEIS-A087324](OEIS/A087324/README.md) (disproved, partly-known). Lean: Lean proof, [`A087324_mathlib.lean`](OEIS/A087324/A087324_mathlib.lean).
- Prior art: The analogous refutation is in A087325; the 9's complement version (mod 4 argument) is not recorded.
- Draft comment:

  > Conjecture (2) is false: no term has an all-even prime signature, such as that of 4 = 2^2 or of p^2*q^2. Such a term n and its 9's complement 10^d - 1 - n would both be squares, but their sum 10^d - 1 is == 3 (mod 4) for d >= 2, which a sum of two squares never is, and for d = 1 no pair (n, 9-n) consists of two squares. The same argument refutes conjecture (2) of A087325; conjecture (1) is not addressed here. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A087324.

### [A088104](https://oeis.org/A088104): an n-digit prime beginning with prime(n) always exists

- Problem: [OEIS-A088104](OEIS/A088104/README.md) (proved, new). Lean: paper proof.
- Prior art: Unconditional via Dusart 2010 short intervals plus a finite check; not stated anywhere found.
- Draft comment:

  > The conjecture is true unconditionally: if P = prime(n) has d digits, the candidates fill [x, x + x/P) with x = P*10^(n-d) >= 10^(n-1), and for n >= 7 Dusart's 2010 bound (a prime in (x, x(1 + 1/(25*log^2 x))] for x >= 396738) together with P < 25*log^2 x puts a prime there; the terms for n <= 14 are found directly. This removes the dependence on Legendre's conjecture noted above. A proof is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A088104.

### [A088120](https://oeis.org/A088120): the common difference is 2 at n = 12

- Problem: [OEIS-A088120](OEIS/A088120/README.md) (disproved, new). Lean: Lean proof, [`A088120_mathlib.lean`](OEIS/A088120/A088120_mathlib.lean).
- Prior art: Counterexample is visible in the entry's own data (d = 2 at n = 12) but nobody has noted it.
- Draft comment:

  > Conjecture (2) is false: a(12) = 1*3*5*...*23 + 2 = 316234143227, with common difference 2. The smaller values k(k+1)...(k+11) + 1, k = 1..4, are composite (e.g., 12! + 1 = 13^2*2834329), and every other choice of a and d gives a larger value. Conjecture (1) is not addressed here. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A088120.

### [A088226](https://oeis.org/A088226): a(n) = |a(n-1) − a(n-2) − a(n-3)| is half the smallest even distance from n − 1 to a square

- Problem: [OEIS-A088226](OEIS/A088226/README.md) (corrected-and-proved, new). Lean: Lean proof, [`A088226_mathlib.lean`](OEIS/A088226/A088226_mathlib.lean).
- Prior art: Entry gives the block formula a(k^2+2m+1)=m, a(k^2+2m+2)=k-m without proof; the conjecture is the same statement shifted by one index and misindexed as printed. No proof found.
- Draft comment:

  > The conjecture is misstated as written; the corrected form is true: Corrected form true: a(n) = f(n − 1) for every n ≥ 1. The printed form is a misstatement by one index. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A088226). - _<Name>_, <Mon DD YYYY>

### [A088617](https://oeis.org/A088617): mean number of U steps in a Schröder n-path is ~ n/√2

- Problem: [OEIS-A088617](OEIS/A088617/README.md) (proved, new). Lean: paper proof, [`A088617_mathlib.lean`](OEIS/A088617/A088617_mathlib.lean).
- Prior art: Roitner proved the companion A090981 (ascents) by the vectorial kernel method and singularity analysis; no proof of the U-step statement found. Proof here: exact formula 4U(n+1) = (3n+2)r(n+1) - n r(n) plus ratio limit r(n+1)/r(n) -> 3+2sqrt2.
- Draft comment:

  > The conjecture is true: With r(n) = Σ_k T(n,k) (A006318) and U(n) = Σ_k k·T(n,k), exactly 4·U(n+1) = (3n+2)·r(n+1) − n·r(n), and U(n)/(n·r(n)) → √(1/2). (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A088617). - _<Name>_, <Mon DD YYYY>

### [A089758](https://oeis.org/A089758): the prime concatenation chain never stops

- Problem: [OEIS-A089758](OEIS/A089758/README.md) (proved, new). Lean: Lean proof, [`A089758_mathlib.lean`](OEIS/A089758/A089758_mathlib.lean).
- Prior art: Direct consequence of Dirichlet's theorem.
- Draft comment:

  > The conjecture is true by Dirichlet's theorem: if C is the current prime concatenation, with L digits, then gcd(C, 30) = 1, so the progression C + 3*10^L*y contains infinitely many primes, and an admissible next term 3y always exists. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A089758.

### [A090519](https://oeis.org/A090519): some prime p has floor(10^n/p) prime

- Problem: [OEIS-A090519](OEIS/A090519/README.md) (proved, new). Lean: Lean proof, [`A090519_mathlib.lean`](OEIS/A090519/A090519_mathlib.lean).
- Prior art: Direct consequence of Bertrand's postulate.
- Draft comment:

  > The conjecture is true: a(1) = 2, and for n >= 2 Bertrand's postulate gives a prime p with 10^n/4 < p <= 10^n/2, so floor(10^n/p) is 2 or 3, both prime. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A090519.

### [A096123](https://oeis.org/A096123): a(n) = n!/(p-1)! for large n (p least prime with n ≤ 2p) is false

- Problem: [OEIS-A096123](OEIS/A096123/README.md) (disproved, partly-known). Lean: Lean proof, [`A096123_mathlib.lean`](OEIS/A096123/A096123_mathlib.lean).
- Prior art: Failure at every n = 2p is new as a proof; data hinted at it.
- Draft comment:

  > The conjecture is false: For every prime p, a(2p) ≤ (2p)!/p! < (2p)!/(p-1)!, and p is the least prime with 2p ≤ 2p. So the conjecture fails at n = 2p for every prime p. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A096123). - _<Name>_, <Mon DD YYYY>

### [A100056](https://oeis.org/A100056): the A054065 permutations do not maximize the sum of differences

- Problem: [OEIS-A100056](OEIS/A100056/README.md) (disproved, partly-known). Lean: Lean proof, [`A100056_mathlib.lean`](OEIS/A100056/A100056_mathlib.lean).
- Prior art: The true maximum floor(n^2/2) - 1 is known (folklore, programming-contest standard); that A100056 falls short at n = 5 is not recorded.
- Draft comment:

  > The conjecture is false: for n = 5 the A054065 permutation (5,2,4,1,3) gives a(5) = 10, but (4,2,5,1,3) gives 2 + 3 + 4 + 2 = 11. For n = 2..9 the true maxima are 1, 3, 7, 11, 17, 23, 31, 39, the well-known value floor(n^2/2) - 1 (cf. A047838), against a(n) = 1, 3, 7, 10, 16, 22, 27, 37. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A100056.

### [A101312](https://oeis.org/A101312): other weekday/day pairs do not give a shifted Friday-13th sequence

- Problem: [OEIS-A101312](OEIS/A101312/README.md) (trivial or misstated, partly-known). Lean: paper proof.
- Prior art: The known unequal 400-year totals (688 Fridays vs 684-687 for other weekdays) immediately rule out a cyclic shift; nobody has drawn this conclusion for A101312.
- Draft comment:

  > The conjecture is true for 1901-2099 but false for the Gregorian calendar as a whole. Every "weekday w on day d" sequence equals "weekday u on the 13th" for some u, and on 1901-2099 the pattern has period 28 and weekday u corresponds to a shift of 20, 8, 24, 12, 0, 16, 4 years for u = Monday, ..., Sunday; across a non-leap century year this correspondence breaks, and over the 400-year cycle no weekday other than Friday gives a cyclic shift of the Friday sequence, as the unequal 400-year totals (688 Friday the 13ths, 684 to 687 for the other weekdays) already show. A proof is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A101312.

### [A104895](https://oeis.org/A104895): positions of k ≥ 0 are A048724(k), positions of −k are A065621(k)

- Problem: [OEIS-A104895](OEIS/A104895/README.md) (proved, partly-known). Lean: Lean proof, [`A104895_mathlib.lean`](OEIS/A104895/A104895_mathlib.lean).
- Prior art: Conjecture follows from cross-referenced identities; no written proof found. %N name line misprinted (signs swapped).
- Draft comment:

  > The conjecture is true: a(n) = k exactly when n = A048724(k) (k ≥ 0), a(n) = −k exactly when n = A065621(k) (k ≥ 1), and a is a bijection from ℕ onto ℤ. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A104895). - _<Name>_, <Mon DD YYYY>

### [A104896](https://oeis.org/A104896): counting integers below 10^n with no digit 0, 1, 2

- Problem: [OEIS-A104896](OEIS/A104896/README.md) (proved, new). Lean: Lean proof, [`A104896_mathlib.lean`](OEIS/A104896/A104896_mathlib.lean).
- Prior art: Trivial count of strings over {3..9}.
- Draft comment:

  > The conjecture is true: 0 has the digit 0, and the other integers below 10^n with no digit 0, 1, 2 are the strings of length 1..n over {3, ..., 9}, numbering 7 + 7^2 + ... + 7^n, which satisfies a(n) = 7a(n-1) + 7. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A104896.

### [A105596](https://oeis.org/A105596): the self-convolution with alternating signs is 1 mod 4

- Problem: [OEIS-A105596](OEIS/A105596/README.md) (proved, new). Lean: Lean proof, [`A105596_mathlib.lean`](OEIS/A105596/A105596_mathlib.lean).
- Prior art: The oddness input is Gao's; the mod-4 step from it to A105596 is stated nowhere.
- Draft comment:

  > With the indices of the unsuppressed convolution c(m) = Sum_{k=0..m} (-1)^k*b(k)*b(m-k), b = A105595, the conjecture is true: for odd m the terms k and m-k cancel, and c(2n) = 2*Sum_{k<n} (-1)^k*b(k)*b(2n-k) + (-1)^n*b(n)^2 == 2n + (-1)^n == 1 (mod 4), because every b(k) is odd (B. Gao, in A105595). A partial Lean 4 verification (the oddness of all terms of A105595 outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A105596.

### [A106249](https://oeis.org/A106249): roots of x^n + 1 in the left half-plane (index shift by one)

- Problem: [OEIS-A106249](OEIS/A106249/README.md) (proved, new). Lean: Lean proof, [`A106249_mathlib.lean`](OEIS/A106249/A106249_mathlib.lean).
- Prior art: Elementary count; the index shift by one is not noted in the entry.
- Draft comment:

  > The conjecture is true after shifting the index by one: a(n) is the number of roots of x^(n+1) + 1 in the open left half-plane, n >= 0 (as printed it fails at n = 1, since x + 1 has the root -1 but a(1) = 0). The roots exp(i*Pi*(2k+1)/m) of x^m + 1 have negative real part iff m < 2(2k+1) < 3m, giving 2*floor(m/4) + (m mod 2) of them, and 2*floor((n+1)/4) + ((n+1) mod 2) satisfies the recurrence of the g.f. with the same initial values. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A106249.

### [A107363](https://oeis.org/A107363): the nonnegative terms are exactly the Fibonacci numbers

- Problem: [OEIS-A107363](OEIS/A107363/README.md) (proved, new). Lean: Lean proof, [`A107363_mathlib.lean`](OEIS/A107363/A107363_mathlib.lean).
- Prior art: Follows in a few lines from Barker's recurrence and F(k+6)=4F(k+3)+F(k); not stated anywhere found.
- Draft comment:

  > The conjecture is true: the denominator multiplies out to 1 - 4x^6 - x^12, so a(n+12) = 4a(n+6) + a(n), and since F(k+6) = 4F(k+3) + F(k) (likewise for Lucas numbers) the 6-sections are a(6j) = F(3j+2), a(6j+1) = a(6j+3) = F(3j+1), a(6j+2) = -L(3j+1) < 0, a(6j+4) = F(3j+3), a(6j+5) = 0. These cover every Fibonacci number, and the formula for a(6j+2) also settles the conjectured formula involving A048876. A proof formally verified in Lean 4 (starting from the recurrence implied by the g.f.) is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A107363.

### [A110320](https://oeis.org/A110320): blocks in RNA secondary structures via Whitney numbers

- Problem: [OEIS-A110320](OEIS/A110320/README.md) (proved, partly-known). Lean: Lean proof, [`A110320_mathlib.lean`](OEIS/A110320/A110320_mathlib.lean).
- Prior art: With Tenn's crown = fence(n) - fence(n-2) identity, McGarvey's conjecture is Irwin's formula rewritten; nobody has written that down.
- Draft comment:

  > The conjecture is true, given the g.f.s of A110320 (E. Deutsch), A051286 (1/R) and A051292 ((1 - z^2 + R)/R), R = sqrt(1 - 2z - z^2 - 2z^3 + z^4): the difference between (1 - z - z^2)/(2z^2*R) - 1/(2z^2) and Sum_{n>=1} (A051292(n+2) - A051286(n+1))/2 * z^n simplifies to 0. Equivalently, by A051292(n) = A051286(n) - A051286(n-2) (M. Tenn, 2026), it is the formula of Irwin above rewritten. A partial Lean 4 verification (that the printed g.f.s generate these sequences outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A110320.

### [A110735](https://oeis.org/A110735): no digit insertion makes a multiple of 101

- Problem: [OEIS-A110735](OEIS/A110735/README.md) (disproved, new). Lean: Lean proof, [`A110735.lean`](OEIS/A110735/A110735.lean).
- Prior art: The counterexample a(101) = 0 is not in OEIS or elsewhere found.
- Draft comment:

  > The conjecture is false: a(101) = 0. The candidates b1 1 b2 0 b3 1 b4 equal b1*10^6 + 10^5 + b2*10^4 + b3*10^2 + 10 + b4, which is == (b2 + b4) - (b1 + b3) + 20 (mod 101) since 100 == -1, a number between 2 and 38, so never 0. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A110735.

### [A113610](https://oeis.org/A113610): local minima of composite digit sums do not mark twin primes

- Problem: [OEIS-A113610](OEIS/A113610/README.md) (disproved, new). Lean: Lean proof, [`A113610.lean`](OEIS/A113610/A113610.lean).
- Prior art: Counterexample n = 12 is not recorded anywhere found.
- Draft comment:

  > The conjecture is false: a(12) = 27 > a(13) = 6 < a(14) = 27, but prime(12) = 37 and prime(13) = 41 are not twin primes. The variant with prime(n+1), prime(n+2) twins also fails, at n = 21 (a(21) = 65 > a(22) = 27 < a(23) = 70, prime(22) = 79, prime(23) = 83); below 10^5 there are 3194 and 1981 failures, respectively. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A113610.

### [A113676](https://oeis.org/A113676): row lengths of Golomb's sequence cut into rows = first differences of A014644

- Problem: [OEIS-A113676](OEIS/A113676/README.md) (proved, new). Lean: Lean proof, [`A113676_mathlib.lean`](OEIS/A113676/A113676_mathlib.lean).
- Prior art: Short induction once the Levine rows are seen as Golomb prefixes.
- Draft comment:

  > The conjecture is true: Both conjectures are true. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A113676). - _<Name>_, <Mon DD YYYY>

### [A116731](https://oeis.org/A116731): bubble sort produces (n^3 − 3n^2 + 5n)/3 distinct (flips, iterations) pairs

- Problem: [OEIS-A116731](OEIS/A116731/README.md) (proved, new). Lean: Lean proof, [`A116731_mathlib.lean`](OEIS/A116731/A116731_mathlib.lean).
- Prior art: No proof found; the pair-set characterisation and count are ours, from classical bubble-sort facts.
- Draft comment:

  > The conjecture is true: for every n ≥ 1: the pairs are exactly (0, 0) and (i, b) with 1 ≤ b ≤ n − 1 and b ≤ i ≤ M(b), where M(b) = Σ_{j<n} min(b, j); there are (n^3 − 3n^2 + 5n)/3 of them. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A116731). - _<Name>_, <Mon DD YYYY>

### [A119659](https://oeis.org/A119659): consecutive prime-indexed primes form a triangle from (17, 31, 41) on

- Problem: [OEIS-A119659](OEIS/A119659/README.md) (proved, new). Lean: paper proof, [`A119659_mathlib.lean`](OEIS/A119659/A119659_mathlib.lean).
- Prior art: Immediate from standard explicit bounds.
- Draft comment:

  > The conjecture is true: q_n + q_{n+1} > q_{n+2} for every n ≥ 4, and fails exactly for n = 1, 2, 3. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A119659). - _<Name>_, <Mon DD YYYY>

### [A123722](https://oeis.org/A123722): multiples of 3 in the list are 3 and 3p (p prime), and every odd prime occurs

- Problem: [OEIS-A123722](OEIS/A123722/README.md) (proved, new). Lean: Lean proof, [`A123722_mathlib.lean`](OEIS/A123722/A123722_mathlib.lean).
- Prior art: Entry still a conjecture (verified to 2000 by Layman); no proof found.
- Draft comment:

  > The conjecture is true: Proved, both parts. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A123722). - _<Name>_, <Mon DD YYYY>

### [A123723](https://oeis.org/A123723): multiples of 4 in the list, other than 4, are 4p with p prime

- Problem: [OEIS-A123723](OEIS/A123723/README.md) (proved, new). Lean: Lean proof, [`A123723_mathlib.lean`](OEIS/A123723/A123723_mathlib.lean).
- Prior art: Entry still a conjecture; no proof found.
- Draft comment:

  > The conjecture is true: Proved. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A123723). - _<Name>_, <Mon DD YYYY>

### [A124431](https://oeis.org/A124431): Mathar's recurrence for Σ 2^k C(⌊(n+k)/2⌋, k) C(⌊(n+k+1)/2⌋, k)

- Problem: [OEIS-A124431](OEIS/A124431/README.md) (proved, new). Lean: Lean proof, [`A124431_mathlib.lean`](OEIS/A124431/A124431_mathlib.lean).
- Prior art: Entry prints an algebraic g.f. without proof; no proof of the recurrence found.
- Draft comment:

  > The conjecture is true: for every n ≥ 4. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A124431). - _<Name>_, <Mon DD YYYY>

### [A129454](https://oeis.org/A129454): p-adic valuation of a triple gcd product (true after an index shift)

- Problem: [OEIS-A129454](OEIS/A129454/README.md) (proved, partly-known). Lean: Lean proof, [`A129454_mathlib.lean`](OEIS/A129454/A129454_mathlib.lean).
- Prior art: The 2-D analogue is confirmed in A092287; the 3-D case and the index correction (n-1 for n) are not stated anywhere found.
- Draft comment:

  > The conjecture is true with n-1 in place of n (i.e., for the product over 1..n) and false as printed: for every prime p and n >= 1, ordp(a(n),p) = Sum_{t>=1} floor((n-1)/p^t)^3, while the printed formula fails at n = 2, p = 2 and at n = 3, p = 3 (a(3) = 2). Indeed ordp(gcd(i,j,k),p) counts the t with p^t dividing i, j and k, and summing over 1 <= i,j,k <= n-1 gives Sum_t floor((n-1)/p^t)^3; this is the 3-dimensional analog of A092287. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A129454.

### [A131262](https://oeis.org/A131262): least k with A130654(k) = n equals sigma(2^n) phi(2^n)

- Problem: [OEIS-A131262](OEIS/A131262/README.md) (proved, new). Lean: Lean proof, [`A131262_mathlib.lean`](OEIS/A131262/A131262_mathlib.lean).
- Prior art: No proof found; ingredients classical.
- Draft comment:

  > The conjecture is true: a(0) = 1 and a(n) = 2^(n-1)(2^(n+1) - 1) = sigma(2^n) phi(2^n) = 4^n - 2^(n-1) for n >= 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A131262). - _<Name>_, <Mon DD YYYY>

### [A132089](https://oeis.org/A132089): the first column of L^(m+1) is the row-sum sequence of L^m (L = Losanitsch's triangle)

- Problem: [OEIS-A132089](OEIS/A132089/README.md) (proved, new). Lean: Lean proof, [`A132089.lean`](OEIS/A132089/A132089.lean).
- Prior art: Immediate from the first column of Losanitsch's triangle being all ones.
- Draft comment:

  > The conjecture is true: both parts; (1) is (2) with power 1. The identification "row sums of L = A005418" in (1) is the known name of A005418 (Losanitsch). (proof verified in Lean 4: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A132089). - _<Name>_, <Mon DD YYYY>

### [A133212](https://oeis.org/A133212): a(n) = 2*A038503(n+3) for n > 0

- Problem: [OEIS-A133212](OEIS/A133212/README.md) (proved, new). Lean: Lean proof, [`A133212_mathlib.lean`](OEIS/A133212/A133212_mathlib.lean).
- Prior art: Both sides satisfy the same recurrence (stated in the two entries); matching initial terms is the whole proof, not written anywhere.
- Draft comment:

  > The conjecture is true: by the roots-of-unity filter, A038503(m) = (2^m + (1+i)^m + (1-i)^m)/4 for m >= 1, so A038503(m) satisfies the recurrence with characteristic polynomial (x-2)(x^2-2x+2) = x^3 - 4x^2 + 6x - 4, as does a(n), and both sides of a(n) = 2*A038503(n+3) equal 4, 12, 32 at n = 1, 2, 3. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A133212.

### [A135571](https://oeis.org/A135571): differences of two positive triangular numbers in an odd number of ways

- Problem: [OEIS-A135571](OEIS/A135571/README.md) (proved, partly-known). Lean: Lean proof, [`A135571_mathlib.lean`](OEIS/A135571/A135571_mathlib.lean).
- Prior art: The odd-divisor count is classical (Sylvester); the parity characterisation follows in a few lines but is not stated anywhere found.
- Draft comment:

  > The conjecture is true: T(a) - T(b) = n corresponds to factorizations 2n = (a-b)(a+b+1) into factors of opposite parity, so the number of representations with b >= 1 is the number of odd divisors of n minus [n is triangular]. The number of odd divisors is odd iff n is a square or twice a square; a twice-square is never triangular, and no number is both a square and twice a square, which gives the stated set. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A135571.

### [A137328](https://oeis.org/A137328): the prime 2 never occurs

- Problem: [OEIS-A137328](OEIS/A137328/README.md) (disproved, new). Lean: Lean proof, [`A137328_mathlib.lean`](OEIS/A137328/A137328_mathlib.lean).
- Prior art: That 2 never occurs is not recorded for A137328; the odd-prime part stays open.
- Draft comment:

  > The conjecture is false: 2 never occurs, since the subtracted primorial is even and >= 2, so prime(n) - primorial(k) = 2 would make prime(n) even and >= 4. Every odd prime below 10^6 does occur; whether every odd prime occurs is open. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A137328.

### [A138808](https://oeis.org/A138808): the row sums of A010766 are upper bounds

- Problem: [OEIS-A138808](OEIS/A138808/README.md) (proved, new). Lean: Lean proof, [`A138808_mathlib.lean`](OEIS/A138808/A138808_mathlib.lean).
- Prior art: Immediate; no written proof found.
- Draft comment:

  > The conjecture is true: for every n >= 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A138808). - _<Name>_, <Mon DD YYYY>

### [A139043](https://oeis.org/A139043): sum of composites ≤ 10^n versus 10^n(10^n+1)/2 - 1 - (10^n)^2/(2 log 10^n - 1)

- Problem: [OEIS-A139043](OEIS/A139043/README.md) (proved, partly-known). Lean: Lean proof, [`A139043_mathlib.lean`](OEIS/A139043/A139043_mathlib.lean).
- Prior art: The expansion is in the literature; the conclusion for this entry (ratio true, difference false) is not stated.
- Draft comment:

  > Read as asymptotic equivalence (ratio -> 1), both statements are true: the main one because both sides are ~ x^2/2 with x = 10^n, since the sum S(x) of primes <= x is at most x*pi(x), and the parenthetical one by the prime number theorem. Read as difference -> 0, both are false: with L = log x, S(x) = x^2/(2L) + x^2/(4L^2) + x^2/(4L^3) + O(x^2/L^4) (cf. C. Axler, arXiv:1606.06874), while x^2/(2L - 1) = x^2/(2L) + x^2/(4L^2) + x^2/(8L^3) + O(x^2/L^4), so the difference grows like x^2/(8L^3). A partial Lean 4 verification (the main statement in the ratio reading; the parenthetical claim and the difference reading outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A139043.

### [A140869](https://oeis.org/A140869): if h is not a term, then 4h + 5 is prime

- Problem: [OEIS-A140869](OEIS/A140869/README.md) (proved, partly-known). Lean: Lean proof, [`A140869.lean`](OEIS/A140869/A140869.lean).
- Prior art: Sundaram-type argument; the specific statement is not written anywhere found.
- Draft comment:

  > The conjecture is true: if 4h + 5 = (2a+1)(2b+1) with a, b >= 1, then a + b is even and h = ab + (a+b)/2 - 1 = floor((2ab + a + b - 2)/2) = T(max(a,b), min(a,b)), so every h with 4h + 5 composite is a term (a Sundaram-type argument). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A140869.

### [A141459](https://oeis.org/A141459): denominators of ∫_0^1 log(1 - 1/x)^n dx

- Problem: [OEIS-A141459](OEIS/A141459/README.md) (proved, new). Lean: Lean proof, [`A141459_mathlib.lean`](OEIS/A141459/A141459_mathlib.lean).
- Prior art: Classical ingredients (logistic moments via eta(2k), von Staudt-Clausen); the evaluation int_0^1 log(1-1/x)^n dx = 2^n B'_n (pi i)^n not found stated.
- Draft comment:

  > The conjecture is true: ∫_0^1 log(1 - 1/x)^n dx = 2^n B'_n (πi)^n for all n ≥ 0 (B'_n the Bernoulli numbers with B'_1 = +1/2), and den(2^n B'_n) = A141459(n). Hence both conjectures hold (A211163 for n ≥ 2, where (-1/π^n)·∫ = -2^n B'_n i^n is rational). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A141459). - _<Name>_, <Mon DD YYYY>

### [A144652](https://oeis.org/A144652): if h is not a term, then 4h + 1 is prime (h ≥ 1)

- Problem: [OEIS-A144652](OEIS/A144652/README.md) (proved, partly-known). Lean: Lean proof, [`A144652.lean`](OEIS/A144652/A144652.lean).
- Prior art: Sundaram-type argument; the specific statement is not written anywhere found.
- Draft comment:

  > The conjecture is true for h >= 1 (h = 0 is not a term and 4h + 1 = 1): if 4h + 1 = (2a+1)(2b+1) with a, b >= 1, then a + b is even and h = ab + (a+b)/2 = T(max(a,b), min(a,b)), so every h >= 1 with 4h + 1 composite is a term (a Sundaram-type argument). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A144652.

### [A155005](https://oeis.org/A155005): a(5+5n) = 1125*10^n for n > 0

- Problem: [OEIS-A155005](OEIS/A155005/README.md) (disproved, new). Lean: Lean proof, [`A155005_mathlib.lean`](OEIS/A155005/A155005_mathlib.lean).
- Prior art: Refuted by the entry's own data; no published remark found.
- Draft comment:

  > The conjecture is false: It holds for n = 1, 2 (a(10) = 11250, a(15) = 112500, in the entry's data) and fails at n = 3: A121041(1125000) = 19, so a(20) is not 1125000. The entry's own data list a(19) = 1125000 and a(20) = 3124800. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A155005). - _<Name>_, <Mon DD YYYY>

### [A156834](https://oeis.org/A156834): for n > 1, a(n) = n iff n is prime

- Problem: [OEIS-A156834](OEIS/A156834/README.md) (proved, new). Lean: Lean proof, [`A156834_mathlib.lean`](OEIS/A156834/A156834_mathlib.lean).
- Prior art: Entry still says conjecture.
- Draft comment:

  > The conjecture is true: Both conjectures are true: for n > 1, A156834(n) >= n and A156833(n) >= n, with equality iff n is prime. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A156834). - _<Name>_, <Mon DD YYYY>

### [A156869](https://oeis.org/A156869): T(2n + m, n + m) = T(2n, n) iff m >= 0

- Problem: [OEIS-A156869](OEIS/A156869/README.md) (proved, partly-known). Lean: Lean proof, [`A156870_mathlib.lean`](OEIS/A156870/A156870_mathlib.lean).
- Prior art: 'Only if' (strict drop for m < 0) not found; immediate.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A156869). - _<Name>_, <Mon DD YYYY>

### [A156870](https://oeis.org/A156870): T(2n + m, n + m) = T(2n, n) iff m >= 0

- Problem: [OEIS-A156870](OEIS/A156870/README.md) (proved, partly-known). Lean: Lean proof, [`A156870_mathlib.lean`](OEIS/A156870/A156870_mathlib.lean).
- Prior art: 'Only if' (strict drop for m < 0) not found; immediate.
- Draft comment:

  > The conjecture is true: in both directions: T(2n+m, n+m) = T(2n, n) for m >= 0, and T(2n+m, n+m) < T(2n, n) for m < 0. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A156870). - _<Name>_, <Mon DD YYYY>

### [A158233](https://oeis.org/A158233): the terms are only 0, 3, 4, 6

- Problem: [OEIS-A158233](OEIS/A158233/README.md) (proved, new). Lean: Lean proof, [`A158233_mathlib.lean`](OEIS/A158233/A158233_mathlib.lean).
- Prior art: Immediate residue check mod 9; no proof found.
- Draft comment:

  > The conjecture is true: a(n) is 0, 3, 4 or 6 for every n >= 1, and all four values occur. Moreover a(n) = 4 exactly when 3 does not divide the product. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A158233). - _<Name>_, <Mon DD YYYY>

### [A165300](https://oeis.org/A165300): Layman's four rules for the 1,2-path sequence

- Problem: [OEIS-A165300](OEIS/A165300/README.md) (proved, new). Lean: Lean proof, [`A165300_mathlib.lean`](OEIS/A165300/A165300_mathlib.lean).
- Prior art: Entry has Layman's conjecture and Lava's mod-4 recurrence formula, both without proof; no proof found.
- Draft comment:

  > The conjecture is true: (all four rules, for every n; the closed form below is also proved). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165300). - _<Name>_, <Mon DD YYYY>

### [A165640](https://oeis.org/A165640): a(n) = floor(4(n+4)/5) - floor(2(n+4)/3)

- Problem: [OEIS-A165640](OEIS/A165640/README.md) (proved, new). Lean: Lean proof, [`A165640_mathlib.lean`](OEIS/A165640/A165640_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true for n >= 1. With x, y, z the multiplicities of -2, 1, 3, the conditions are 3x = n - 3 + 2z and y = n - x - z >= 0, so for n >= 3, a(n) is the number of z == n (mod 3) in [0, floor((2n+3)/5)]; this count and the floor formula are both degree-1 quasi-polynomials of period 15, so agreement on two periods (and at n = 1, 2) proves the identity. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165640.

### [A165886](https://oeis.org/A165886): a(n)/A141459(n+1) = A006519(n+1)

- Problem: [OEIS-A165886](OEIS/A165886/README.md) (proved, new). Lean: Lean proof, [`A165886_mathlib.lean`](OEIS/A165886/A165886_mathlib.lean).
- Prior art: Elementary two-line identity; no written proof found.
- Draft comment:

  > The conjecture is true: for every n ≥ 0: a(n) = A141459(n+1) · A006519(n+1). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165886). - _<Name>_, <Mon DD YYYY>

### [A166272](https://oeis.org/A166272): the reduced denominator is always 3

- Problem: [OEIS-A166272](OEIS/A166272/README.md) (proved, new). Lean: Lean proof, [`A166272_mathlib.lean`](OEIS/A166272/A166272_mathlib.lean).
- Prior art: Immediate from k | 3S(k) (same round's A166102/A166103 resolution).
- Draft comment:

  > The conjecture is true: for every odd k with k ∤ S(k), S(k)/k = t/3 in lowest terms with t = 3S(k)/k. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A166272). - _<Name>_, <Mon DD YYYY>

### [A167230](https://oeis.org/A167230): entries of exp(Sierpiński triangle)/e are Bell numbers

- Problem: [OEIS-A167230](OEIS/A167230/README.md) (proved, new). Lean: Lean proof, [`A167230_mathlib.lean`](OEIS/A167230/A167230_mathlib.lean).
- Prior art: No proof found. Short proof: the Sierpinski matrix is the zeta matrix of the Boolean lattice (Lucas), so its m-th power has entries m^j, and Dobinski's formula gives Bell(j).
- Draft comment:

  > The conjecture is true: entry (n,k) is Bell(j) = A000110(j) if the binary 1's of k are among those of n, with j = A000120(n) - A000120(k), and 0 otherwise. By Lucas's theorem the Sierpinski triangle S is the Kronecker power of [[1,0],[1,1]], so S^m has entries m^j or 0, and exp(S)(n,k) = Sum_{m>=0} m^j/m! = e*Bell(j) by Dobinski's formula. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A167230.

### [A173643](https://oeis.org/A173643): the odd-part formula needs K = 0 (counterexample 3)

- Problem: [OEIS-A173643](OEIS/A173643/README.md) (disproved, new). Lean: Lean proof, [`A173643_mathlib.lean`](OEIS/A173643/A173643_mathlib.lean).
- Prior art: 
- Draft comment:

  > The conjecture is false: As stated (K, M > 0) the conjecture is false: a(3) = 3 = (2^5 − 2^1 − 3)/9 has odd part 3, and F(M,K) ≠ 3 for K, M > 0 (F(2,0) = 3). With K ≥ 0 allowed it is true. The odd parts missed by K > 0 are exactly F(M,0) for even M: 3, 227, 14563, 932067, …, each of which is a term. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A173643). - _<Name>_, <Mon DD YYYY>

### [A177430](https://oeis.org/A177430): exp(sum b(n)^m x^n/n) is integral exactly for even m >= 0

- Problem: [OEIS-A177430](OEIS/A177430/README.md) (proved, new). Lean: Lean proof, [`A177430_mathlib.lean`](OEIS/A177430/A177430_mathlib.lean).
- Prior art: Immediate from Dwork/Gauss congruences; no written proof found.
- Draft comment:

  > The conjecture is true: in both directions: exp(sum b(n)^m x^n/n) is integral iff m >= 0 and m is even. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A177430). - _<Name>_, <Mon DD YYYY>

### [A177431](https://oeis.org/A177431): exp(sum a(n)^m x^n/n) integral only for even m >= 0

- Problem: [OEIS-A177431](OEIS/A177431/README.md) (proved, new). Lean: Lean proof, [`A177430_mathlib.lean`](OEIS/A177430/A177430_mathlib.lean).
- Prior art: Immediate from Dwork/Gauss congruences; no written proof found.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A177431). - _<Name>_, <Mon DD YYYY>

### [A178473](https://oeis.org/A178473): OEIS A178473

- Problem: [OEIS-A178473](OEIS/A178473/README.md) (proved, new). Lean: Lean proof, [`A178473_mathlib.lean`](OEIS/A178473/A178473_mathlib.lean).
- Prior art: Does not need the conjectured closed form of A202367.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A178473). - _<Name>_, <Mon DD YYYY>

### [A178612](https://oeis.org/A178612): no term is a square (rank-0 elliptic curve)

- Problem: [OEIS-A178612](OEIS/A178612/README.md) (proved, new). Lean: paper proof, [`A178612_mathlib.lean`](OEIS/A178612/A178612_mathlib.lean).
- Prior art: 
- Draft comment:

  > The conjecture is true: F(p,q) = p^6 − 4p^4q + 4p^2q^2 + 4q^3 is never a perfect square for integers p, q ≠ 0. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A178612). - _<Name>_, <Mon DD YYYY>

### [A179873](https://oeis.org/A179873): nondecreasing sequence of odd numbers

- Problem: [OEIS-A179873](OEIS/A179873/README.md) (proved, new). Lean: Lean proof, [`A179874_mathlib.lean`](OEIS/A179874/A179874_mathlib.lean).
- Prior art: Immediate from the classical formula; deduction not found written.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A179873). - _<Name>_, <Mon DD YYYY>

### [A179874](https://oeis.org/A179874): integral antiharmonic means of the units mod h are odd and nondecreasing

- Problem: [OEIS-A179874](OEIS/A179874/README.md) (proved, new). Lean: Lean proof, [`A179874_mathlib.lean`](OEIS/A179874/A179874_mathlib.lean).
- Prior art: Immediate from the classical formula; deduction not found written.
- Draft comment:

  > The conjecture is true: Both true: whenever B(h) is an integer, 3B(h) = 2h ± 1, so B(h) is odd, and B is nondecreasing along A179871. More precisely B(h) ∈ ℤ iff h is squarefree and B(h) = (2h + (−1)^ω(h))/3 is an integer. Side note: A179874's data lists 151 twice ("..., 145, 151, 151, 153, ..."); the distinct values contain 151 once and otherwise agree with the data. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A179874). - _<Name>_, <Mon DD YYYY>

### [A179902](https://oeis.org/A179902): the parity pattern 1, 0, 1, 1 (period 4) holds

- Problem: [OEIS-A179902](OEIS/A179902/README.md) (proved, partly-known). Lean: Lean proof, [`A179902_mathlib.lean`](OEIS/A179902/A179902_mathlib.lean).
- Prior art: Parity is immediate from Howroyd's closed form, which the entry states without proof; closed form and parity proved in Lean here.
- Draft comment:

  > The conjecture is true: for every n >= 1: a(n) is even iff n = 2 (mod 4). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A179902). - _<Name>_, <Mon DD YYYY>

### [A182132](https://oeis.org/A182132): (30n-7)(90n-23)(300n-79) is Carmichael when all factors are prime

- Problem: [COM-C016](COM/C016/README.md) (proved, new). Lean: Lean proof, [`C016_mathlib.lean`](COM/C016/C016_mathlib.lean).
- Prior art: One-line Korselt check of the kind Greathouse wrote in sibling entries A182085, A182133; A182132 itself has no proof.
- Draft comment:

  > The conjecture is true: with m = 30n - 8 the factors are m+1, 3m+1, 10m+1, and C - 1 = m(30m^2 + 43m + 14) is divisible by m, 3m and 10m because m == 1 (mod 3) and m == 2 (mod 10); so by Korselt's criterion C is a Carmichael number whenever the three factors are prime. Compare the analogous arguments in A182085 and A182133. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/COM/C016.

### [A182132](https://oeis.org/A182132): (30n-7)(90n-23)(300n-79) is Carmichael whenever its factors are prime

- Problem: [OEIS-A182132](OEIS/A182132/README.md) (proved, new). Lean: Lean proof, [`A182132_mathlib.lean`](OEIS/A182132/A182132_mathlib.lean).
- Prior art: Standard Korselt/Chernick check for (m+1)(3m+1)(10m+1), m = 30n-8; not stated for this entry, unlike its sisters.
- Draft comment:

  > The conjecture is true: C - 1 = 60(4n-1)(15n-4)(225n-53), and each of 30n-8, 90n-24, 300n-80 divides it as a polynomial with integer quotient; when 30n-7, 90n-23, 300n-79 are prime they are distinct, so C is squarefree and Korselt's criterion makes it a Carmichael number. This is the Chernick-type family (m+1)(3m+1)(10m+1) with m = 30n - 8. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182132.

### [A182207](https://oeis.org/A182207): Carmichael numbers divisible by p and 2p - 1 (true, short)

- Problem: [COM-C042](COM/C042/README.md) (trivial or misstated, new). Lean: Lean proof, [`C042_mathlib.lean`](COM/C042/C042_mathlib.lean).
- Prior art: One-line Korselt argument; A182207 still lists it as a conjecture.
- Draft comment:

  > The conjecture is true by Korselt's criterion: 2p - 2 divides C - 1, and with C = p(2p-1)m, since 2p - 1 == 1 and p^2 == 1 (mod 2p-2) (p is odd, as C is odd), pm == 1 gives m == p (mod 2p-2), so m = n(2p-2) + p with n >= 0. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/COM/C042.

### [A182207](https://oeis.org/A182207): Carmichael numbers divisible by p and 2p - 1 are p(2p-1)(n(2p-2)+p)

- Problem: [OEIS-A182207](OEIS/A182207/README.md) (proved, new). Lean: Lean proof, [`A182207_mathlib.lean`](OEIS/A182207/A182207_mathlib.lean).
- Prior art: Entry still labels it a conjecture; the one-line Korselt proof (2p-2 | C-1 and p^2 = 1 mod 2p-2) is not stated there. Same pattern as the sister entries Greathouse closed in 2012.
- Draft comment:

  > The conjecture is true by Korselt's criterion: 2p - 2 divides C - 1, and writing C = p(2p-1)m, 2p - 1 == 1 and p^2 == 1 (mod 2p-2) (C and hence p are odd), so pm == 1 gives m == p (mod 2p-2), i.e., C = p(2p-1)(n(2p-2) + p) with n >= 0 (in fact n >= 1, since m = p would give p^2 | C). The analogous statements in A182151, A182206, A182208 were proved in the same way. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182207.

### [A182334](https://oeis.org/A182334): the order-9 recurrence fails at n = 10, 11 (holds from n = 12)

- Problem: [OEIS-A182334](OEIS/A182334/README.md) (disproved, partly-known). Lean: Lean proof, [`A182334_mathlib.lean`](OEIS/A182334/A182334_mathlib.lean).
- Prior art: The correct range (n >= 12) is implicit in Barker's g.f. and the Magma program, but no one states that the printed formula fails at n = 10, 11.
- Draft comment:

  > The formula a(n) = 35*a(n-3) - 35*a(n-6) + a(n-9) holds for n >= 12 but fails at n = 10 and 11: 35*a(7) - 35*a(4) + a(1) = 11025 != a(10) = 11026, and the right side at n = 11 is 17956 != a(11) = 17955. T = k(k+1)/2 = s^2 +- 1 means x^2 - 8s^2 = 9 or -7 with x = 2k+1; every solution lies on the orbit of (3,0), (1,1) or (5,2) under (x,s) -> (3x+8s, x+3s), T satisfies the recurrence with characteristic polynomial (t-1)(t^2-34t+1) on each orbit, and the three orbits interleave with period 3 from a(4) on. This range agrees with the g.f., whose numerator has degree 11 over a denominator of degree 9. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182334.

### [A182336](https://oeis.org/A182336): n + 1 ≤ a(n) ≤ 9n/8 + 1 for n > 96

- Problem: [OEIS-A182336](OEIS/A182336/README.md) (proved, new). Lean: Lean proof, [`A182336_mathlib.lean`](OEIS/A182336/A182336_mathlib.lean).
- Prior art: Entry still a conjecture; no proof found.
- Draft comment:

  > The conjecture is true: Proved. The threshold is sharp: a(96) = 111 > 109 = ⌊9·96/8⌋ + 1. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182336). - _<Name>_, <Mon DD YYYY>

### [A182532](https://oeis.org/A182532): Carmichael numbers divisible by 7 and 17: the four residue classes mod 120

- Problem: [OEIS-A182532](OEIS/A182532/README.md) (proved, new). Lean: Lean proof, [`A182532_mathlib.lean`](OEIS/A182532/A182532_mathlib.lean).
- Prior art: Entry still presents conjectures (1)-(4); they follow from Korselt (C = 1 mod 48) plus CRT with 119 | C and the residue mod 5.
- Draft comment:

  > Conjectures (1)-(4) are true by Korselt's criterion: 6 and 16 divide C - 1, so 48 | C - 1, and with C = 119m, 119 == 23 (mod 48) gives m == 23 (mod 48), i.e., m == 7 (mod 8) and m == 2 (mod 3). Since C == 9m (mod 10), the last digit of C fixes m mod 5, giving m == 119, 95, 47, 71 (mod 120) for C == 1, 5, 3, 9 (mod 10). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182532.

### [A187011](https://oeis.org/A187011): det(|p_i − p_j|) over the first n primes

- Problem: [OEIS-A187011](OEIS/A187011/README.md) (proved, partly-known). Lean: Lean proof, [`A187011_growth_mathlib.lean`](OEIS/A187011/A187011_growth_mathlib.lean).
- Prior art: Sign part is the weighted-path case of the Bapat-Kirkland-Neumann tree formula; growth part a routine sieve corollary; no prior proof of the A187011 conjecture found.
- Draft comment:

  > The conjecture is true: Both parts are true, and both are proved in Lean 4 + Mathlib. For n ≥ 2, a(n) = (−1)^(n−1) · 2^(n−2) · (p_n − 2) · ∏_{i<n} (p_{i+1} − p_i), so the sign part is immediate. The growth part follows from this formula, a Selberg-sieve upper bound for prime pairs uniform in the shift, and Chebyshev's lower bound for π(x). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A187011). - _<Name>_, <Mon DD YYYY>

### [A192205](https://oeis.org/A192205): a(n)^(1/n) → 16√3/9 for the coefficient sum of (1-x-x^2+x^3)^n

- Problem: [OEIS-A192205](OEIS/A192205/README.md) (proved, new). Lean: Lean proof, [`A192205_mathlib.lean`](OEIS/A192205/A192205_mathlib.lean).
- Prior art: No source found for this specific limit. It is immediate: l2 <= l1 <= sqrt(3n+1) l2 with l2^2 = binomial(4n,n) (stated in the entry); equivalently Gelfand's spectral-radius formula in the Wiener algebra gives max_{|z|=1} |P| = 16 sqrt(3)/9.
- Draft comment:

  > The conjecture is true: with l1 = a(n) and l2^2 the sum of the squared coefficients of P^n, P = 1 - x - x^2 + x^3, Cauchy-Schwarz gives l2 <= l1 <= sqrt(3n+1)*l2, and by Parseval l2^(1/n) tends to max_{|z|=1} |P(z)|. Since |P(e^(it))|^2 = 64s^2(1-s) with s = sin^2(t/2), maximal at s = 2/3, this maximum is sqrt(256/27) = 16*sqrt(3)/9; the identity l2^2 = binomial(4n,n) with Stirling's formula gives the same limit. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A192205.

### [A193550](https://oeis.org/A193550): sqrt((A(x) - 1)/x) is an integer series

- Problem: [OEIS-A193550](OEIS/A193550/README.md) (proved, new). Lean: Lean proof, [`A193550_mathlib.lean`](OEIS/A193550/A193550_mathlib.lean).
- Prior art: No proof found; the mod-4 reduction to the Catalan continued fraction is ours.
- Draft comment:

  > The conjecture is true: Writing A = 1 + x B(x)^2, B has integer coefficients (B = 1 + x + 6x^2 + 97x^3 + ...). The proof uses only that every partial numerator is 1 mod 4, so the same holds for any S-fraction 1/(1 - c_1 x/(1 - c_2 x/(1 - ...))) with all c_i = 1 (mod 4) integers. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A193550). - _<Name>_, <Mon DD YYYY>

### [A195538](https://oeis.org/A195538): denominators of Pythagorean approximations to √8 satisfy a(n) = 35a(n−2) − 35a(n−4) + a(n−6)

- Problem: [OEIS-A195538](OEIS/A195538/README.md) (proved, new). Lean: Lean proof, [`A195538_mathlib.lean`](OEIS/A195538/A195538_mathlib.lean).
- Prior art: Mathar's conjecture still marked as such; the bisection sequences have their own recurrences but no proof of the identification with the Pythagorean-approximation sequence was found.
- Draft comment:

  > The conjecture is true: (recurrence and both bisections). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A195538). - _<Name>_, <Mon DD YYYY>

### [A195539](https://oeis.org/A195539): numerators of Pythagorean approximations to √8 satisfy b(n) = 34b(n−2) − b(n−4)

- Problem: [OEIS-A195539](OEIS/A195539/README.md) (proved, new). Lean: Lean proof, [`A195539_mathlib.lean`](OEIS/A195539/A195539_mathlib.lean).
- Prior art: Mathar's conjecture still marked as such; the bisection sequences have their own recurrences but no proof of the identification with the Pythagorean-approximation sequence was found.
- Draft comment:

  > The conjecture is true: (recurrence and both bisection formulas, the odd one for n ≥ 0 and the even one for n ≥ 1). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A195539). - _<Name>_, <Mon DD YYYY>

### [A195673](https://oeis.org/A195673): p(n,x,p+1,q+1) - p(n,x,p,q) = S(n,x)

- Problem: [OEIS-A195673](OEIS/A195673/README.md) (proved, new). Lean: Lean proof, [`A195673_mathlib.lean`](OEIS/A195673/A195673_mathlib.lean).
- Prior art: Immediate from linearity of the recurrence in the initial values.
- Draft comment:

  > The conjecture is true: for all integers p, q and all n >= 0. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A195673). - _<Name>_, <Mon DD YYYY>

### [A197521](https://oeis.org/A197521): the constant 3.52133782... is 3 plus the constant of A197383

- Problem: [OEIS-A197521](OEIS/A197521/README.md) (proved, new). Lean: Lean proof, [`A197521_mathlib.lean`](OEIS/A197521/A197521_mathlib.lean).
- Prior art: No source states it. Elementary: with s = sin(pi t/6), the two equations give 4s^4+4s^3-4s^2-3s+1 = (s+1)(4s^3-4s+1) and 4s^3-4s+1 = 0, plus a check that the least positive roots match.
- Draft comment:

  > The conjecture is true: with x = t + 3 and s = sin(Pi*t/6), cos(Pi*x/2) = cos(Pi*x/3)^2 becomes (s+1)(4s^3 - 4s + 1) = 0, and the equation of A197383 becomes s(4s^3 - 4s + 1) = 0. Neither has a root with x in (0,3] (4s^3 - 4s + 1 > 0 for -1 <= s <= 0), and for t > 0 the least root of both comes from the least positive root s1 = 0.2696... of 4s^3 - 4s + 1, so both are given by t0 = (6/Pi)*arcsin(s1) = 0.52133782957... A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A197521.

### [A197702](https://oeis.org/A197702): least k with n = ±1 ±3 ± … ±(2k−1)

- Problem: [OEIS-A197702](OEIS/A197702/README.md) (proved, new). Lean: Lean proof, [`A197702_mathlib.lean`](OEIS/A197702/A197702_mathlib.lean).
- Prior art: No proof found; elementary induction on the subset sums of the first k odd numbers.
- Draft comment:

  > The conjecture is true: for every n ≥ 1. SO(k) = k². (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A197702). - _<Name>_, <Mon DD YYYY>

### [A202941](https://oeis.org/A202941): Shevelev's generalized binomials at the first p-row

- Problem: [OEIS-A202941](OEIS/A202941/README.md) (proved, new). Lean: Lean proof, [`A202941_mathlib.lean`](OEIS/A202941/A202941_mathlib.lean).
- Prior art: Does not need the conjectured closed form of A202367.
- Draft comment:

  > The conjecture is true: All six claims hold for every prime in their range. Write r* for the row in each claim (r* = (p−1)/2; k or 2k+1; k or 2k+1). Then v_p(n!^(t)) = 0 for n < r* and v_p(r*!^(t)) ≥ 1, so every inner entry of row r* has v_p = v_p(r*!^(t)) ≥ 1, the two outer entries are 1, and the row sum is 2 plus a multiple of p. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A202941). - _<Name>_, <Mon DD YYYY>

### [A202943](https://oeis.org/A202943): a(n) is odd iff n has no 1-bit at an even position ≥ 2

- Problem: [OEIS-A202943](OEIS/A202943/README.md) (proved, new). Lean: Lean proof, [`A202943_mathlib.lean`](OEIS/A202943/A202943_mathlib.lean).
- Prior art: Standard Frobenius argument ((1+x)^(1/3) in GF(2)[[x]]); not found written for this entry.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A202943). - _<Name>_, <Mon DD YYYY>

### [A203278](https://oeis.org/A203278): OEIS A203278

- Problem: [OEIS-A203278](OEIS/A203278/README.md) (proved, new). Lean: Lean proof, [`A203278_mathlib.lean`](OEIS/A203278/A203278_mathlib.lean).
- Prior art: Does not need the conjectured closed form of A202367.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A203278). - _<Name>_, <Mon DD YYYY>

### [A203484](https://oeis.org/A203484): OEIS A203484

- Problem: [OEIS-A203484](OEIS/A203484/README.md) (proved, new). Lean: Lean proof, [`A203484_mathlib.lean`](OEIS/A203484/A203484_mathlib.lean).
- Prior art: Does not need the conjectured closed form of A202367.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A203484). - _<Name>_, <Mon DD YYYY>

### [A203498](https://oeis.org/A203498): OEIS A203498

- Problem: [OEIS-A203498](OEIS/A203498/README.md) (proved, new). Lean: Lean proof, [`A203498_mathlib.lean`](OEIS/A203498/A203498_mathlib.lean).
- Prior art: Does not need the conjectured closed form of A202367.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A203498). - _<Name>_, <Mon DD YYYY>

### [A203509](https://oeis.org/A203509): OEIS A203509

- Problem: [OEIS-A203509](OEIS/A203509/README.md) (proved, new). Lean: Lean proof, [`A203509_mathlib.lean`](OEIS/A203509/A203509_mathlib.lean).
- Prior art: Does not need the conjectured closed form of A202367.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A203509). - _<Name>_, <Mon DD YYYY>

### [A207969](https://oeis.org/A207969): exp(Σ 5 F(n)^(2k) x^n/n) is an integer series

- Problem: [OEIS-A207969](OEIS/A207969/README.md) (proved, new). Lean: Lean proof, [`A207969_mathlib.lean`](OEIS/A207969/A207969_mathlib.lean).
- Prior art: Standard tools (Gauss/Dold congruences, Dwork lemma, Lucas congruences); this application not found in print.
- Draft comment:

  > The conjecture is true: for every k ≥ 0. (k = 2 and k = 3 are A207969 and A207970.) (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A207969). - _<Name>_, <Mon DD YYYY>

### [A207970](https://oeis.org/A207970): exp(Σ 5 F(n)^6 x^n/n)

- Problem: [OEIS-A207970](OEIS/A207970/README.md) (proved, new). Lean: Lean proof, [`A207969_mathlib.lean`](OEIS/A207969/A207969_mathlib.lean).
- Prior art: Standard tools (Gauss/Dold congruences, Dwork lemma, Lucas congruences); this application not found in print.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A207970). - _<Name>_, <Mon DD YYYY>

### [A208034](https://oeis.org/A208034): exp(Σ 2 Pell(n)^(2k) xⁿ/n) is an integer series; the odd-power and halved versions are not

- Problem: [OEIS-A208034](OEIS/A208034/README.md) (proved, new). Lean: Lean proof, [`A208034_mathlib.lean`](OEIS/A208034/A208034_mathlib.lean).
- Prior art: Same route as the Fibonacci analogue A207969 in this repo; standard tools.
- Draft comment:

  > The conjecture is true: All three hold for every k ≥ 1 ((1) also for k = 0). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A208034). - _<Name>_, <Mon DD YYYY>

### [A208060](https://oeis.org/A208060): lim a(n)^(1/n) = 2L, L the Lüroth geometric mean

- Problem: [OEIS-A208060](OEIS/A208060/README.md) (proved, new). Lean: Lean proof, [`A208060_mathlib.lean`](OEIS/A208060/A208060_mathlib.lean).
- Prior art: No proof found; short Riemann-sum argument.
- Draft comment:

  > The conjecture is true: a(n)^(1/n) -> 2L. Likewise A075885(n)^(1/n) -> L. For any base c >= 1 the sum 1 + sum_m c^m prod_{k<=m}[n/k] has n-th root tending to cL. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A208060). - _<Name>_, <Mon DD YYYY>

### [A210529](https://oeis.org/A210529): a(n) is defined for every n (Dirichlet)

- Problem: [OEIS-A210529](OEIS/A210529/README.md) (proved, partly-known). Lean: Lean proof, [`A210529_mathlib.lean`](OEIS/A210529/A210529_mathlib.lean).
- Prior art: Schmidt's construction in A210708 is the key step; requiring a(n) prime then needs only Dirichlet's theorem for the progression p mod Q. Not stated anywhere found.
- Draft comment:

  > The conjecture is true by Dirichlet's theorem: if p = prime(n) and Q is the product of the primes below sqrt(p), then gcd(p, Q) = 1, so there are infinitely many primes a == p (mod Q), and any such a != p has Q | a - p | a^2 - p^2. This adds the primality requirement to E. M. Schmidt's proof in A210708. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A210529.

### [A211163](https://oeis.org/A211163): numerators of (-1/π^n) ∫_0^1 log(1-1/x)^n dx

- Problem: [OEIS-A211163](OEIS/A211163/README.md) (proved, new). Lean: Lean proof, [`A141459_mathlib.lean`](OEIS/A141459/A141459_mathlib.lean).
- Prior art: Classical ingredients (logistic moments via eta(2k), von Staudt-Clausen); the evaluation int_0^1 log(1-1/x)^n dx = 2^n B'_n (pi i)^n not found stated.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A211163). - _<Name>_, <Mon DD YYYY>

### [A214970](https://oeis.org/A214970): L(2k-1) and L(2k)+1 divide their base-φ → base-φ² images

- Problem: [OEIS-A214970](OEIS/A214970/README.md) (proved, partly-known). Lean: Lean proof, [`A214970_mathlib.lean`](OEIS/A214970/A214970_mathlib.lean).
- Prior art: Dekking's comment in A214971 gives the base-phi representations of L(2k-1) and L(2k)+1; the divisibility n | f(n) (F(4k-2) = F(2k-1)L(2k-1), L(4k)+1 = (L(2k)-1)(L(2k)+1)) is not stated anywhere found.
- Draft comment:

  > The conjecture is true: the greedy base-phi expansions are L(2k-1) = Sum_{j=-(k-1)..k-1} phi^(2j) and L(2k) + 1 = phi^(2k) + 1 + phi^(-2k) (standard representations, as in M. Dekking's comment in A214971), so f(L(2k-1)) = Sum_{j=-(k-1)..k-1} phi^(4j) = F(4k-2) = F(2k-1)*L(2k-1) and f(L(2k)+1) = L(4k) + 1 = (L(2k) - 1)*(L(2k) + 1). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A214970.

### [A215343](https://oeis.org/A215343): Infinitely many Poulet numbers (n+1)p^2 - np with p Poulet

- Problem: [COM-C037](COM/C037/README.md) (proved, new). Lean: Lean (partial), [`C037.lean`](COM/C037/C037.lean).
- Prior art: Follows directly from Larsen 2025 (the progression 561 mod 314160 is Carmichael compatible and contains 561); nobody has noted this, and A215343 still lists it as a conjecture.
- Draft comment:

  > The conjecture is true: for p = 561, (n+1)*561^2 - 561n = 561 + 314160(n+1), so these numbers are the N == 561 (mod 314160 = 561*560) with N > 561^2. This progression contains the Carmichael number 561 and is Carmichael-compatible (lambda(561) = 80 divides 560), so by D. Larsen's theorem (arXiv:2504.09056, 2025) it contains infinitely many Carmichael numbers, all of them Poulet numbers; those below 10^13 are 10054063041, 709277461761, 795066389601, 7650392590401. A partial Lean 4 verification (Larsen's theorem outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/COM/C037.

### [A215461](https://oeis.org/A215461): 2n is a prime plus an odd nonprime for every n > 5

- Problem: [OEIS-A215461](OEIS/A215461/README.md) (proved, new). Lean: Lean proof, [`A215461.lean`](OEIS/A215461/A215461.lean).
- Prior art: No source found; it is a three-line mod-3 argument (one of 2n-3, 2n-5, 2n-7 is a multiple of 3).
- Draft comment:

  > The conjecture is true: for n > 5 one of 2n-3, 2n-5, 2n-7 is a multiple of 3 greater than 3, hence an odd nonprime, and its partner 3, 5 or 7 is prime. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A215461.

### [A215462](https://oeis.org/A215462): 2n is a sum of two odd nonprimes for n > 19; eventual ordering

- Problem: [OEIS-A215462](OEIS/A215462/README.md) (proved, partly-known). Lean: Lean proof, [`A215462_conj2_mathlib.lean`](OEIS/A215462/A215462_conj2_mathlib.lean).
- Prior art: Conjecture 1 is the classical 1984 AIME Problem 14 fact. Conjecture 2 (eventual ordering) follows from Chebyshev plus the Brun-Selberg upper bound for Goldbach representations; no source states it for these sequences.
- Draft comment:

  > Both conjectures are true. For n > 19, one of 9, 25, 35 (residues 0, 1, 2 mod 3) leaves 2n - c an odd multiple of 3 that is >= 9 when n >= 22, and 40 = 25 + 15, 42 = 15 + 27 (the classical fact that every even number > 38 is a sum of two odd composites). For the second, A002372(n) + A215461(n) + a(n) = n gives A215461(n) = 2(P - G) and a(n) = n - 2P + G, with P the number of odd primes below 2n and G = A002372(n), and both inequalities follow from n/log n << P = o(n) (Chebyshev) and G << n/log^2 n (Brun-Selberg sieve). A partial Lean 4 verification (the first conjecture; the second outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A215462.

### [A216971](https://oeis.org/A216971): every entry of row n is divisible by n

- Problem: [OEIS-A216971](OEIS/A216971/README.md) (proved, new). Lean: Lean proof, [`A216971_mathlib.lean`](OEIS/A216971/A216971_mathlib.lean).
- Prior art: No proof found; elementary: C(n,r) r! = n!/(n-r)! is a multiple of n for r >= 1.
- Draft comment:

  > The conjecture is true: n divides T(n,k) for all n >= 1 and all k. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A216971). - _<Name>_, <Mon DD YYYY>

### [A217448](https://oeis.org/A217448): a(n) exists for every n (CRT)

- Problem: [OEIS-A217448](OEIS/A217448/README.md) (proved, new). Lean: Lean proof, [`A217448_mathlib.lean`](OEIS/A217448/A217448_mathlib.lean).
- Prior art: No source found; a CRT choice of k makes q = spf(1+n^2) divide 1+(n+k)^2 while all smaller primes do not.
- Draft comment:

  > The conjecture is true: let q be the smallest prime factor of 1 + n^2 and k = (1 + n^2)!; every prime l <= 1 + n^2 divides k, so l divides 1 + (n+k)^2 iff it divides 1 + n^2, hence 1 + (n+k)^2 also has smallest prime factor q. (A Chinese remainder argument gives smaller such k.) A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A217448.

### [A217876](https://oeis.org/A217876): adjacent transpositions in a random involution are asymptotically Poisson(1)

- Problem: [OEIS-A217876](OEIS/A217876/README.md) (proved, new). Lean: paper proof, [`A217876_mathlib.lean`](OEIS/A217876/A217876_mathlib.lean).
- Prior art: Only permutation analogues (adjacencies in random permutations) found; nothing on involutions.
- Draft comment:

  > The conjecture is true: T(n,j)/I(n) → e^{−1}/j! for every j ≥ 0. Also E C(X_n,i) → 1/i!. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A217876). - _<Name>_, <Mon DD YYYY>

### [A221650](https://oeis.org/A221650): P(n,j,k) = [k | j] p(n-j) counts partitions with at least j/k parts k

- Problem: [OEIS-A221650](OEIS/A221650/README.md) (proved, partly-known). Lean: Lean proof, [`A221650_mathlib.lean`](OEIS/A221650/A221650_mathlib.lean).
- Prior art: Folklore: partitions of n with at least m parts k number p(n - mk) (remove m copies of k; generating function x^(mk)/prod(1-x^i)). The summed form is in A066633; the per-m statements are not written in these entries.
- Draft comment:

  > Both conjectures are true: removing m = j/k parts equal to k is a bijection from the partitions of n with at least m parts k onto the partitions of n - j, so their number is p(n-j), and each such partition contains exactly one part that is the m-th part of size k, which gives conjecture 2. The summed version is in A066633. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A221650.

### [A225004](https://oeis.org/A225004): a(n) divides n²

- Problem: [OEIS-A225004](OEIS/A225004/README.md) (proved, new). Lean: Lean proof, [`A225004_mathlib.lean`](OEIS/A225004/A225004_mathlib.lean).
- Prior art: Immediate from multiplicativity of tau.
- Draft comment:

  > The conjecture is true: every positive multiple m of n with τ(m) < 2τ(n) divides n², so in particular a(n) | n² (and the maximum exists, at most n²). (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A225004). - _<Name>_, <Mon DD YYYY>

### [A226661](https://oeis.org/A226661): 3x+k cycles with exactly n odd elements exist for every n

- Problem: [OEIS-A226661](OEIS/A226661/README.md) (proved, partly-known). Lean: Lean proof, [`A226661_mathlib.lean`](OEIS/A226661/A226661_mathlib.lean).
- Prior art: Existence (3x+k, n odd elements) is an immediate corollary of Lagarias 1990 Thm 2.1 plus the rational-cycle/primitive-cycle correspondence, but no source states it for these entries; our explicit cycles via 3^n - 2^n are a concrete instance.
- Draft comment:

  > The conjecture is true: take a prime m > 3^n/2 and k = 2^(n+m) - 3^n; then the odd numbers x_j = 3^j*2^(n-j)*(2^m-1) - k, 0 <= j < n, and the even numbers 2^i*(3^n - 2^n), 1 <= i <= m, form a cycle of x -> x/2 (x even), (3x+k)/2 (x odd) with exactly n odd elements. It is primitive since gcd(3^n - 2^n, 2^m - 1) = 1, every prime factor of 2^m - 1 being == 1 (mod m) and so > 3^n. Existence also follows from Lagarias (1990), Thm. 2.1; the construction bounds a(n) but does not give its value. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A226661.

### [A226676](https://oeis.org/A226676): 3x-k cycles of every length N ≥ 3 exist

- Problem: [OEIS-A226676](OEIS/A226676/README.md) (proved, partly-known). Lean: Lean proof, [`A226676_mathlib.lean`](OEIS/A226676/A226676_mathlib.lean).
- Prior art: Existence (3x-k, n elements) is an immediate corollary of Lagarias 1990 Thm 2.1 plus the rational-cycle/primitive-cycle correspondence, but no source states it for these entries; our explicit cycles via 3^n - 2^n are a concrete instance.
- Draft comment:

  > The conjecture is true: for n >= 3 put r = n - 1 and k = 3^r - 2^n; then x_j = k + 3^j*2^(r-j), 0 <= j <= r, form a cycle of n positive integers under x -> x/2 (x even), (3x-k)/2 (x odd), with x_0, ..., x_(r-1) odd and x_r = 2(3^r - 2^r), and it is primitive since gcd(3^r - 2^r, k) = gcd(3^r - 2^r, 2^r) = 1. Existence also follows from Lagarias (1990), Thm. 2.1; the construction bounds a(n) but does not give its value. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A226676.

### [A226677](https://oeis.org/A226677): 3x-k cycles with exactly n odd elements exist for every n

- Problem: [OEIS-A226677](OEIS/A226677/README.md) (proved, partly-known). Lean: Lean proof, [`A226677_mathlib.lean`](OEIS/A226677/A226677_mathlib.lean).
- Prior art: Existence (3x-k, n odd elements) is an immediate corollary of Lagarias 1990 Thm 2.1 plus the rational-cycle/primitive-cycle correspondence, but no source states it for these entries; our explicit cycles via 3^n - 2^n are a concrete instance.
- Draft comment:

  > The conjecture is true: for n = 1 take k = 1 and the fixed point 1 of x -> (3x-1)/2, and for n >= 2 put k = 3^n - 2^(n+1); then x_j = k + 3^j*2^(n-j), 0 <= j <= n, form a cycle of x -> x/2 (x even), (3x-k)/2 (x odd) with exactly n odd elements x_0, ..., x_(n-1), primitive since gcd(3^n - 2^n, k) = gcd(3^n - 2^n, 2^n) = 1. Existence also follows from Lagarias (1990), Thm. 2.1; the construction bounds a(n) but does not give its value. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A226677.

### [A227500](https://oeis.org/A227500): (b(n) - a(n))/c(n) is 0, 0 followed by the Fibonacci numbers

- Problem: [OEIS-A227500](OEIS/A227500/README.md) (proved, new). Lean: Lean proof, [`A227500_mathlib.lean`](OEIS/A227500/A227500_mathlib.lean).
- Prior art: No proof found; it follows at once from linearity of the transform and B2 - B1 = [n=1].
- Draft comment:

  > The conjecture is true: for all n >= 2, r2(n) - r1(n) = F(n-2) (Fibonacci, F(0) = 0), and r2(0) - r1(0) = r2(1) - r1(1) = 0. Since the difference is an integer, both fractions have the same reduced denominator c(n), and (b(n) - a(n))/c(n) = F(n-2) for n >= 2 and 0 for n < 2. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A227500). - _<Name>_, <Mon DD YYYY>

### [A227553](https://oeis.org/A227553): number of solutions of x^2 - y^2 - z^2 ≡ 1 (mod p^s)

- Problem: [OEIS-A227553](OEIS/A227553/README.md) (proved, partly-known). Lean: Lean proof, [`A227553_mathlib.lean`](OEIS/A227553/A227553_mathlib.lean).
- Prior art: Odd prime powers: immediate from Cohen's formula as given in Toth 2014 Prop. 14 (linked from the entry). The 2-power cases a(2) = 4, a(2^s) = 2^(2s-1) are not covered there.
- Draft comment:

  > The conjecture is true. For odd p, u = x - y, v = x + y turn the equation into uv = 1 + z^2, giving p(p-1) + 2p = (p+1)p solutions mod p if p == 1 (mod 4) and p(p-1) if p == 3 (mod 4), and every solution is nonsingular, so it has p^2 lifts at each step (Hensel). For 2^s with s >= 2, x must be odd, and counting the square roots of 1 + y^2 + z^2 over the pairs (y, z) gives a(4) = 8 and a(2^s) = 2^(2s-1); the odd prime-power cases also follow from E. Cohen's formula as given in Toth (2014), Prop. 14. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A227553.

### [A228916](https://oeis.org/A228916): indices of primes in A108300 are 1 and multiples of 3

- Problem: [OEIS-A228916](OEIS/A228916/README.md) (proved, new). Lean: Lean proof, [`A228916_mathlib.lean`](OEIS/A228916/A228916_mathlib.lean).
- Prior art: Immediate congruence argument.
- Draft comment:

  > The conjecture is true: if A108300(n) is prime then n = 1 or 3 | n. (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A228916). - _<Name>_, <Mon DD YYYY>

### [A228933](https://oeis.org/A228933): the optimal ascending continued fraction of 1/φ follows a(n) = a(n-1)^2 - 2 from the fourth term

- Problem: [OEIS-A228933](OEIS/A228933/README.md) (proved, partly-known). Lean: Lean proof, [`A228933_mathlib.lean`](OEIS/A228933/A228933_mathlib.lean).
- Prior art: The lemma is Artico's (A228931 pdf); the computation of the first three steps for 1/phi landing on the unit phi^6 = 9 + 4 sqrt 5 is not written anywhere found.
- Draft comment:

  > The conjecture is true: for 1/phi the first remainders are z_1 = 2/phi - 1 = phi^(-3) and z_2 = 4*phi^(-3) - 1 = -phi^(-6), giving a(1) = 2, a(2) = round(phi^3) = 4 and a(3) = -18 = -L(6); from there the remainder is governed by the unit phi^6 = 9 + 4*sqrt(5) of norm +1, and G. Artico's lemma for A228931 gives a(n) = a(n-1)^2 - 2 from a(4) = 322 on. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A228933.

### [A228934](https://oeis.org/A228934): the optimal ascending continued fraction of √44 − 6 follows a two-step recurrence

- Problem: [OEIS-A228934](OEIS/A228934/README.md) (proved, new). Lean: Lean proof, [`A228934_mathlib.lean`](OEIS/A228934/A228934_mathlib.lean).
- Prior art: Artico's A228931 note has the one-step norm-1 unit lemma; the two-step invariant for sqrt 44 - 6 is not written there.
- Draft comment:

  > The conjecture is true (proof verified in Lean 4 + Mathlib: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A228934). - _<Name>_, <Mon DD YYYY>

## Known elsewhere, still labelled a conjecture in OEIS (19): cross-reference only

- [A008578](https://oeis.org/A008578): 1 and the primes are exactly the k with sigma(k) > k·Omega(k). Known from: Already proved in Lean by others before this project: otoi-lab/oeis-lean-proofs, OeisProofs/FC/A8578.lean (Lean 4; 'Solved by Claude (Anthropic) prompted by otoinobuo'), first commit 2026-10-12; marked solved in google-deepmind/formal-conjectures FormalConjectures/OEIS/8578.lean. This project proved it independently; the OEIS entry still says Conjecture. Missed by the 2026-11-04 review, which did not search formal-conjectures. No source found for sigma(k) <= k Omega(k) on composites; elementary proof.
- [A024187](https://oeis.org/A024187): e_n(3, 4, ..., n+3) is A001711. Known from: With Vieta's formula the entry's own 2020 formula settles it.
- [A047926](https://oeis.org/A047926): sorted three-square representations of 3^(2n) (misindexed; reduced to r_3(9^n)). Known from: Corrected count is a direct consequence of the classical Hurwitz formula for r_3(n^2); the off-by-one indexing of the comment is not noted in the entry.
- [A072901](https://oeis.org/A072901): composites with disc Q(√n) = 4n are squarefree. Known from: Textbook: disc Q(sqrt n) = 4n iff n squarefree and n == 2, 3 (mod 4).
- [A079665](https://oeis.org/A079665): when is (b^s + 1)/(b^r + 1) an integer. Known from: Classical: b^r + 1 | b^s + 1 iff r | s and s/r odd.
- [A081199](https://oeis.org/A081199): collinear 4-tuples in the 4^n grid. Known from: Collinear 4-sets in the 4^n grid are the winning lines, counted by Moser's formula ((k+2)^n - k^n)/2.
- [A081200](https://oeis.org/A081200): collinear 5-tuples in the 5^n grid. Known from: Collinear 5-sets in the 5^n grid are the winning lines, counted by Moser's formula ((k+2)^n - k^n)/2.
- [A081201](https://oeis.org/A081201): collinear 6-tuples in the 6^n grid. Known from: Collinear 6-sets in the 6^n grid are the winning lines, counted by Moser's formula ((k+2)^n - k^n)/2.
- [A088276](https://oeis.org/A088276): 10^k + 9351 is never prime, though 9351 ≡ 0 (mod 3). Known from: Prime Puzzles 556 (c. 2010) gives the covering {7, 11, 13, 37} for p == 9351 (mod 37037), including r = 9351, and also 48247, 56473; not linked to A088276.
- [A097406](https://oeis.org/A097406): primitive prime factors of 2^n − 1 are ≡ 1 (mod n). Known from: Textbook: ord_p(2) = n divides p - 1. Conjecture (2) is not a precise statement.
- [A101462](https://oeis.org/A101462): 2^k − 509203 is never prime, so a(42228) does not exist. Known from: That 2^n - 509203 is never prime is stated (Wikipedia, dual Riesel numbers); the link to A101462 (index 42228) is not recorded.
- [A102613](https://oeis.org/A102613): π(n)/(n − π(n)) → 0. Known from: Immediate from pi(n)/n -> 0 (Chebyshev/Legendre).
- [A113250](https://oeis.org/A113250): a(m, 2n+1) is a perfect square (m = 4). Known from: Already proved in Lean by others before this project: KitaKen1/oeis-a113249-family-square-terms-lean (Lean 4); marked solved in google-deepmind/formal-conjectures FormalConjectures/OEIS/113250.lean, PR #4963 (2026-08-15). This project proved it independently; the OEIS entry still says Conjecture. Missed by the 2026-11-04 review, which did not search formal-conjectures. The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture.
- [A113252](https://oeis.org/A113252): a(m, 2n+1) is a perfect square (m = 6). Known from: Already proved in Lean by others before this project: KitaKen1/oeis-a113249-family-square-terms-lean (Lean 4); marked solved in google-deepmind/formal-conjectures FormalConjectures/OEIS/113252.lean, PR #4963 (2026-08-15). This project proved it independently; the OEIS entry still says Conjecture. Missed by the 2026-11-04 review, which did not search formal-conjectures. The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture.
- [A113255](https://oeis.org/A113255): a(m, 2n+1) is a perfect square (m = 9). Known from: Already proved in Lean by others before this project: KitaKen1/oeis-a113249-family-square-terms-lean (Lean 4); marked solved in google-deepmind/formal-conjectures FormalConjectures/OEIS/113255.lean, PR #4963 (2026-08-15). This project proved it independently; the OEIS entry still says Conjecture. Missed by the 2026-11-04 review, which did not search formal-conjectures. The m = 3 (Israel 2017) and m = 8 (Stephan 2026, AI proof) cases are proved in OEIS; Jacob's 2023 closed forms make m = 1, 3, 5, 7 a one-line check. No source proves the family for all m, and the entry for this m still says Conjecture.
- [A115038](https://oeis.org/A115038): every prime is y^k − x^2. Known from: Triviality; squares count as perfect powers per the entry's own data.
- [A125148](https://oeis.org/A125148): every x coprime to 10 has a prime x + 10m. Known from: Direct corollary of Dirichlet's theorem.
- [A176494](https://oeis.org/A176494): an odd prime p with |2^m - p| composite for every m ≥ 1. Known from: 509203 is a known dual Riesel number and is prime, so it refutes the conjecture; OEIS does not record this.
- [A182088](https://oeis.org/A182088): (30n-29)(60n-59)(90n-89)(180n-179) is Carmichael whenever its factors are prime. Known from: The product is U_4(m) with m = 5(n-1) (p(2p-1)(3p-2)(6p-5), p = 30n-29), Chernick's 1939 form.

