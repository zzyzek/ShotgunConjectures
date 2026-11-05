# OEIS outreach list

OEIS entries whose conjecture this project settled and which OEIS does not yet record as settled
(prior-art review 2026-11-04: current entry, entries citing it, edit history, web, arXiv).
Each draft comment is a starting point: shorten it to OEIS style and sign it. "Partly known" means a source covers part of it; the note says which part.

75 entries.

## Substantive (not an immediate consequence of a known theorem) (16)

### [A045764](https://oeis.org/A045764): Meeussen's numbers are not values of W(n) = n − d(n) − φ(n) + 1

- Problem: [NT-B10.3](NT/B10.3/README.md) (proved, new). Lean: Lean proof, [`B10_3_mathlib.lean`](NT/B10.3/B10_3_mathlib.lean).
- Prior art: OEIS A045764 lists exactly these numbers and still labels them a conjecture; our result proves every odd term below 1000 (A045764 also contains the even term 2, which our result does not cover). Worth an OEIS comment.
- Draft comment:

  > The conjecture is true for every odd term below 1000: none of them is a value of W(n) = n - d(n) - phi(n) + 1, and the odd non-values below 1000 are exactly 86 numbers 13, 67, 93, 123, ..., 973, 997. For n >= 3, W(n) is odd only if n is an odd square or an even nonsquare, and the bounds phi(n) <= n/2, d(n) <= 2*sqrt(n) (n even) and phi(k^2) <= k^2*(1 - 1/p) with p the least prime factor of k (k odd composite) show that W(n) < 1000 forces n <= 1001^2, which a sieve covers. The even term 2 is not covered by this argument. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/NT/B10.3.

### [A094787](https://oeis.org/A094787): every prime is a least prime p with p + n a perfect power

- Problem: [OEIS-A094787](OEIS/A094787/README.md) (proved, new). Lean: Lean proof, [`A094787_mathlib.lean`](OEIS/A094787/A094787_mathlib.lean).
- Prior art: Short counting argument; no source found.
- Draft comment:

  > The conjecture is true: for a prime q and m > q put n = m^2 - q; then p + n is not a square for any prime p < q, since (m-1)^2 < m^2 - q + 2, so a(n) = q unless [m^2 - q + 2, m^2 - 1] contains a non-square perfect power. These windows are disjoint for different m, and there are only O(M^(2/3)*log M) non-square perfect powers up to M^2, so some m > q works. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A094787.

### [A100682](https://oeis.org/A100682): exception list of Greathouse's formula is incomplete

- Problem: [OEIS-A100682](OEIS/A100682/README.md) (disproved, new). Lean: Lean proof, [`A100682_mathlib.lean`](OEIS/A100682/A100682_mathlib.lean).
- Prior art: No source gives further exceptions. Note: the comment's formula only matches the entry's offset under the shifted reading the README uses.
- Draft comment:

  > Reading the formula as floor(binomial(n,4)^(1/4)) = floor((n - 3/2)/24^(1/4)), the reading that reproduces the listed exceptions 6, 17, 2403, 5318, the conjecture is false: n = 634027531 (index 634027528 of this sequence) is a further exception, with floor(binomial(n,4)^(1/4)) = 286454272 but floor((n - 3/2)/24^(1/4)) = 286454273. Further exceptions in the same reading are 1705327318, 55292025086, ..., near continued-fraction convergents of 384^(1/4). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A100682.

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

### [A210445](https://oeis.org/A210445): a(n) < n for n > 1 and a(n) < n/2 for n > 47 (least k with kn practical)

- Problem: [OEIS-A210445](OEIS/A210445/README.md) (proved, new). Lean: Lean proof, [`A210445_mathlib.lean`](OEIS/A210445/A210445_mathlib.lean).
- Prior art: No proof found. The argument uses Stewart-Sierpinski plus an explicit practical family {2^a*105, 2^a*165} and a finite check for 47 < p < 2881; not deep but more than a line.
- Draft comment:

  > The conjecture is true. By the Stewart-Sierpinski criterion, if n is composite with largest prime factor P, then k = 2^t with 2^t < P <= 2^(t+1) makes kn practical and k < P <= n/2; for prime p the same k gives a(p) < p. For primes p > 47, a(p) < p/2 follows from the practical family k = 2^a*105, 2^a*165 (for p > 11, kp is practical iff p <= 1 + sigma(k)) for large p and a direct check of the remaining primes. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A210445.

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

### [A229487](https://oeis.org/A229487): Finucane's lists for the iteration n → φ(n) + 1 are complete

- Problem: [NT-B41.5](NT/B41.5/README.md) (proved, new). Lean: Lean proof, [`B41_5_mathlib.lean`](NT/B41.5/B41_5_mathlib.lean).
- Prior art: Proves the terms a(3)=12 and a(4)=30 of OEIS A229487, which is labelled conjectural; worth an OEIS comment. Erdos #409 forum could not be read.
- Draft comment:

  > The conjectured terms a(3) = 12 and a(4) = 30 are correct: the numbers whose trajectory under n -> phi(n) + 1 ends at 5 are exactly 5, 8, 10, 12, and those ending at 7 are exactly 7, 9, 14, 15, 16, 18, 20, 24, 30. The set reaching a prime q is built from q by repeatedly solving phi(n) = m - 1; the inverse totient sets needed are phi^(-1)(4) = {5, 8, 10, 12}, phi^(-1)(6) = {7, 9, 14, 18} and phi^(-1)(8) = {15, 16, 20, 24, 30}, while 7, 9, 11, 13, 14, 15, 17, 19, 23, 29 are not totients. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/NT/B41.5.

## Immediate from a known theorem or short argument, still open in OEIS (59)

### [A004050](https://oeis.org/A004050): only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways

- Problem: [OEIS-A004050](OEIS/A004050/README.md) (proved, partly-known). Lean: Lean (partial), [`A004050_mathlib.lean`](OEIS/A004050/A004050_mathlib.lean).
- Prior art: Two representations give 3^d - 2^a = 3^b - 2^c; for b, c >= 1 Bennett's Thm 1.1 (Stroeker-Tijdeman) leaves only c in {1, -5, -13}, i.e. 11, 35, 259; the zero-exponent cases (5, 17) are elementary. So the result follows from the literature without Ellison; not stated for A085634 anywhere found.
- Draft comment:

  > The conjecture is true: only 5, 11, 17, 35, 259 are 2^a + 3^b in two ways (see A085634). If 2^a + 3^b = 2^c + 3^d with a > c, lifting the exponent gives b < d <= a and |2^a - 3^d| <= 4a, and Ellison's 1971 bound |2^x - 3^y| > 2^x*e^(-x/10) (x >= 12, x not in {13, 14, 16, 19, 27}) forces a <= 27, leaving a finite search. The cases with b, c >= 1 (giving 11, 35, 259) also follow from the solution of Pillai's equation by Stroeker and Tijdeman (1982), in the form of M. A. Bennett (2003), Thm. 1.1. A partial Lean 4 verification (Ellison's 1971 bound outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A004050.

### [A005408](https://oeis.org/A005408): one-coach primes and the first q odd numbers

- Problem: [OEIS-A005408](OEIS/A005408/README.md) (proved, partly-known). Lean: Lean proof, [`A005408_mathlib.lean`](OEIS/A005408/A005408_mathlib.lean).
- Prior art: The prime direction is the Coach theorem (phi(b) = 2ck, cited in A216371) plus counting; the converse (composite b excluded) is a short extra step. Same conjecture also in A216371.
- Draft comment:

  > Reading the top row as the set of entries of the coach of 1 (Hilton-Pedersen, see A216371), the conjecture is true. For odd b the map a -> odd part of (b - a) permutes the odd numbers below b/2 that are coprime to b, and the coaches are its cycles; there are exactly q odd numbers below b/2, all coprime to b when b is prime, while a composite odd b has an odd prime factor below b/2 that no coach contains. For prime b this also follows from the Coach theorem phi(b) = 2ck quoted in A216371. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A005408.

### [A008676](https://oeis.org/A008676): coefficients of 1/((1-x^3)(1-x^5)) as a floor formula

- Problem: [OEIS-A008676](OEIS/A008676/README.md) (proved, partly-known). Lean: Lean proof, [`A008676_mathlib.lean`](OEIS/A008676/A008676_mathlib.lean).
- Prior art: Akinari's formula in the entry equals Layman's by floor(2(n+3)/3) = n+2-ceil(n/3), ceil(n/3) = floor((n+2)/3), floor(3(n+3)/5) = n+1-floor(2n/5); so the entry already effectively contains it (Akinari's formula is not proved there).
- Draft comment:

  > The conjecture is true for all n >= 0: by the g.f., a(n) = a(n-3) + a(n-5) - a(n-8) for n >= 8, and the floor formula satisfies the same recurrence (it increases by 1 when n increases by 15) and agrees with a(n) for n = 0..7. It equals T. Akinari's formula a(n) = floor((2n+5)/5) - floor((n+2)/3) above by elementary floor identities. A proof formally verified in Lean 4 (starting from the recurrence implied by the g.f.) is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A008676.

### [A025060](https://oeis.org/A025060): with signs allowed, i·j + j·k + k·i takes every integer

- Problem: [OEIS-A025060](OEIS/A025060/README.md) (trivial or misstated, new). Lean: Lean proof, [`A025060.lean`](OEIS/A025060/A025060.lean).
- Prior art: Two explicit families of triples; trivial.
- Draft comment:

  > The conjecture is true: (i, j) = (2, -1) gives ij + jk + ki = k - 2, which covers every integer except -3, -2, 0 (k not in {-1, 0, 2}), and (i, j) = (4, -3) gives k - 12, which covers -3, -2, 0 with k = 9, 10, 12. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A025060.

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

### [A139043](https://oeis.org/A139043): sum of composites ≤ 10^n versus 10^n(10^n+1)/2 - 1 - (10^n)^2/(2 log 10^n - 1)

- Problem: [OEIS-A139043](OEIS/A139043/README.md) (proved, partly-known). Lean: Lean (partial), [`A139043_mathlib.lean`](OEIS/A139043/A139043_mathlib.lean).
- Prior art: The expansion is in the literature; the conclusion for this entry (ratio true, difference false) is not stated.
- Draft comment:

  > Read as asymptotic equivalence (ratio -> 1), both statements are true: the main one because both sides are ~ x^2/2 with x = 10^n, since the sum S(x) of primes <= x is at most x*pi(x), and the parenthetical one by the prime number theorem. Read as difference -> 0, both are false: with L = log x, S(x) = x^2/(2L) + x^2/(4L^2) + x^2/(4L^3) + O(x^2/L^4) (cf. C. Axler, arXiv:1606.06874), while x^2/(2L - 1) = x^2/(2L) + x^2/(4L^2) + x^2/(8L^3) + O(x^2/L^4), so the difference grows like x^2/(8L^3). A partial Lean 4 verification (the main statement in the ratio reading; the parenthetical claim and the difference reading outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A139043.

### [A140869](https://oeis.org/A140869): if h is not a term, then 4h + 5 is prime

- Problem: [OEIS-A140869](OEIS/A140869/README.md) (proved, partly-known). Lean: Lean proof, [`A140869.lean`](OEIS/A140869/A140869.lean).
- Prior art: Sundaram-type argument; the specific statement is not written anywhere found.
- Draft comment:

  > The conjecture is true: if 4h + 5 = (2a+1)(2b+1) with a, b >= 1, then a + b is even and h = ab + (a+b)/2 - 1 = floor((2ab + a + b - 2)/2) = T(max(a,b), min(a,b)), so every h with 4h + 5 composite is a term (a Sundaram-type argument). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A140869.

### [A144652](https://oeis.org/A144652): if h is not a term, then 4h + 1 is prime (h ≥ 1)

- Problem: [OEIS-A144652](OEIS/A144652/README.md) (proved, partly-known). Lean: Lean proof, [`A144652.lean`](OEIS/A144652/A144652.lean).
- Prior art: Sundaram-type argument; the specific statement is not written anywhere found.
- Draft comment:

  > The conjecture is true for h >= 1 (h = 0 is not a term and 4h + 1 = 1): if 4h + 1 = (2a+1)(2b+1) with a, b >= 1, then a + b is even and h = ab + (a+b)/2 = T(max(a,b), min(a,b)), so every h >= 1 with 4h + 1 composite is a term (a Sundaram-type argument). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A144652.

### [A165640](https://oeis.org/A165640): a(n) = floor(4(n+4)/5) - floor(2(n+4)/3)

- Problem: [OEIS-A165640](OEIS/A165640/README.md) (proved, new). Lean: Lean proof, [`A165640_mathlib.lean`](OEIS/A165640/A165640_mathlib.lean).
- Prior art: No proof found.
- Draft comment:

  > The conjecture is true for n >= 1. With x, y, z the multiplicities of -2, 1, 3, the conditions are 3x = n - 3 + 2z and y = n - x - z >= 0, so for n >= 3, a(n) is the number of z == n (mod 3) in [0, floor((2n+3)/5)]; this count and the floor formula are both degree-1 quasi-polynomials of period 15, so agreement on two periods (and at n = 1, 2) proves the identity. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A165640.

### [A167230](https://oeis.org/A167230): entries of exp(Sierpiński triangle)/e are Bell numbers

- Problem: [OEIS-A167230](OEIS/A167230/README.md) (proved, new). Lean: Lean proof, [`A167230_mathlib.lean`](OEIS/A167230/A167230_mathlib.lean).
- Prior art: No proof found. Short proof: the Sierpinski matrix is the zeta matrix of the Boolean lattice (Lucas), so its m-th power has entries m^j, and Dobinski's formula gives Bell(j).
- Draft comment:

  > The conjecture is true: entry (n,k) is Bell(j) = A000110(j) if the binary 1's of k are among those of n, with j = A000120(n) - A000120(k), and 0 otherwise. By Lucas's theorem the Sierpinski triangle S is the Kronecker power of [[1,0],[1,1]], so S^m has entries m^j or 0, and exp(S)(n,k) = Sum_{m>=0} m^j/m! = e*Bell(j) by Dobinski's formula. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A167230.

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

### [A182532](https://oeis.org/A182532): Carmichael numbers divisible by 7 and 17: the four residue classes mod 120

- Problem: [OEIS-A182532](OEIS/A182532/README.md) (proved, new). Lean: Lean proof, [`A182532_mathlib.lean`](OEIS/A182532/A182532_mathlib.lean).
- Prior art: Entry still presents conjectures (1)-(4); they follow from Korselt (C = 1 mod 48) plus CRT with 119 | C and the residue mod 5.
- Draft comment:

  > Conjectures (1)-(4) are true by Korselt's criterion: 6 and 16 divide C - 1, so 48 | C - 1, and with C = 119m, 119 == 23 (mod 48) gives m == 23 (mod 48), i.e., m == 7 (mod 8) and m == 2 (mod 3). Since C == 9m (mod 10), the last digit of C fixes m mod 5, giving m == 119, 95, 47, 71 (mod 120) for C == 1, 5, 3, 9 (mod 10). A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A182532.

### [A187011](https://oeis.org/A187011): det(|p_i − p_j|) over the first n primes

- Problem: [OEIS-A187011](OEIS/A187011/README.md) (proved, partly-known). Lean: paper proof, [`A187011_mathlib.lean`](OEIS/A187011/A187011_mathlib.lean).
- Prior art: Sign part is the weighted-path case of the Bapat-Kirkland-Neumann tree formula; growth part a routine sieve corollary; no prior proof of the A187011 conjecture found.
- Draft comment:

  > The conjecture is true: Both parts are true. For n ≥ 2, a(n) = (−1)^(n−1) · 2^(n−2) · (p_n − 2) · ∏_{i<n} (p_{i+1} − p_i), so the sign part is immediate. The growth part follows from this formula and a sieve upper bound for prime pairs. (proof: https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A187011). - _<Name>_, <Mon DD YYYY>

### [A192205](https://oeis.org/A192205): a(n)^(1/n) → 16√3/9 for the coefficient sum of (1-x-x^2+x^3)^n

- Problem: [OEIS-A192205](OEIS/A192205/README.md) (proved, new). Lean: Lean proof, [`A192205_mathlib.lean`](OEIS/A192205/A192205_mathlib.lean).
- Prior art: No source found for this specific limit. It is immediate: l2 <= l1 <= sqrt(3n+1) l2 with l2^2 = binomial(4n,n) (stated in the entry); equivalently Gelfand's spectral-radius formula in the Wiener algebra gives max_{|z|=1} |P| = 16 sqrt(3)/9.
- Draft comment:

  > The conjecture is true: with l1 = a(n) and l2^2 the sum of the squared coefficients of P^n, P = 1 - x - x^2 + x^3, Cauchy-Schwarz gives l2 <= l1 <= sqrt(3n+1)*l2, and by Parseval l2^(1/n) tends to max_{|z|=1} |P(z)|. Since |P(e^(it))|^2 = 64s^2(1-s) with s = sin^2(t/2), maximal at s = 2/3, this maximum is sqrt(256/27) = 16*sqrt(3)/9; the identity l2^2 = binomial(4n,n) with Stirling's formula gives the same limit. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A192205.

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

### [A210529](https://oeis.org/A210529): a(n) is defined for every n (Dirichlet)

- Problem: [OEIS-A210529](OEIS/A210529/README.md) (proved, partly-known). Lean: Lean proof, [`A210529_mathlib.lean`](OEIS/A210529/A210529_mathlib.lean).
- Prior art: Schmidt's construction in A210708 is the key step; requiring a(n) prime then needs only Dirichlet's theorem for the progression p mod Q. Not stated anywhere found.
- Draft comment:

  > The conjecture is true by Dirichlet's theorem: if p = prime(n) and Q is the product of the primes below sqrt(p), then gcd(p, Q) = 1, so there are infinitely many primes a == p (mod Q), and any such a != p has Q | a - p | a^2 - p^2. This adds the primality requirement to E. M. Schmidt's proof in A210708. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A210529.

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

- Problem: [OEIS-A215462](OEIS/A215462/README.md) (proved, partly-known). Lean: Lean (partial), [`A215462_mathlib.lean`](OEIS/A215462/A215462_mathlib.lean).
- Prior art: Conjecture 1 is the classical 1984 AIME Problem 14 fact. Conjecture 2 (eventual ordering) follows from Chebyshev plus the Brun-Selberg upper bound for Goldbach representations; no source states it for these sequences.
- Draft comment:

  > Both conjectures are true. For n > 19, one of 9, 25, 35 (residues 0, 1, 2 mod 3) leaves 2n - c an odd multiple of 3 that is >= 9 when n >= 22, and 40 = 25 + 15, 42 = 15 + 27 (the classical fact that every even number > 38 is a sum of two odd composites). For the second, A002372(n) + A215461(n) + a(n) = n gives A215461(n) = 2(P - G) and a(n) = n - 2P + G, with P the number of odd primes below 2n and G = A002372(n), and both inequalities follow from n/log n << P = o(n) (Chebyshev) and G << n/log^2 n (Brun-Selberg sieve). A partial Lean 4 verification (the first conjecture; the second outside Lean) and the full argument are at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A215462.

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

### [A227553](https://oeis.org/A227553): number of solutions of x^2 - y^2 - z^2 ≡ 1 (mod p^s)

- Problem: [OEIS-A227553](OEIS/A227553/README.md) (proved, partly-known). Lean: Lean proof, [`A227553_mathlib.lean`](OEIS/A227553/A227553_mathlib.lean).
- Prior art: Odd prime powers: immediate from Cohen's formula as given in Toth 2014 Prop. 14 (linked from the entry). The 2-power cases a(2) = 4, a(2^s) = 2^(2s-1) are not covered there.
- Draft comment:

  > The conjecture is true. For odd p, u = x - y, v = x + y turn the equation into uv = 1 + z^2, giving p(p-1) + 2p = (p+1)p solutions mod p if p == 1 (mod 4) and p(p-1) if p == 3 (mod 4), and every solution is nonsingular, so it has p^2 lifts at each step (Hensel). For 2^s with s >= 2, x must be odd, and counting the square roots of 1 + y^2 + z^2 over the pairs (y, z) gives a(4) = 8 and a(2^s) = 2^(2s-1); the odd prime-power cases also follow from E. Cohen's formula as given in Toth (2014), Prop. 14. A proof formally verified in Lean 4 is at https://github.com/zzyzek/ShotgunConjectures/tree/main/OEIS/A227553.

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

## Known elsewhere, still labelled a conjecture in OEIS (17): cross-reference only

- [A008578](https://oeis.org/A008578): 1 and the primes are exactly the k with sigma(k) > k·Omega(k). Known from: Already proved in Lean by others before this project: otoi-lab/oeis-lean-proofs, OeisProofs/FC/A8578.lean (Lean 4; 'Solved by Claude (Anthropic) prompted by otoinobuo'), first commit 2026-10-12; marked solved in google-deepmind/formal-conjectures FormalConjectures/OEIS/8578.lean. This project proved it independently; the OEIS entry still says Conjecture. Missed by the 2026-11-04 review, which did not search formal-conjectures. No source found for sigma(k) <= k Omega(k) on composites; elementary proof.
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

