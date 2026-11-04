# OEIS A129454: p-adic valuation of a triple gcd product (true after an index shift)

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

**Evidence.**
- `certificate/a129454.py`: computes a(n) for n ≤ 24 and confirms the shifted formula for all
  primes ≤ 23; lists the literal failures.
- [`A129454.lean`](A129454.lean): `decide` checks of a(n) for n ≤ 6 against the shifted
  formula (p = 2, 3, 5) and the literal failure at n = 3. The general double-counting step is
  outside Lean.
- Lean (Mathlib): [`A129454_mathlib.lean`](A129454_mathlib.lean), `A129454_main`: for every prime p and n ≥ 1, `padicValNat p (a n)` = Σ_{t=1}^{n} floor((n-1)/p^t)^3 for a(n) = ∏_{i,j,k ≤ n-1} gcd(i,j,k), and the literal formula fails at n = 3, p = 3. Nothing outside Lean.

**Review level.** `lean-proof` for the shifted statement (Mathlib file above).

**Prior art.** Verdict partly-known, immediate (OEIS status conjecture; searched 2026-11-04). The 2-D analogue is confirmed in A092287; the 3-D case and the index correction (n-1 for n) are not stated anywhere found. Sources: [OEIS A129454 (fetched 2026-11-04)](https://oeis.org/A129454): still says Conjecture, with floor(n/p^t) (off by one); [OEIS A092287 (fetched 2026-11-04)](https://oeis.org/A092287): 2-D analogue: 'The conjecture is correct' (C. R. Greathouse IV, Apr 2013). Searched: OEIS entry (text format); OEIS search for references; OEIS edit history; OEIS A092287, A129453, A129455.
