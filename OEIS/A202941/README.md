# OEIS A202941, A178473, A203484 (and row sums A203278, A203509, A203498): Shevelev's generalized binomials at the first p-row

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

**Evidence.** Lean (Mathlib), all six claims, checked 2026-11-06:
[A202941_mathlib.lean](A202941_mathlib.lean), [A203278](../A203278/A203278_mathlib.lean),
[A203484](../A203484/A203484_mathlib.lean), [A203498](../A203498/A203498_mathlib.lean),
[A178473](../A178473/A178473_mathlib.lean), [A203509](../A203509/A203509_mathlib.lean)
(`A202941_main`, ...), each an application of `shevelev_row` in the library module
`lib/OpenProblemsLib/ShevelevFactorial.lean`. The library defines Q^(t)_m (`shevQ`; `shevQ_succ_eval`
is the entry's recursion and `shevQ_unique` says any family with it is `shevQ`), n!^(t)
(`shevFact`, lcm of coefficient denominators) and C^(t)(n,m) (`shevBinom`). Its route differs from
the Stirling argument above in two places: the power sums are Mathlib's Faulhaber polynomials with
p-integrality from Mathlib's von Staudt–Clausen theorem (`Spoly_mem`), and S_(p−1), S_(2p−2) fail
to be p-integral because Σ_{i≤p} i^k ≡ −1 (mod p) while a p-integral polynomial takes congruent
values at p and 0 (`Spoly_not_mem`); Newton's identity is used in the recurrence form
m Q_m = Σ_{a+b=m, b≥1} Q_a S_{tb} (`newton`), not as a partition sum. Axioms: propext,
Classical.choice, Quot.sound. Outside Lean: none. Only the Reading above remains (v_p ≥ 1 for
"multiple of p"; the row-sum congruence is stated for every integer equal to the rational row sum).
`certificate/shev.py` computes n!^(t) exactly from the definition and reproduces the data of
A202367, A202368, A202369; `certificate/shevcheck.py 50` checks every claim for all primes whose
row is ≤ 50 (t = 2: p ≤ 103; t = 3: p ≤ 151; t = 4: p ≤ 197); all inner entries there are integers.

**Review level.** `lean-proof` (all six claims; 2026-11-06).

**Prior art.** Checked 2026-11-06: the six entries and A202367–A202369 still state conjectures;
web search found nothing; not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs.
The ingredients (Stirling expansion of power sums, Newton's identities, Fermat's sum of powers)
are standard.
