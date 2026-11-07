# OEIS A055234: σ(x) = n·φ(x) is solvable for every n — partial result (all n <= 212; Lean for n <= 123)

**Source.** [A055234](https://oeis.org/A055234) (J. McCranie, 2000): "Smallest x such that sigma(x) = n*phi(x), or
-1 if no such x exists." Comment: "Conjecture: For each n, a(n) > 0." (F. Firoozbakht, 2004). Known terms:
data to n = 39; b-file (D. A. Corneth) to n = 50; comments give a(37), a(40) > 10^15 and upper bounds.
OEIS text, CC BY-SA 4.0, checked 2026-11-07.

**Result (partial).** For every n with 1 <= n <= 212 there is x with sigma(x) = n·phi(x); for n <= 123 this is
checked in Lean (`A055234_exists`), for 124 <= n <= 212 by exact sympy verification of explicit witnesses. The witnesses are not claimed minimal; for n <= 50 the search returns the b-file
value except at n = 23 (5650888320 instead of 1719277560, whose factorization uses a prime outside the pool).

**Method.** sigma(x)/phi(x) is multiplicative, with value r(p, k) = (p^{k+1} - 1)/((p - 1)^2 p^{k-1}) on p^k.
Take a pool of prime powers whose ratio has all prime factors in a fixed set: primes p <= 60 with
r(p, k) 60-smooth, primes p < 8.3·10^9 with p - 1 and p + 1 both 60-smooth (items.py), and for each prime
61 <= q <= 300 the primes p = q·m ± 1 with m 60-smooth (m <= 10^6) and p ∓ 1 smooth over the primes <= 300
(items2.py). For a target n, an integer program (scipy/HiGHS, ilp.py) chooses at most one exponent per prime so
that the exponent vectors of the ratios add up to that of n, minimising log x. Every solution is re-verified
with exact sigma and phi (sympy).

**Evidence.**
- Lean (Mathlib + OpenProblemsLib.ArithFactor): [`A055234_mathlib.lean`](A055234_mathlib.lean). A table of
  123 factorizations; `A055234_table` checks by `decide +kernel` that the bases are distinct primes (trial
  division), exponents positive, and sigF = n·phiF; `A055234_covers` checks every n <= 123 occurs;
  `A055234_exists`: for 1 <= n <= 123, ∃ x > 0, sigma 1 x = n * φ x. Checked with
  `tools/leancheck-mathlib.sh`: OK, axioms at most propext, Classical.choice, Quot.sound.
- [`certificate/witnesses212.txt`](certificate/witnesses212.txt) (n, x) for n <= 212, ILP logs ilp_q3.out,
  ilp_q4.out, scripts items.py, items2.py, ilp.py, mklean2.py (Lean table generator; tables beyond 123 rows
  exceeded the 6 GB check limit).
- Outside Lean: the witnesses for 124 <= n <= 212 (verified with exact sigma and phi in sympy). Not verified:
  minimality of the witnesses.

**Obstruction for all n.** The pool of a fixed finite set of primes bounds sigma(x)/phi(x) (the 60-smooth pool
reaches only n <= 123), so larger n need new primes p whose p ± 1 factor over the pool. A proof for every n would
need, for each prime q, primes p with q | p + 1 and the rest of p^2 - 1 smooth over a fixed set: smooth-shifted
primes in short ranges (Dickson/Schinzel-type), not available. See work/OEIS-A055234/REPORT.md.

**Review level.** `lean-witness`.

**Prior art.** Checked 2026-11-07: OEIS entry and b-file (to n = 50), google-deepmind/formal-conjectures and
otoi-lab/oeis-lean-proofs (no entry), web search (no general result on sigma(x) = k·phi(x)).
