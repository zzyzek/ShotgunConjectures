# OEIS A027687: the digital root of a 4-perfect number divides it (partial: all 4-perfect numbers divisible by 6)

**Source.** [A027687](https://oeis.org/A027687): 4-perfect numbers, sigma(n) = 4n. "Conjecture: A010888(a(n))
divides a(n). Tested for n up to 36 incl." (Ivan N. Ianakiev, Oct 31 2013; A010888 = digital root.) (OEIS text,
CC BY-SA 4.0, fetched 2026-11-07.)

**Result (partial).** The conjecture holds for every 4-perfect number divisible by 6, in particular for all 36
known terms (all divisible by 6; 34 of them by 9). For general terms it is open: whether the list is complete,
and whether a 4-perfect number can avoid 3 or be odd, are open.

**Argument.** dr(N) = 1 + (N-1) mod 9 for N >= 1, so dr(N) = N mod 9 with 9 for 0. If 6 | N then N mod 9 is
0, 3 or 6, so dr(N) is 9 (then 9 | N), 3 or 6 (both divide N).

**What remains (reduction).** A counterexample N must be 4-perfect with 3 ∤ N, or odd. For even N with 3 ∤ N,
3 ∤ sigma(N) = 4N forces every prime p = 2 mod 3 (including 2) to an even exponent, so N = 2^a m with a even;
a = 2 gives sigma(4) = 7 | N. Then dr(N) is in {1, 2, 4, 5, 7, 8}; 1, 2, 4 divide N, 8 divides N unless a = 2,
in which case 7 | N. So an even counterexample has (N = 5 mod 9, 5 ∤ N), (N = 7 mod 9, 7 ∤ N), or
(N = 8 mod 9, a = 2). An odd counterexample has N = 2, 4, 6, 8 mod 9, or N = 5, 7 mod 9 without the factor 5, 7.

**Evidence.**
- Lean (core): [`A027687.lean`](A027687.lean). `dr` is the iterated decimal digit sum (A010888's definition);
  `dr_eq` (closed form), `dr_dvd_of_six_dvd` (6 | N implies dr(N) | N), `known_six_dvd` and
  `known_conjecture` (the 36 b-file terms). `tools/leancheck.sh`: OK, no warnings, axioms propext, Quot.sound.
  No sorry, no native_decide.
- [`certificate/b027687.txt`](certificate/b027687.txt): the b-file (36 terms); sigma(N) = 4N rechecked with sympy.
- Not verified in Lean: that the 36 numbers are 4-perfect (sympy) and the paper reduction above.
- Outside Lean: the general conjecture (open) and the case reduction for 3 ∤ N.

**Review level.** `lean-proof` for the stated partial theorem.

**Prior art.** Checked 2026-11-07. The entry gives only the test to n = 36. K. A. Broughan and Q. Zhou, "Divisibility by 3 of even multiperfect numbers of abundancy 3 and 4", J. Integer Seq. 13 (2010) 10.1.5, ask whether every even 4-perfect number is divisible by 3 and prove special cases (Carmichael: four distinct primes; flat 4-perfect numbers with exponent 1 mod 12); a yes answer plus nonexistence of odd 4-perfect numbers would settle the conjecture.
Not in google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).
