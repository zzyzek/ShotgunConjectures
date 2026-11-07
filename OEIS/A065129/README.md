# OEIS A065129: if the period of sqrt(m) divides m, it is even or has only prime factors 1 mod 4

**Source.** [A065129](https://oeis.org/A065129): a(n) = least m with m/A003285(m) = n (A003285(m) = period of
the continued fraction of sqrt(m)), or 0. "Conjecture: A003285(m) = even or A004613, if m is divisible by
A003285(m). [This sentence appears to be saying that all odd terms of this sequence are in A004613.]"
(A004613: numbers all of whose prime factors are 1 mod 4.) (OEIS text, CC BY-SA 4.0, fetched 2026-11-07.)

**Reading.** Two readings: (R1) for every nonsquare m with l = A003285(m) | m, l is even or l is in A004613;
(R2, the editor's) every odd m with l | m (in particular every odd term of A065129) is in A004613. Both hold.

**Result.** True in both readings.

**Argument.** If l is odd then x^2 - m y^2 = -1 has a solution (classical: for odd period the convergent
p_{l-1}/q_{l-1} satisfies p^2 - m q^2 = (-1)^l = -1). Then x^2 = -1 mod p for every prime p | m, so p = 2 or
p = 1 mod 4. (R1) If l | m and l is odd, every prime factor of l is an odd prime dividing m, so it is 1 mod 4.
(R2) If m is odd and l | m then l is odd, and every prime factor of m is odd, so it is 1 mod 4.

**Evidence.**
- Lean (Mathlib): [`A065129_mathlib.lean`](A065129_mathlib.lean). `prime_dvd_of_negPell` (x^2 + 1 = m y^2 and
  odd prime p | m imply p % 4 = 1, via `ZMod.exists_sq_eq_neg_one_iff`), `odd_divisor_A004613` (R1 given the
  Pell solution), `odd_m_A004613` (R2 given the Pell solution). `tools/leancheck-mathlib.sh`: OK, no warnings;
  axioms propext, Classical.choice, Quot.sound; no sorry, no native_decide.
- [`certificate/check.py`](certificate/check.py): for every nonsquare m < 300000, odd period gives
  p^2 - m q^2 = -1 at the end of the first period, and both readings hold (16814 cases with l | m).
- Outside Lean: the classical fact that an odd period gives a solution of x^2 - m y^2 = -1 (Legendre; standard in texts on
  continued fractions and the Pell equation).

**Review level.** `lean-witness` (the arithmetic step is in Lean; the continued-fraction step is classical).

**Prior art.** Checked 2026-11-07. The entry gives no proof; the argument is the textbook link between odd
period and the negative Pell equation, so the result is immediate. Not in google-deepmind/formal-conjectures or
otoi-lab/oeis-lean-proofs (local clones, 2026-11-06).
