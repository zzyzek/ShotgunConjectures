# OEIS A086844: a(n) - 4n is not ultimately periodic (Cloitre's conjecture is false)

**Source.** [A086844](https://oeis.org/A086844): odd m such that the orbit b(1) = m, b(k) = floor((1+sqrt 3) b(k-1))
contains only odd numbers. Comment (Benoit Cloitre, Aug 10 2003): for r(z) = (z + sqrt(z^2+4z))/2, z >= 1 an
integer, and a the sequence of odd m whose orbit under b(k) = floor(r(z) b(k-1)) is all odd, "the sequence a(n)-4n
... becomes ultimately periodic". Formula section (same author): "it seems that abs(a(n)-4n)<=9". The case z = 2 is
the entry itself, since r(2) = 1 + sqrt 3. (OEIS text, entry fetched 2026-11-07.)

**Result.** False for every z >= 1: a(n) - 4n is not ultimately periodic. The remark |a(n) - 4n| <= 9 also fails:
for z = 2, a(838) = 3363 and a(838) - 4*838 = 11.

**Argument.** Write r = r(z), D = z^2 + 4z, s = r - z.

1. (z+1)^2 < D < (z+2)^2, so D is not a square, sqrt D is irrational, and so is r. Also 0 < s < 1, and
   r^2 = z r + z.
2. *Linear recurrence.* For an integer x >= 1 put c = floor(r x) and f = r x - c, so 0 < f < 1 by irrationality.
   Then r c = r^2 x - r f = z(c + f) + z x - r f = z c + z x - s f, and 0 < s f < 1, so
   floor(r c) = z c + z x - 1. Hence the orbit satisfies b(k+2) = z b(k+1) + z b(k) - 1.
3. *Characterisation.* If b(k) and b(k+1) are odd, then z(b(k+1) + b(k)) is even and b(k+2) is odd. So m is a term
   iff m is odd and floor(r m) is odd.
4. *No period.* Suppose a(n+P) = a(n) + 4P for all n >= N (this is what ultimate periodicity of a(n) - 4n means).
   Then the set of terms is invariant under m -> m + Q, Q = 4P, above a(N). By step 3, for odd m >= a(N),
   floor(r m) and floor(r(m+Q)) have the same parity, so g(m) = floor(r(m+Q)) - floor(r m) is even. Every g(m) lies
   in the open interval (rQ - 1, rQ + 1), which contains at most one even integer, so g is a constant E on odd
   m >= a(N). Starting from one such m0 and stepping by Q (which keeps m odd), floor(r(m0 + tQ)) = floor(r m0) + tE,
   so |t(rQ - E)| < 1 for every t, hence rQ = E and r is rational, contrary to step 1.

Remark (outside Lean, not needed for the result): the terms are the odd m with frac(m (r - z)/2) in a fixed interval
of length 1/2 (step 3), and by Kesten's theorem (H. Kesten, Acta Arith. 12 (1966) 193-212) the counting error of an
irrational rotation in an interval is bounded only when the length lies in Z alpha + Z; so a(n) - 4n is in fact
unbounded, growing like log n (record values 11, 13, ..., 23 at n = 838, 2293, 11701, 31973, 163016, 445375,
2270575 for z = 2).

**Evidence.**
- Lean (Mathlib): [`A086844_mathlib.lean`](A086844_mathlib.lean). `A086844_conjecture_false`: with the entry's own
  orbit `orbit m` (⌊(1+√3)·⌋₊ iterated) and `A086844Pred m = Odd m ∧ ∀ k, Odd (orbit m k)`, there are no P > 0 and N
  with `Nat.nth A086844Pred (n+P) = Nat.nth A086844Pred n + 4P` for all n >= N. General z: `not_eventually_periodic`
  (via `floor_rec`, `b_rec`, `inSeq_iff`, `no_even_shift`, `irr_r`). Check: `tools/leancheck-mathlib.sh`, exit 0,
  no warnings; every theorem uses at most propext, Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check_A086844.py`](certificate/check_A086844.py): exact integer arithmetic (floor(r x) =
  (z x + isqrt(D x^2)) div 2); for z = 1..6 and odd m < 4000 checks the recurrence of step 2 over 30 steps and the
  characterisation of step 3; reproduces the listed terms; finds the record values of a(n) - 4n up to m = 2*10^7.
- Outside Lean: the witness a(838) = 3363 (certificate script only) and the unboundedness remark (Kesten's theorem).
  The main result (no ultimate periodicity) has nothing outside Lean beyond reading the definition.

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-07: the OEIS entry (conjecture and the |a(n)-4n| <= 9 remark still present, no
resolution recorded), google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (local clones, no
A086844). The floor identity of step 2 is the standard one for quadratic r with r^2 = z r + z; its use to settle
this conjecture was not found.
