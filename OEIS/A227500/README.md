# OEIS A227500: (b(n) - a(n))/c(n) is 0, 0 followed by the Fibonacci numbers

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

**Evidence.**
- Lean (Mathlib): [`A227500_mathlib.lean`](A227500_mathlib.lean). `r B` is the transform; a(n)/c(n) is
  `r bernoulli n` and b(n)/c(n) is `r bernoulli' n` (Mathlib's `bernoulli` has B(1) = -1/2, `bernoulli'` has
  B(1) = +1/2). Theorems: `A227500_diff` (r bernoulli' (n+2) - r bernoulli (n+2) = fib n), `A227500_diff_small`
  (n = 0, 1), `A227500_den` (equal reduced denominators), `A227500_main` ((num r2(n) - num r1(n))/den r1(n) =
  fib (n-2) for n >= 2, 0 otherwise). Check: `tools/leancheck-mathlib.sh`, exit 0, no warnings; axioms propext,
  Classical.choice, Quot.sound. No `sorry`, no `native_decide`.
- [`certificate/check.gp`](certificate/check.gp): reproduces the 31 data terms from the definition and checks
  equal denominators and (b-a)/c = F(n-2) for n <= 300 (exit 0).
- Outside Lean: that Mathlib's `bernoulli` and `bernoulli'` equal A027641/A027642 and A164555/A027642 (the standard
  conventions; check.gp reproduces the data terms with PARI's `bernfrac`).

**Review level.** `lean-proof`.

**Prior art.** Checked 2026-11-06. The entry and its history (revisions to #20) keep the statement as a conjecture,
confirmed numerically for 100 terms; A228151 (the denominators) adds nothing on it. Not in
google-deepmind/formal-conjectures (no `FormalConjectures/OEIS/227500.lean`) or otoi-lab/oeis-lean-proofs. A web
search found no proof. The argument is a two-line linearity observation.
