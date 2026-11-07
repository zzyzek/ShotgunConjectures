# OEIS A081097: the "recurrence of order m" conjecture

**Source.** [A081097](https://oeis.org/A081097), numbers n with n^2 = (1/5)(n + floor(sqrt(5) n floor(sqrt(5) n))).
Comment: "Conjecture: if m is an integer and sqrt(m) is irrational, the sequence of n such that n^2 = (1/m)*(n +
floor(sqrt(m)*n*floor(sqrt(m)*n))) always satisfies a recurrence of order m." The entry's own m = 5 formula is a
four-case recurrence, and Barker's empirical g.f. has a denominator of degree 9. (OEIS text, CC BY-SA 4.0, entry as
of Jun 24 2013, checked 2026-11-07.)

**Reading.** "Recurrence of order m" is not defined: the m = 5 example splits n by residue mod 4, not 5, and its
minimal constant-coefficient recurrence (if Barker's g.f. is right) has order 9 > 5. We prove the precise version:
for every non-square m the solution sequence has a rational generating function (satisfies a linear recurrence
with constant coefficients), and is an interleaving with period P(m) of sequences b(t+1) = 2u b(t) - b(t-1) + c.
P(m) = 1, 1, 4, 2, 1, 1, 2, 2 for m = 2, 3, 5, 6, 7, 8, 10, 11 (certificate/sols.py), so P(m) is not m.

**Result.** Misstated (vague); corrected statement true.

**Argument.** Let k = floor(sqrt(m) n), f = sqrt(m) n - k in (0,1), D = m n^2 - k^2 = 2fk + f^2 > 0. Then
floor(sqrt(m) n k) = k^2 + floor(fk) and floor(fk) = floor((D - f^2)/2), which is D/2 - 1 for D even and (D-1)/2 for
D odd. The equation m n^2 - n = k^2 + floor(fk) becomes D = 2n - 2 or D = 2n - 1, i.e.
(m n - 1)^2 - m k^2 = 1 - 2m or 1 - m. Conversely such (n, k) with n >= 1 has 0 < D <= 2n - 1 < 2k + 1, so
k = floor(sqrt(m) n). So the solutions are the generalized Pell solutions X^2 - m Y^2 in {1-m, 1-2m} with
X = mn - 1. These form finitely many orbits under the fundamental unit u + v sqrt(m); the condition X = -1 mod m is
periodic along each orbit, so n runs through finitely many sequences A_i eps^t + B_i eps^(-t) + 1/m. Sorted, they
interleave periodically and each satisfies b(t+1) = 2U b(t) - b(t-1) + c, so the g.f. is rational.

**Evidence.**
- `certificate/pell.py`: the reduction holds for all non-square m < 40 and n < 2*10^5; for m = 5 the orbits of
  9 + 4 sqrt(5) on (5n - 1, k) give exactly the 23 data terms.
- `certificate/sols.py`: first solutions for m = 2, 3, 5, 6, 7, 8, 10, 11.
- Lean: none. Outside Lean: the reduction (short, above) and generalized Pell theory (finitely many classes).

**Review level.** `rechecked` (reduction checked numerically).

**Prior art.** Checked 2026-11-07: entry (no history changes since 2013 beyond Barker's g.f.); not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs. The Pell reduction is ours (routine).
