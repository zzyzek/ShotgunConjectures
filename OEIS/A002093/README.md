# OEIS A002093: highly abundant numbers are eventually divisible by every k

**Source.** [A002093](https://oeis.org/A002093), highly abundant numbers: n with sigma(n) > sigma(m) for all m < n.
Comment (Jaycob Coleman, Oct 16 2013): "Conjecture: (a) Every highly abundant number > 10 is practical (A005153).
(b) For every integer k there exists A such that k divides a(n) for all n > A." Daniel Fischer proved (b) for
k = 2, 6, 12 (thresholds 3, 20, 630). (OEIS text, CC BY-SA 4.0, entry as of Aug 18 2026, checked 2026-11-07.)

**Result.**
- (b) True (ours): for every prime power q^e, all sufficiently large highly abundant n are divisible by q^e; hence
  by every k.
- (a) Proved informally by D. Eppstein (blog, Feb 26 2015, revised after 630 was found); that case analysis is cited,
  not re-derived here.

**Argument for (b).** For a prime s with s^a || n and the replacement s^a -> s^(a+i) (i >= 1), sigma is multiplied by
(s^(a+i+1)-1)/(s^(a+1)-1) >= s^i (1 + delta_s(a)), delta_s(a) = (1 - 1/s)/(s^(a+1) - 1) > 0, decreasing in a. For
s^a -> s^(a-j), sigma is multiplied by (s^(a-j+1)-1)/(s^(a+1)-1) >= s^(-j)(1 - s^(j-a-1)); for s^1 -> s^0 by
1/(s+1). A highly abundant n admits no m < n with sigma(m) >= sigma(n).
Fix q, e and suppose v_q(n) <= e-1 for infinitely many highly abundant n; let delta = delta_q(e-1). Fix a prime
r != q.
1. If v_r(n) is unbounded along them: pick i, j >= 1 with q^i < r^j < q^i(1 + delta/2) (exists since
   log r / log q is irrational). Then m = n q^i / r^j < n and sigma(m)/sigma(n) >= (1+delta)/(1+delta/2) *
   (1 - r^(j-a-1)) > 1 once a = v_r(n) is large. Contradiction.
2. If v_r(n) <= B but the largest prime factor P of n is unbounded: let eps = delta_r(B). For P large pick
   i >= 1, k >= 0 with P/(1 + delta/2) < q^i r^k < P (the numbers q^i r^k have consecutive ratios -> 1). Then
   m = n q^i r^k / P < n and sigma(m)/sigma(n) >= (1+delta) q^i r^k / (P+1) > (1+delta)/(1+delta/2) * P/(P+1) > 1.
3. If v_r(n) and P are both bounded: n is P-smooth with P bounded, so some prime s != q has v_s(n) unbounded; apply
   1 with s in place of r.
So v_q(n) >= e for all large highly abundant n.

**Evidence.**
- `certificate/check.py` (run on the OEIS b-file, 10000 terms): last terms not divisible by k = 2, 3, 4, 5, 7, 8, 9,
  11, 13, 16, 25, 27, 32, 49 are 3, 20, 630, 3024, 47520, 540540, 8168160, 46781280, 37067738400, 1164544781400,
  1226737062541710720, 31672512601329600, 4648566756368995059600, 5753889678079110793457232000.
- Lean (Mathlib + lib/PNTPlus): [`A002093_mathlib.lean`](A002093_mathlib.lean). `A002093_partB`: for every k >= 1
  there is A such that every highly abundant n > A (defined as n >= 1 with sigma(m) < sigma(n) for 1 <= m < n) is
  divisible by k; `A002093_primePow` is the case q^e. The Lean proof replaces the density step of the argument above
  by the prime number theorem (a prime in (x, (1+eps)x), PNT+ `prime_between`): with G = sigma(q^(e-1)) and
  k = 2qG, take a prime s != q and j >= 1 with s^j | n, s^j large and (s-1) s^(v_s(n)-j) >= 4qG (a large prime
  factor with j = 1, or else a large exponent, since n is then smooth), and a prime Q with
  k s^j < (k+1) q Q < (k+1) s^j; then m = n q Q / s^j < n and sigma(m) >= sigma(n) (`ha_key`).
  Axioms: propext, Classical.choice, Quot.sound.
- Outside Lean: part (a) (Eppstein's case analysis, cited).

**Review level.** `lean-proof` for (b); (a) cited.

**Prior art.** Checked 2026-11-07: entry and Wikipedia (Fischer: 2, 6, 12 only; Alaoglu-Erdős 1944 list exponent
questions as open); D. Eppstein, "Highly abundant numbers", 11011110 blog, 2015-02-26 (part (a)). Not in
google-deepmind/formal-conjectures or otoi-lab/oeis-lean-proofs. No source for (b) for general k found; the argument
is elementary, so it may well be folklore.
