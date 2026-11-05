# OEIS A182336: n + 1 ≤ a(n) ≤ 9n/8 + 1 for n > 96

**Source.** OEIS [A182336](https://oeis.org/A182336) (V. Shevelev, 2012): a(n) is the least
m ≥ n whose binary Hamming distance from n is 4. Conjecture: "for n > 96, n + 1 <= a(n) <= 9n/8
+ 1." (C. R. Greathouse IV, Apr 25 2012; OEIS text, CC BY-SA 4.0.)

**Result.** Proved. The threshold is sharp: a(96) = 111 > 109 = ⌊9·96/8⌋ + 1.

**Argument.** The lower bound holds because the distance from n to n is 0. For the upper bound,
build m with distance 4 and 8(m − n) ≤ n + 8. Hamming distance adds over a split into a high
part and a low part: D(2^K·a + s, 2^K·b + t) = D(a, b) + D(s, t) when s, t < 2^K. Write
n = 64q + r with 0 ≤ r < 64.
- r < 56: bit 3, 4 or 5 of n is 0. A table over r < 56 gives r < r' < 64 with r' ≤ r + 15 and
  D(r, r') = 4. Then m = 64q + r' works once n ≥ 112.
- r ≥ 56: let u = ⌊n/8⌋ and write u + 1 = 2^j·(2H + 1). Then j ≥ 3,
  n = 2^j·(16H + 7) + s and m = n + 2^j = 2^j·(16H + 8) + s with s < 2^j. So D(n, m) =
  D(7, 8) = 4, and 8·2^j ≤ 8(u + 1) ≤ n + 8. This case covers n = 2^L − 1, where the bound is
  nearly tight.
- 97 ≤ n < 112: finite check.

**Evidence.**
- [`A182336_mathlib.lean`](A182336_mathlib.lean) (Mathlib). `A182336_main` proves the statement
  for a(n) = `Nat.find`, with D(n, m) = popcount(n XOR m) and popcount defined by structural
  recursion. `A182336_data` checks a(0..22) against the OEIS data, and `A182336_96` checks the
  sharpness at 96. Axioms: propext, Classical.choice, Quot.sound. The finite tables use
  `decide +kernel`. Outside Lean: nothing.
- `certificate/check.py` checks the bound and the explicit witness for 112 ≤ n < 10^5 and lists
  the 42 failures with n ≤ 96.

**Review level.** lean-proof.

**Prior art (2026-11-05).** The OEIS entry still marks this as a conjecture. A web search found no
proof. google-deepmind/formal-conjectures has no file for A182336.
