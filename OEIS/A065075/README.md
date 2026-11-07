# OEIS A065075: every non-multiple of 3 appears — partial result (verified up to 1255)

**Source.** [A065075](https://oeis.org/A065075) (B. Zinser, 2001): a(1) = a(2) = 1, a(n) = sum of digits of
a(1) + ... + a(n-1). Comment: "Conjecture: every non-multiple of 3 does appear in the sequence."
(F. T. Adams-Watters, 2009); positions of first appearance in [A230289](https://oeis.org/A230289), b-file for
the first 86 non-multiples of 3 (up to 128). OEIS text, CC BY-SA 4.0, checked 2026-11-07.

**Reading.** The partial sums S_k = a(1) + ... + a(k) satisfy S_1 = 1 and S_{k+1} = S_k + s(S_k), where s is
the decimal digit sum; they form the orbit of x -> x + s(x) from 1 (A004207 without its leading 1), and the
values of A065075 are exactly the digit sums s(S_k). Multiples of 3 never occur: S_{k+1} ≡ 2 S_k (mod 9), so
S_k mod 9 runs through 1, 2, 4, 8, 7, 5.

**Result (partial).** Every m ≢ 0 (mod 3) with m <= 1255 occurs in A065075. More precisely, for every
D <= 140 checked (all D <= 60, and D = 100, 140), every m ≢ 0 (mod 3) with m <= 9D - 9 is the digit sum of an
orbit point below 10^D (certificate/pattern.out; the first missing value below 10^D lies in [9D - 8, 9D]).

**Method.** Block recursion. Write an orbit point as x = H·10^j + L with L < 10^j; while x stays in the block,
L evolves by L -> L + s(H) + s(L), which depends only on (j, s(H), L). The function rec(j, h, L) returns the
exit offset and the set of values s(L) visited inside the block; a j-block is ten (j-1)-blocks with h raised by
the top digit. Memoising rec over (j, h, entry offset) makes the orbit up to 10^140 (about 10^137 points)
computable exactly. Brute-force simulation agrees for D <= 7.

**Evidence.**
- [`certificate/orbit.py`](certificate/orbit.py) (block recursion + brute-force comparison),
  [`certificate/orbit100.out`](certificate/orbit100.out), [`certificate/orbit140.out`](certificate/orbit140.out),
  [`certificate/pattern.out`](certificate/pattern.out).
- Lean: none.
- Outside Lean: the whole computation.

**Review level.** `rechecked` (block recursion validated against direct simulation for D <= 7 and against
A230289's first appearances implicitly through the set of values).

**Prior art.** Checked 2026-11-07: OEIS A065075, A230289 (b-file to the 86th non-multiple, 128), A004207;
google-deepmind/formal-conjectures and otoi-lab/oeis-lean-proofs (no entry). The block recursion is the
standard carry-automaton acceleration for x -> x + s(x).
